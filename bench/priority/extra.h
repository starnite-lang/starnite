/* Included after the reference harness helpers. */
typedef struct { int64_t *p; size_t len, cap; } Vector;
static void append(Vector *v, int64_t item) {
    if (v->len == v->cap) {
        require(v->cap <= SIZE_MAX / sizeof *v->p / 2);
        size_t cap = v->cap ? v->cap * 2 : 4;
        int64_t *p = realloc(v->p, cap * sizeof *p);
        require(p != NULL);
        v->p = p;
        v->cap = cap;
    }
    v->p[v->len++] = item;
}
typedef struct { char *p; size_t n; } Text;
static Text new_text(const char *p, size_t n) {
    require(n < SIZE_MAX);
    Text t = {alloc(n+1,1),n};
    if (n) memcpy(t.p,p,n);
    t.p[n] = 0;
    return t;
}
static Text join_text(const Text *parts, size_t n, const char *sep, size_t sep_n) {
    size_t len=0;
    for (size_t i=0;i<n;i++) {
        require(parts[i].n <= SIZE_MAX-len && (!i || sep_n <= SIZE_MAX-len-parts[i].n));
        len += parts[i].n + (i ? sep_n : 0);
    }
    require(len < SIZE_MAX);
    Text t = {alloc(len+1,1),len};
    size_t at=0;
    for (size_t i=0;i<n;i++) {
        if (i && sep_n) { memcpy(t.p+at,sep,sep_n); at+=sep_n; }
        memcpy(t.p+at,parts[i].p,parts[i].n); at+=parts[i].n;
    }
    t.p[len]=0;
    return t;
}
static int space(unsigned char c) { return c == 32 || (c >= 9 && c <= 13); }
static int boundary(Text t,size_t i) { return i==t.n || (((unsigned char)t.p[i]&0xc0)!=0x80); }
static uint32_t scalar(Text t, size_t *pos) {
    size_t i=*pos;
    require(i<t.n);
    unsigned c=(unsigned char)t.p[i++];
    unsigned rem=0;
    if (c>=0x80) {
        if (c>=0xc2 && c<=0xdf) { rem=1; c&=31; }
        else if (c>=0xe0 && c<=0xef) { rem=2; c&=15; }
        else if (c>=0xf0 && c<=0xf4) { rem=3; c&=7; }
        else require(0);
    }
    require(rem <= t.n-i);
    unsigned width=rem;
    while(rem--) {
        unsigned b=(unsigned char)t.p[i++];
        require((b&0xc0)==0x80);
        c=(c<<6)|(b&63);
    }
    static const unsigned minimum[]={0,0x80,0x800,0x10000};
    require(c>=minimum[width] && c<=0x10ffff && !(c>=0xd800 && c<=0xdfff));
    *pos=i;
    return c;
}
static int extra(const char *name, int64_t seed, uint64_t *elapsed, int64_t *result) {
    uint64_t start=0,end=0;
    int64_t sum=0;
    if (!strcmp(name,"int_arithmetic")) {
        sum=seed; start=now();
        for (int i=0;i<4000000;i++) sum=add(mul(sum,1664525),1013904223)%2147483647;
        end=now();
    } else if (!strcmp(name,"float_arithmetic")) {
        double x=(double)seed; start=now();
        for (int i=0;i<4000000;i++) { x=x*0.9999999+0.000013; x/=1.0000001; }
        end=now();
        x*=1000000.;
        require(x>=-0x1p63 && x<0x1p63);
        sum=(int64_t)x;
    } else if (!strcmp(name,"array_fill")) {
        size_t n=2000000; start=now();
        int64_t *a=alloc(n,sizeof *a);
        for(size_t i=0;i<n;i++)a[i]=seed;
        observe(a); end=now(); sum=add((int64_t)n,a[1000000]); free(a);
    } else if (!strcmp(name,"array_push") || !strcmp(name,"array_clear_refill")) {
        Vector a={0}; int refill=!strcmp(name,"array_clear_refill");
        start=now();
        if (refill) {
            for(int i=0;i<2000;i++) {
                a.len=0;
                for(int j=0;j<128;j++)append(&a,add(add(seed,i),j));
                sum=add(sum,a.p[127]);
            }
        } else {
            for(int i=0;i<500000;i++)append(&a,add(i,seed));
            sum=add((int64_t)a.len,a.p[250000]);
        }
        end=now(); free(a.p);
    } else if (!strcmp(name,"array_front_insert_remove")) {
        const size_t n=16000;
        int64_t *a=alloc(n+1,sizeof *a), *initial=data(n);
        memcpy(a,initial,n*sizeof *a); free(initial);
        start=now();
        for(int i=0;i<5000;i++) {
            memmove(a+1,a,n*sizeof *a); a[0]=add(i,seed);
            observe(a); sum=add(sum,a[0]); memmove(a,a+1,n*sizeof *a);
        }
        end=now(); sum=add(sum,a[8192]); free(a);
    } else if (!strcmp(name,"array_reverse")) {
        const size_t n=500000; int64_t *a=data(n);
#ifdef SHARED
        StnArray *values=copy_array(a,n,&integer_ops);
        free(a);
        start=now(); stn_array_reverse_i64(&values); a=(int64_t*)values->data;
#else
        start=now();
        for(size_t i=0;i<n/2;i++) {int64_t x=a[i];a[i]=a[n-i-1];a[n-i-1]=x;}
#endif
        observe(a); end=now(); sum=add(a[0],mul(3,a[n-1]));
#ifdef SHARED
        stn_drop(values, stn_array_release);
#else
        free(a);
#endif
    } else if (!strcmp(name,"array_owned_slice") || !strcmp(name,"array_extend") || !strcmp(name,"array_snapshot_write")) {
        const size_t n=500000;
        int64_t *a=data(n), *other=NULL, *b;
        if (!strcmp(name,"array_extend")) {
            other=data(n);
            start=now(); b=realloc(a,2*n*sizeof *b); require(b!=NULL);
            memcpy(b+n,other,n*sizeof *b); observe(b); end=now();
            sum=add(2*n,add(b[n-1],b[n])); a=b;
        } else if (!strcmp(name,"array_owned_slice")) {
            require(100000<=450000 && 450000<=n);
            start=now(); b=alloc(350000,sizeof *b);
            memcpy(b,a+100000,350000*sizeof *b); observe(b); end=now();
            sum=add(350000,add(b[0],b[349999])); other=b;
        } else {
            /* The original and the snapshot must both be available after the write. */
            start=now(); b=alloc(n,sizeof *b); memcpy(b,a,n*sizeof *b);
            b[250000]=seed; observe(b); end=now();
            sum=add((int64_t)n,add(a[250000],mul(3,b[250000]))); other=b;
        }
        free(a); free(other);
    } else if (!strcmp(name,"option_result")) {
        typedef struct { int64_t value; unsigned char tag; } Tagged;
        Tagged *o=alloc(500000,sizeof *o),*r=alloc(500000,sizeof *r);
        for(int64_t i=0;i<500000;i++) {
            int64_t value=add(i,seed);
            o[i]=(Tagged){value,(unsigned char)(i%3!=0)};
            r[i]=(Tagged){value,(unsigned char)(i%3!=0)};
        }
        start=now();
        for(size_t i=0;i<500000;i++)sum=add(sum,add(o[i].tag?o[i].value:1,r[i].tag?r[i].value:2));
        end=now(); free(o); free(r);
    } else if (!strcmp(name,"tuple_array_scan") || !strcmp(name,"struct_array_scan")) {
        typedef struct { int64_t x,y; } Pair;
        Pair *a=alloc(500000,sizeof *a);
        for(int64_t i=0;i<500000;i++)a[i]=(Pair){add(seed,i),mul(3,i)};
        start=now();
        for(size_t i=0;i<500000;i++)sum=add(sum,add(a[i].x,a[i].y));
        end=now(); free(a);
    } else if (!strncmp(name,"str_",4)) {
        int concat=!strcmp(name,"str_concat"), slice=!strcmp(name,"str_owned_slice");
        int split=!strcmp(name,"str_split_owned"), join=!strcmp(name,"str_join");
        int chars=!strcmp(name,"str_chars_owned"), trim=!strcmp(name,"str_trim_owned");
        int repeat=!strcmp(name,"str_repeat");
        if(!(concat||slice||split||join||chars||trim||repeat))return 0;
        char buf[128][64]; Text values[128];
#ifdef SHARED
        StnStr strings[128];
        const StnElemOps string_ops={sizeof(StnStr),NULL,NULL};
        const StnElemOps char_ops={sizeof(uint32_t),NULL,NULL};
        StnStr comma=stn_str_new(",",1), pipe=stn_str_new("|",1), last=stn_str_new("end",3);
#endif
        for(size_t i=0;i<128;i++) {
            int d=(int)((i*7+seed)%1000+1000);
            int n=snprintf(buf[i],sizeof buf[i],"  name%d,alpha,tag%d,é漢🙂  ",d,d*3);
            require(n>=12 && n<(int)sizeof buf[i]); values[i]=(Text){buf[i],(size_t)n};
#ifdef SHARED
            strings[i]=stn_str_new(buf[i],n);
#endif
        }
        int count=split?100000:join||chars?150000:200000;
        start=now();
        for(int i=0;i<count;i++) {
            Text s=values[i%128], next=values[(i+1)%128];
#ifdef SHARED
            StnStr text=strings[i%128], next_text=strings[(i+1)%128], out=NULL;
#endif
            if(split) {
#ifdef SHARED
                StnArray *pieces=stn_str_split(text,comma,&string_ops,"benchmark",0,0);
                StnStr *fields=(StnStr*)pieces->data;
                require(pieces->len>=3); observe(pieces);
                sum=add(sum,add(pieces->len,add(fields[1]->len,fields[2]->len)));
                for(int64_t j=0;j<pieces->len;j++)STN_STR_DROP(fields[j]);
                stn_drop(pieces,stn_array_release);
#else
                Text parts[8]; size_t n=0, lo=0;
                for(size_t p=0;p<=s.n;p++) if(p==s.n || s.p[p]==',') {
                    require(n<8); parts[n++]=new_text(s.p+lo,p-lo); lo=p+1;
                }
                require(n>=3); observe(parts);
                sum=add(sum,add(n,add(parts[1].n,parts[2].n)));
                for(size_t j=0;j<n;j++)free(parts[j].p);
#endif
            } else if(chars) {
#ifdef SHARED
                StnArray *letters=stn_str_chars(text,&char_ops);
                require(letters->len>=3); observe(letters);
                sum=add(sum,add(letters->len,((uint32_t*)letters->data)[2]));
                stn_drop(letters,stn_array_release);
#else
                uint32_t *letters=alloc(s.n,sizeof *letters);
                size_t n=0,pos=0;
                while(pos<s.n)letters[n++]=scalar(s,&pos);
                require(n>=3); observe(letters); sum=add(sum,add(n,letters[2])); free(letters);
#endif
            } else {
                size_t index=slice?2:0;
#ifdef SHARED
                if(concat) out=stn_str_concat(text,next_text);
                else if(slice) out=stn_str_slice(text,0,12,"benchmark",0,0);
                else if(join) {StnStr p[]={text,next_text,last};out=stn_str_join_parts(p,3,pipe);}
                else if(trim) out=stn_str_trim(text);
                else out=stn_str_repeat(text,i%5+1,"benchmark",0,0);
                observe(out); require(index<(size_t)out->len);
                sum=add(sum,add(out->len,(unsigned char)out->data[index])); STN_STR_DROP(out);
#else
                Text out;
                if(concat) {Text p[]={s,next};out=join_text(p,2,"",0);}
                else if(slice) {require(s.n>=12 && boundary(s,12));out=new_text(s.p,12);}
                else if(join) {Text p[]={s,next,{"end",3}};out=join_text(p,3,"|",1);}
                else if(trim) {
                    size_t lo=0,hi=s.n;
                    while(lo<hi && space(s.p[lo]))lo++;
                    while(hi>lo && space(s.p[hi-1]))hi--;
                    out=new_text(s.p+lo,hi-lo);
                } else {
                    Text p[]={s,s,s,s,s};out=join_text(p,i%5+1,"",0);
                }
                observe(out.p);require(index<out.n);
                sum=add(sum,add(out.n,(unsigned char)out.p[index]));free(out.p);
#endif
            }
        }
        end=now();
#ifdef SHARED
        for(size_t i=0;i<128;i++)STN_STR_DROP(strings[i]);
        STN_STR_DROP(comma);STN_STR_DROP(pipe);STN_STR_DROP(last);
#endif
    } else return 0;
    *result=sum; *elapsed=end-start;
    return 1;
}
