#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0-or-later
# The input of the CSV to JSON benchmark: `gen.py ROWS` writes that many rows to standard output,
# the same every time. One row in five has a quoted name with a comma in it.
import sys
rows = int(sys.argv[1]) if len(sys.argv) > 1 else 200000
cities = ["London", "Arlington", "Helsinki", "Kyoto", "Lagos", "Lima"]
tags = ["math", "engines", "navy", "compilers", "kernels", "music", "maps"]
out = ["id,name,active,score,address.city,address.geo.lat,address.geo.lon,tags[],limits.daily[]"]
x = 12345
for i in range(rows):
    x = (x * 1103515245 + 12345) & 0x7FFFFFFF
    name = f'"Hopper {i}, Grace"' if i % 5 == 0 else f"user{i}"
    score = "" if i % 7 == 0 else f"{round((x % 1000) / 10 + 0.25, 2)}"
    t = ";".join(tags[(x >> k) % len(tags)] for k in range(0, (x % 4) * 3, 3))
    d = ";".join(str((x >> k) % 500) for k in range(0, (x % 3) * 5, 5))
    out.append(f"{i},{name},{'true' if x % 2 else 'false'},{score},{cities[x % len(cities)]},{round((x % 18000) / 100 - 90 + 0.125, 3)},{round(((x >> 8) % 36000) / 100 - 180 + 0.375, 3)},{t},{d}")
sys.stdout.write("\n".join(out) + "\n")
