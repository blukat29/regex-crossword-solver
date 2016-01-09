from crossword import solve_crossword

def autosolve(raw, num_rows, num_cols, double=False):
    a = raw.split('\n')
    a = filter(None, map(str.strip, a))
    cols = a[:num_cols]
    a = a[num_cols:]

    rows = []
    rows2 = []
    for i in range(num_rows):
        rows.append(a[0])
        a = a[1:]
        if double:
            rows2.append(a[0])
            a = a[1:]

    if double:
        cols2 = a
    else:
        cols2 = []

    print rows, cols, rows2, cols2
    ans =  solve_crossword(rows, cols, rows2, cols2)
    print '\n'.join(map(lambda x: ' '.join(x), ans))

autosolve("""
[HELP\s]+   
[^\sPONG]+N 
[SONG]+\s
[^SEAP]+    


[\sCOPE]+
[\sPIN]E[NET]   


[^HI\s]+
[^ONE\s]+   


[\sHAG]+
[END\s]+    


[^SODA]+
[^SLIC]+\w  
[OCEAN\s]+  
[^SPIES]+
""",
4, 3, True)

