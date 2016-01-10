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
    
[O-S\sG-L]+ 
[ANTIGE]+   
(S\s|\sS|'A)+   
[PI\sRD]+   
(TD|L|LO|O|OH)+ 
[HITE'\s]+  
[MENDS]+
[HEL\s]+P.+ 






.[SEPOLI\s]+
[MI/SON]+[^OLDE]{4} 






.{3,4}(\sH|\s|IM)+
[IN'THE\.\s]+   






[IT'\s]{4}[H.TE]+
.[A-G]+(R|D)+[END]+ 






.{4}(NI|TE|N|DE)+
(\s\s|OR|HO|ME)+    
[A-G]N+(GI|IG|PI)   
[RAM\sES']+ 
[^AINED]+   
[HORTED]+   
[F-K]{2}[F-M]..?    
(S|I|MS)[MYEND]*
""",
4,7, True)

