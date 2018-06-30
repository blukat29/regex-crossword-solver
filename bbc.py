from crossword import solve_crossword

rows = [
    r'[^XZVCHFJLQM]+',
    r'[^PZVJG]{4}(.)[EFUG]{6}\1[^\sPZVJI]{2}',
    r'[^\sPQFB]{7}[^MGVAJNZ\s]+[^MVZJ]',
    r'N[OYSRU]{5}[NICE]{6}\s\-',
    r'.A[A\sDL]{4}O[AECLV\s]+',
]

cols = [
    r'.*\sA?(SA|PE|N\s){2}',
    r'([XYZ])(P|GO|EL)\1.',
    r'(LS|CA|OS)[L\sP][DO]{2}',
    r'(U)(T)\2\1[AOB?]',
    r'(.)\1\1\1\s',
    r'(FF|BE|QU|OS){2}L',
    r'ES?F?(OBZ|UCO|PTE)',
    r'S[MVU]B(TZ|BP|IV)',
    r'T[GLMV]{2}(E)\1',
    r'(JK|AE|EN|MG){2}L',
    r'N(XN|ZB|CA|FS){2}',
    r'[XHDJ]R[MZVIJ]EC',
    r'X?W(\sE|OS|PE){2}',
    r'[VIMZJ]{3}\-\s',
]

answer = solve_crossword(rows, cols)
for line in answer:
    print '  '.join(line)
