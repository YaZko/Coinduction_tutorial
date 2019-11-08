def ifpstr(n,s1,s2=""):
    if n > 0:
        return s1
    else:
        return s2

def ifzstr(n,s1,s2=""):
    if n == 0:
        return s1
    else:
        return s2

def itrstr(prefix,n,postfix=''):
    result = ""
    for i in range(n):
        result = result+prefix+str(i)+postfix
    return result

def lev(m):
    if m <= 1:
        return ""
    else:
        return "_"+str(m)

def idx(m,i):
    if m <= 1:
        return ""
    else:
        return "_"+str(i)

def itridx(prefix,m,postfix=''):
    result = ""
    for i in range(m):
        result = result+prefix+idx(m,i)+postfix
    return result

