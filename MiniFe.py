import os
import sys

foutname = 'rout'

try:
    fin = open(sys.argv[1], 'r')
except:
    print('file does not exist')
    sys.exit(0)
f = open('{}.asm'.format(foutname), 'w')

switch = 'match'
case = ':'
outkey = 'out'
outlnkey = 'outln'
outchkey = 'outchar'
argloc = 'rbp'
endaddr = 'qword [endaddr]'
terminate = '~~terminate'
sp = 'startplace'
const = 'const'
ahead = 'ahead'
newline = '\n'
usrdef = 'user_defined_'
comment = '#'

lnmap = {}
consts = {'true' : 1, 'false' : 0, 'nothing' : 0}

asmprintmac = """

            {}:
            mov rsi, [rsp + rsize]
            sub rsp, 8
            mov rdi, {}
            xor rax, rax
            call printf
            mov rdi, 0
	    add rsp, 8
	    ret
"""

asmprint = asmprintmac.format('print', 'format')
asmprintln = asmprintmac.format('println', 'formatln')
asmprintch = asmprintmac.format('printch', 'formatch')

asmcallmacro = """


%macro callmet 3
    push {0}
    mov {0}, rsp
    call {1}
    mov rsp, {0}
    pop {0}
    add rsp, rsize * {2}
%endmacro

""".format('%1', '%2', '%3') #.format(argloc, name, len(takes))

asmpref = """

;
;compile with
;nasm -f elf64 {}.asm && gcc {}.o && ./a.out
;

""".format(foutname, foutname) + asmcallmacro + """

%define rsize 8

extern printf, exit
section .data
    format db "%i", ' ', 0
    formatln db "%i", 10, 0
    formatch db "%c", 0
    argloc dq 0
    endaddr dq 0
section .text
    global main
    main:

"""

def isalnum(s):
    an = True
    for c in s:
        if not (c.isalnum() or c =='_'):
            an = False
            break
    return an

def tokenize(src):
    src = src.rstrip(); toks = []; s = ''
    for c in src:
        if not (isalnum(c) and isalnum(s)):
            if not s in [' ', '\t']: toks.append(s)
            s = ''
        s += c
    toks.append(s)
    toks.append(terminate)
    return linehandle(toks)

def linehandle(toks):
    #removes blank lines
    line = 1
    ntoks = ['\n']
    for i in range(len(toks)):
        t = toks[i]
        
        if t == '\n':
            line += 1
        elif t == ';':
            t = '\n'
            
        lnmap[i] = line
        if not (ntoks[-1] == '\n' and t == '\n') and not t == '':
            ntoks.append(t)

    global ind
    while ntoks[ind + 1] == '\n' : ind += 1

    return ntoks

tokens = []
ind = -1
look = ''

labc = -1

mets = {}
aheadmets = {}
arrmets = []
curmet = None

def out(s):
    f.write(s + '\n')
    #print(s)

def err(s):
    out('{}: call exit'.format(sp))
    print("Error at line {}: {}".format(lnmap[ind], str(s).replace('\n', 'newline')))
    f.flush()
    sys.exit(0)

def expect(s):
    if look == terminate : fnd = 'end of file'
    else : fnd = look
    err("expected '{}', found '{}'".format(s, fnd))

def getok():
    global ind
    global look
    oldlook = look
    ind += 1
    look = tokens[ind]
    if look == '\\':
        match('\\')
        match(newline)
    elif look == comment:
        while look != newline and look != terminate:
            getok()
        if oldlook == newline and look == newline:
            getok()

def match(s):
    if look != s : expect(s)
    getok()

def label():
    global labc
    labc += 1
    return 'label{}'.format(labc)

def isint(a):
    try:
        int(a)
        return True
    except:
        return False

#checks if constant int
def iscint(s):
    return isint(s) or isconst(s) and isint(constval(s))

#returns integer value of constant
def ctoint(c):
    if c in consts.keys():
        return int(constval(c))
    else:
        return int(c)

def dupident(s):
    return hasmet(s) or s in consts.keys()

def idtype(s):
    if hasmet(s) : return 'method'
    elif s in consts.keys() : return 'const'
    elif s in metargs(curmet) : return 'argument'
    else : return None

def useident(s):
    if dupident(s):
        err("duplicate identifier '{}' originally declared as a '{}'".format(s, idtype(s)))

rc = 'rcx'
rd = 'rdx'
rg = 'rax'

addop = '+'
subop = '-'
mulop = '*'
divop = '/'
modop = '%'

ops = [[addop, subop], [mulop, divop, modop]]
opmap = {}
for i in range(len(ops)):
    for o in ops[i]:
        opmap[o] = i

def popinto(r):
    if len(numstore) > 0 : out('mov {}, {}'.format(r, numstore.pop()))
    else : out('pop {}'.format(r))

def load():
    popinto(rc)
    popinto(rd)

def store():
    out('push {}'.format(rc))

def add() : out('add {}, {}'.format(rc, rd))
def sub():
    out('sub {}, {}'.format(rc, rd))
    out('imul {}, -1'.format(rc))
def mul() : out('imul {}, {}'.format(rc, rd))
def div():
    out('mov rax, {}'.format(rd))
    out('xor rdx, rdx')
    out('idiv {}'.format(rc))
    out('mov {}, rax'.format(rc)) 
def mod():
    out('mov rax, {}'.format(rd))
    out('xor rdx, rdx')
    out('idiv {}'.format(rc))
    out('mov {}, rdx'.format(rc))

opdefs = {addop : add, subop : sub, mulop : mul, divop : div, modop : mod}

def isop(s) : return s in opmap.keys()

numstore = []

def coperand():
    if not iscint(look) : expect('constant int')
    return ctoint(look)

def cparseop(opd1, oldop):
    getok()
    opd2 = coperand()
    getok()
    if isop(look) and opmap[look] > opmap[oldop]:
        opd2 = cparseop(opd2, look)
    return tryop(opd1, oldop, opd2)

def constexpr():
    num = coperand()
    getok()
    while isop(look):
        num = cparseop(num, look)
    if num == None : err('invalid constant expression')
    return num

def pusharg(name):
    ma = metargs(curmet)
    if not name in ma : err("argument '{}' does not exist".format(name))
    out('mov {}, {}'.format(rg, argloc))
    out('push qword [{} + rsize * {}]'.format(argloc, ma[::-1].index(name) + 1))
    
def operand():
    ma = metargs(curmet)
    opd = look
    if iscint(opd):
        opd = ctoint(opd)
        out('push {}'.format(opd))
    elif opd == '(':
        match('(')
        expression()
        if look != ')' : expect(')')
    elif isalnum(opd):
        if opd in ma:
            pusharg(opd)
        elif hasmet(opd):
            getok()
            callmet(opd)
        else : expect ('known identifier')
    elif opd == "'":
        match("'")
        if len(look) != 1 : expect('character')
        out('push {}'.format(ord(look)))
        getok()
        if look != "'" : expect("'")
    else : expect('valid operand')

def tryop(opd1, op, opd2):
    if iscint(opd1) and iscint(opd2):
        o1 = ctoint(opd1)
        o2 = ctoint(opd2)
        if op == addop:
            return o1 + o2
        elif op == subop:
            return o1 - o2
        elif op == mulop:
            return o1 * o2
        elif op == divop:
            return o1 / o2
        elif op == modop:
            return o1 % o2
    else:
        return None

def parseop(oldop):
    getok()
    opnd = look
    operand()
    if look != terminate:
        getok()
    if isop(look) and opmap[look] > opmap[oldop]:
        parseop(look, opnd)
    load()
    opdefs[oldop]()
    store()
        
def expression():
    if iscmd(look):
        callcmd(look)
    else:
        operand()
        getok()
        while isop(look):
            parseop(look)
        if len(numstore) > 0:
            out('push {}'.format(numstore.pop()))

def callmet(name):
    out('push rbx') #store a match comparision

    takes = metargs(name)

    match('(')

    rp = ')'
    for i in range(len(takes)):
        while look != rp:
            expression()
            if look != rp : match(',')
    if look != rp : expect(rp)

    out('callmet {}, {}, {}'.format(argloc, metlabel(name), len(takes)))

    out('pop rbx') #put back the match comparison
    
    out('push {}'.format(rg))

def metargs(name):
    if name in mets.keys():
        return mets[name]
    elif name in aheadmets.keys():
        return aheadmets[name]
    else:
        return []

def matchmet(name, args):
    if name in aheadmets.keys():
        if args == aheadmets[name]:
            aheadmets.pop(name)
        else:
            err("method '{}' does not match its header".format(name))
    useident(name)
    mets[name] = args

def hasmet(s):
    return s in mets.keys() or s in aheadmets.keys()

def metlabel(name):
    return '{}{}'.format(usrdef, name)

def dometargs(name):
    
    args = []
    if look == '(':
        getok()
        while look != ')':
            if not isalnum(look) : expect('alphanumeric')
            args.append(look)
            useident(look)
            getok()
            if look != ')' : match(',')
        match(')')
    else : expect('(')

    return args

def newmet():

    def endmet():
        out('pop {}'.format(rg))
        out('mov rsp, {}'.format(argloc))
        out('sub rsp, rsize * 1')
        out('ret')

    def startline():
        match('\n')
        if look == '<':
            match('<')
            match('>')
            endmet()
            newmet()
        elif look == switch:
            match(switch)
            doswitch()
        else:
            expression()
    
    name = look

    global curmet
    curmet = name
    
    if not isalnum(name) : expect('alphanumeric')
    getok()
    args = dometargs(name)

    matchmet(name, args)
    
    out(metlabel(name) + ':')
    startline()
    while look != '<' and look != terminate:
        startline()

def doswitch():
    expression()
    out('pop rbx')
    match('\n')
    leave = label()
    other = 'default'
    while look != other:
        nextl = label()
        expression()
        out('add rsp, rsize')
        out('cmp rbx, [rsp - rsize]')
        out('jne {}'.format(nextl))
        match(':')
        expression()
        out('jmp {}'.format(leave))
        match('\n')
        out(nextl + ':')
    match(other)
    match(':')
    expression()
    out(leave + ':')

def doprint():
    getok()
    expression()
    out('call print')

def doprintln():
    getok()
    expression()
    out('call println')

def doprintch():
    getok()
    expression()
    out('call printch')

cmds = {outkey : doprint, outlnkey : doprintln, outchkey : doprintch}

def iscmd(s):
    return s in cmds.keys()

def callcmd(s):
    cmds[s]()

def constval(c):
    return consts[c]

def isconst(c):
    return c in consts.keys()

cnstkeys = [const, ahead]

def doconst():
    match(const)
    name = look
    useident(name)
    getok()
    match('=')
    consts[name] = str(constexpr())
    match(newline)

def doahead():
    match(ahead)
    name = look
    useident(name)
    getok()
    aheadmets[name] = dometargs(name)
    match(newline)

def doheader():
    while look in cnstkeys:
        if look == 'const':
            doconst()
        elif look == ahead:
            doahead()

def start():

    out(asmpref)

    out('jmp {}'.format(sp))

    out(asmprint)
    out(asmprintln)
    out(asmprintch)
    
    getok()

    doheader()
    
    match('<')
    match('>')
    newmet()

    if len(metargs(curmet)) != 0:
        err("starting method '{}' cannot take arguments".format(curmet))
    
    out('pop {}'.format(rg))

    out('mov rsp, {}'.format(argloc))
    out('sub rsp, rsize * 1')
    
    out('ret')

    out("""
        {}:
        mov {}, rsp
        call {}
        call exit
        """.format(sp, argloc, metlabel(curmet)))

src = fin.read()

tokens = tokenize(src)
#print(tokens)
start()
f.flush()

outfilename = 'a.out'
if len(sys.argv) > 2 : outfilename = sys.argv[2]
os.system("nasm -f elf64 rout.asm && gcc rout.o -o {}".format(outfilename))
