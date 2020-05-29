# Fix the extracted file 

import sys

f = open('extracted_tc.ml')
strf = open('extra/String_as_OT.ml')
extraf = open('extra/typedecls.ml')

skip = False
prev = ""

for line in f:
    if line.find('module Nenv = Make(Nat_as_OT)') != -1:        
        # Emit the String_as_OT module
        sys.stdout.write(strf.read())
        strf.close()
        sys.stdout.write('\n')

        # Replace the module since extraction changed
        sys.stdout.write('module Nenv = Make(String_as_OT)\n')

    elif line.find('module Ienv = Make(Int64_OT)') != -1:
        # Replace the module since extraction changed
        sys.stdout.write('module Ienv = Make(String_as_OT)\n')

    #elif line.find('nat_of_Z (Word.unsigned sz i0)') != -1:
        # Replace to int
    #    sys.stdout.write(line.replace('nat_of_Z (Word.unsigned sz i0)', 'i0', 1))

    #elif line.find('nat_of_Z (Word.unsigned sz i)') != -1:
        # Replace to int
    #    sys.stdout.write(line.replace('nat_of_Z (Word.unsigned sz i)', 'i', 1))

    #elif prev.find('(Word.unsigned') != -1 and line.find('sz2 i0')

    elif line.find('| Const_null -> Some ((Ftyp_ptr (typ_int32, 0))::[])') != -1:
        sys.stdout.write('| Const_null -> Some ((Ftyp_ptr (typ_int32, ""))::[])')

    elif line.find('type lab = string') != -1:
        sys.stdout.write('open SCast\n\n')
        sys.stdout.write(extraf.read())
        sys.stdout.write('\n')
        extraf.close()
        skip = True

    elif line.find('type functions = function0 list') != -1:
        skip = False

    else:
        if skip:
            prev = line
            continue
        else:
            sys.stdout.write(line)
    prev = line

f.close()
