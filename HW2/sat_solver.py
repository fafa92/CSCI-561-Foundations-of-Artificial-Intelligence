from os.path import isfile
import sys,re
import itertools
import sys

class formula:
    def __init__(self,fname):
        self.fname=fname        
        if not isfile(fname):
            print('file '+fname+' does not exist!\n')
            print('Press any kay to continue ...')
            sys.stdin.read(1)
            sys.exit(0)
        else:
            f=open(fname)
        with f:
            content = f.readlines()
            content = [x.strip() for x in content] 
            MN=content[0].split()
            self.relations=content[1:]
            self.num_members=int(MN[0])
            self.num_tables=int(MN[1])
            self.formul=[]   

    def print_formula(self,f):
        expr=self.formula_to_math_expr()
        f.write(expr+'\n\n')

    def add_clause(self,lst):
       self.formul.append(lst) 

    def create_formula(self):
        lst=range(self.num_tables)
        lst = [int(x)+1 for x in lst]
        it=list(itertools.combinations(lst, 2))
        
        for member in range(self.num_members):
            cls=[]
            for table in range(self.num_tables):
                cls.append([0,member+1,table+1])
            self.add_clause(cls)
            for ls in it:
                cls=[]
                for n in ls:
                    cls.append([1,member+1,n])
                self.add_clause(cls)

        for rel in self.relations:
            lst2=rel.split()        
            if lst2[2]=='F':
                for n in lst:
                    cls=[]
                    cls.append([1,int(lst2[0]),n])
                    cls.append([0,int(lst2[1]),n])
                    self.add_clause(cls)
                    cls=[]
                    cls.append([0,int(lst2[0]),n])
                    cls.append([1,int(lst2[1]),n])
                    self.add_clause(cls)

            elif lst2[2]=='E':
                for n in lst:
                    cls=[]
                    cls.append([1,int(lst2[0]),n])
                    cls.append([1,int(lst2[1]),n])
                    self.add_clause(cls)


    def dpll_satisfiable(self):
        " Check satisfiability of a formula "
        formul=self.formul
        symb=self.get_symbols(formul)        
        return self.dpll(formul,symb,[])

    def dpll(self,the_formula,the_symbols,the_model):
        "See if the clauses are true in a partial model."
        unknown_clauses = []   
        for c in the_formula: 
            val = self.pl_true(c, the_model)
            if val is False: 
                return False 
            if val is not True: 
                unknown_clauses.append(c) 
        if not unknown_clauses: 
            return the_model 
        P, value = self.find_pure_symbol(the_symbols, unknown_clauses)
        if P: 
            symb=[s for s in the_symbols if s!=P]
            return self.dpll(the_formula, symb, self.extend(the_model, P, value)) 
        outlist= self.find_unit_clause(the_formula, the_model) 
        P,value=outlist[0],outlist[1]
        if P: 
            symb=[s for s in the_symbols if s not in P]
            return self.dpll(the_formula, symb, self.extend(the_model, P, value)) 
        if not the_symbols: 
            raise TypeError("Argument should be of the type Expr.") 
        P, symbols = the_symbols[0], the_symbols[1:] 
        return (self.dpll(the_formula, symbols, self.extend(the_model, P, True)) or 
             self.dpll(the_formula, symbols, self.extend(the_model, P, False))) 
    
    def find_unit_clause(self,the_formula, the_model):
        """Find a forced assignment if possible from a clause with only 1 
        variable not bound in the model. """
        literals=[]
        values=[]
        for clause in the_formula: 
            P, value = self.unit_clause_assign(clause, the_model) 
            if P: 
                literals.append(P)
                values.append(value) 
        return [None,None] if literals==[] else [literals,values]

    def unit_clause_assign(self,clause, the_model):
        """Return a single variable/value pair that makes clause true in 
        the model, if possible. """
        P, value = None, None 
        if the_model==[]:
            sym=self.get_symbols([clause])
            if len(sym)>1:
                return None,None
            else:
                return self.inspect_literal(clause[0])
        for literal in clause: 
            sym, positive = self.inspect_literal(literal)            
            if sym in the_model[0]:
                dex=the_model[0].index(sym)
                values=the_model[1]
                val=values[dex]
                if val == positive: 
                    return None, None  # clause already True 
            elif P:
                 return None, None      # more than 1 unbound variable 
            else:
                 P, value = sym, positive 
        return P, value 

    def inspect_literal(self,literal): 
        """The symbol in this literal, and the value it should take to 
        make the literal true."""
        if literal[0]==0:
            return literal[1:],True
        else:
            return literal[1:],False

    def extend(self,model,P,val):
        if model==[]:
            if isinstance(P, list):
                model=[P,val]
            else:
                model=[[P],[val]]
        else:
            lnum=sum(1 for x in model[0] if isinstance(x, list))
            if lnum==0:
                model[0]=[model[0]]
            if not isinstance(model[1], list):
                model[1]=[model[1]]
            lnum=sum(1 for x in P if isinstance(x, list))
            if lnum==0:
                model[0].append(P)
                model[1].append(val)
            else:
                model[0].extend(P)
                model[1].extend(val)
        return model

    def pl_true(self,clause, model=[]):
        if clause in (True, False): 
            return clause 
        lnum=sum(1 for x in clause if isinstance(x, list))
        if lnum != 0:
            if len(clause)==1:
                return self.pl_true(clause[0],model)
            p=[]
            for lit in clause:
                p.append(self.pl_true(lit,model))
            if True in p:
                return True           
            if False in p:
                dexes=p.index(False)
                clause.pop(dexes)
                return self.pl_true(clause,model)
            else:
                return None
        else:
            is_cont=clause[0]
            lit=clause[1:]
            if model==[]:
                return None
            else:               
                literals=model[0]
                values=model[1]
                lnum=sum(1 for x in literals if isinstance(x, list))
                if lnum==0:
                    literals=[literals]
                    values=[values]
                if lit not in literals:
                    return None
                dex=literals.index(lit)
                if is_cont==1:
                    return not values[dex]
                else:
                    return values[dex]    
    
    def find_pure_symbol(self,symbols, clauses): 
        """Find a symbol and its value if it appears only as a positive literal 
        (or only as a negative) in clauses. """
        for s in symbols: 
            found_pos, found_neg = False, False 
            for c in clauses: 
                literals,contrad=self.get_literals(c)
                if s in literals:
                    dex=literals.index(s)
                    cont=contrad[dex]
                    if not found_pos and cont: 
                        found_pos = True 
                    if not found_neg and not cont: 
                        found_neg = True 
            if found_pos != found_neg: 
                return s, found_pos 
        return None, None 

    def get_literals(self,clause):
        literals=[]
        contrad=[]
        for lit in clause:
            cont=lit[0]
            lit=lit[1:]
            if lit not in literals:
                literals.append(lit)
                if cont==0: 
                    contrad.append(True)
                else:
                    contrad.append(False)
        return literals,contrad

    def get_symbols(self,formul):
        """ get symbols from given formula """
        symbols=[]
        for clause in formul:
            for literal in clause:
                lit=literal[1:]
                if lit not in symbols: 
                    symbols.append(lit) 
        return symbols

    def formula_to_math_expr(self):
        expr=''
        for clause in self.formul:       
            if len(clause)==1:
                cls=''
                sp=clause[0]
                if sp[0]==0:
                    cls=cls+'x'+str(sp[1])+str(sp[2])
                else:
                    cls=cls+'~x'+str(sp[1])+str(sp[2])
            else:
                cls='('
                for lit in clause:
                    sp=lit
                    if sp[0]==0:
                        cls=cls+'x'+str(sp[1])+str(sp[2])
                    else:
                        cls=cls+'~x'+str(sp[1])+str(sp[2])
                    cls=cls+' or '
                cls=cls[:-4]
                cls=cls+')'
            if expr != '' :
                expr=expr+' and '+cls
            else: 
                expr=expr+cls
   
        return expr

def main():
    file='input.txt'
    f=formula(file)
    f.create_formula()
    a=f.dpll_satisfiable()
    name='output.txt'
    fout=open(name, 'w')
    if a:
        fout.write('yes\n')
        sit=a[0]
        vals=a[1]
        tt=[i for i,x in enumerate(vals) if x == True]
        answers=[]
        for t in tt:
            answers.append(sit[t])
        if answers:
            answers.sort(key=lambda l:l[0])
            for s in answers:
                fout.write(str(s[0])+' '+str(s[1])+'\n') 
    else:
        fout.write('no\n')
    fout.close()
    sys.exit(0) 

main()

