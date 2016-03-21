#Look for #IMPLEMENT tags in this file. These tags indicate what has
#to be implemented to complete the warehouse domain.  

'''This file will contain different constraint propagators to be used within 
   bt_search.

   propagator == a function with the following template
      propagator(csp, newly_instantiated_variable=None)
           ==> returns (True/False, [(Variable, Value), (Variable, Value) ...]

      csp is a CSP object---the propagator can use this to get access
      to the variables and constraints of the problem. The assigned variables
      can be accessed via methods, the values assigned can also be accessed.

      newly_instaniated_variable is an optional argument.
      if newly_instantiated_variable is not None:
          then newly_instantiated_variable is the most
           recently assigned variable of the search.
      else:
          progator is called before any assignments are made
          in which case it must decide what processing to do
           prior to any variables being assigned. SEE BELOW

       The propagator returns True/False and a list of (Variable, Value) pairs.
       Return is False if a deadend has been detected by the propagator.
       in this case bt_search will backtrack
       return is true if we can continue.

      The list of variable values pairs are all of the values
      the propagator pruned (using the variable's prune_value method). 
      bt_search NEEDS to know this in order to correctly restore these 
      values when it undoes a variable assignment.

      NOTE propagator SHOULD NOT prune a value that has already been 
      pruned! Nor should it prune a value twice

      PROPAGATOR called with newly_instantiated_variable = None
      PROCESSING REQUIRED:
        for plain backtracking (where we only check fully instantiated constraints)
        we do nothing...return true, []

        for forward checking (where we only check constraints with one remaining variable)
        we look for unary constraints of the csp (constraints whose scope contains
        only one variable) and we forward_check these constraints.

        for gac we establish initial GAC by initializing the GAC queue
        with all constaints of the csp


      PROPAGATOR called with newly_instantiated_variable = a variable V
      PROCESSING REQUIRED:
         for plain backtracking we check all constraints with V (see csp method
         get_cons_with_var) that are fully assigned.

         for forward checking we forward check all constraints with V
         that have one unassigned variable left

         for gac we initialize the GAC queue with all constraints containing V.
         
   '''

def prop_BT(csp, newVar=None):
    '''Do plain backtracking propagation. That is, do no 
    propagation at all. Just check fully instantiated constraints'''
    
    if not newVar:
        return True, []
    for c in csp.get_cons_with_var(newVar):
        if c.get_n_unasgn() == 0:
            vals = []
            vars = c.get_scope()
            for var in vars:
                vals.append(var.get_assigned_value())
            if not c.check(vals):
                return False, []
    return True, []

def prop_FC(csp, newVar=None):
    '''Do forward checking. That is check constraints with 
       only one uninstantiated variable. Remember to keep 
       track of all pruned variable,value pairs and return 

      PROPAGATOR called with newly_instantiated_variable = None
      PROCESSING REQUIRED:
        for forward checking (where we only check constraints with one remaining variable)
        we look for unary constraints of the csp (constraints whose scope contains
        only one variable) and we forward_check these constraints.'''
  
    unary = []    
    pruned_L = []

    if not newVar:
      '''stores all unarry conditions'''
      for c in csp.cons:
        if c.get_n_unasgn() == 1:
          unary.append(c)

      '''PROPAGATOR called with newly_instantiated_variable = a variable V
      PROCESSING REQUIRED:
          for forward checking we forward check all constraints with V
          that have one unassigned variable left'''
    else:
      with_v = csp.get_cons_with_var(newVar)
      '''stores all unarry conditions with newVar'''
      for c in with_v:
        if c.get_n_unasgn() == 1:
          unary.append(c)
    
    '''for each unary constraint'''
    for c in unary: 
      '''get the unassigned variable'''
      un_a = c.get_unasgn_vars()[0]    

      '''cur_dom of the unassigned variable'''
      cur_d = un_a.cur_domain()
      for d in cur_d:
        to_check = []
        '''for every variable in constraint'''
        for v in c.get_scope():         
          if v.is_assigned():
            to_check.append(v.get_assigned_value())
          else:
            to_check.append(d)
        if not c.check(to_check):
          un_a.prune_value(d)
          pruned_L.append((un_a, d))

      '''DWO if no value in cur domain'''
      if un_a.cur_domain_size() == 0:
        return False, pruned_L

    return True, pruned_L


def prop_GAC(csp, newVar=None):
    '''Do GAC propagation. If newVar is None 

        for gac we establish initial GAC by initializing the GAC queue
        with all constaints of the csp'''
    if not newVar:
      '''all constraints'''
      queue = csp.get_all_cons()
      
      '''for gac we initialize the GAC queue with all constraints containing V.'''
    else:
      queue = csp.get_cons_with_var(newVar)
    
    pruned_L = []    
    while len(queue) != 0:
      '''variables in constraint'''
      constraint = queue.pop(0)
      var = constraint.get_scope()
      for v in var:
        '''if the domain is empty , DWO '''
        if v.cur_domain_size() == 0:
          return False, pruned_L
        '''domain of variable'''
        domain = v.cur_domain()
        for d in domain:
          '''test support for each value in domain'''
          if not constraint.has_support(v, d):
            v.prune_value(d)
            pruned_L.append((v,d))
            for rq in csp.get_cons_with_var(v):
              if not rq in queue and rq != constraint:
                queue.append(rq)
    return True, pruned_L
