#Look for #IMPLEMENT tags in this file. These tags indicate what has
#to be implemented to complete the warehouse domain.  

'''
Construct and return futoshiki CSP models.
'''

from cspbase import *
import itertools
import sys


def futoshiki_csp_model_1(initial_futoshiki_board):
    '''Return a CSP object representing a futoshiki CSP problem along 
       with an array of variables for the problem. That is return

       sudoku_csp, variable_array

       where sudoku_csp is a csp representing futoshiki using model_1
       and variable_array is a list of lists

       [ [  ]
         [  ]
         .
         .
         .
         [  ] ]

       such that variable_array[i][j] is the Variable (object) that
       you built to represent the value to be placed in cell i,j of
       the sudokup board (indexed from (0,0) to (8,8))

       
       
       The input board is specified as a list of 9 lists. Each of the
       9 lists represents a row of the board. If a 0 is in the list it
       represents an empty cell. Otherwise if a number between 1--9 is
       in the list then this represents a pre-set board
       position. E.g., the board
    
       -------------------  
       | | |2| |9| | |6| |
       | |4| | | |1| | |8|
       | |7| |4|2| | | |3|
       |5| | | | | |3| | |
       | | |1| |6| |5| | |
       | | |3| | | | | |6|
       |1| | | |5|7| |4| |
       |6| | |9| | | |2| |
       | |2| | |8| |1| | |
       -------------------
       would be represented by the list of lists
       
       [[0,0,2,0,9,0,0,6,0],
       [0,4,0,0,0,1,0,0,8],
       [0,7,0,4,2,0,0,0,3],
       [5,0,0,0,0,0,3,0,0],
       [0,0,1,0,6,0,5,0,0],
       [0,0,3,0,0,0,0,0,6],
       [1,0,0,0,5,7,0,4,0],
       [6,0,0,9,0,0,0,2,0],
       [0,2,0,0,8,0,1,0,0]]
       
       
       This routine returns Model_1 which consists of a variable for
       each cell of the board, with domain equal to {1-9} if the board
       has a 0 at that position, and domain equal {i} if the board has
       a fixed number i at that cell.
       
       Model_1 also contains BINARY CONSTRAINTS OF NOT-EQUAL between
       all relevant variables (e.g., all pairs of variables in the
       same row, etc.), then invoke enforce_gac on those
       constraints. All of the constraints of Model_1 MUST BE binary
       constraints (i.e., constraints whose scope includes two and
       only two variables).

      ---------------inequalities -----------------------------------
      inequalities are another list of lists. 
      ex. [(1,1), '<', (2,1)], [(4,5), '>', (4,6)]]
      (row number, column number)
      
    '''
    futoshiki = CSP('F1')
    board = initial_futoshiki_board[0]
    inequality = initial_futoshiki_board[1]
    '''[[(1,1), '<', (2,1)], [(4,5), '>', (4,6)]]'''

    '''Variables'''
    variables = [] 
    for row in range(len(board)):
      var_row = []
      for column in range(len(board)):
        name = str(row + 1) + ',' + str(column + 1)
        if board[row][column] != 0:
          domain = [board[row][column]]
        else:
          domain = []
          for i in range(len(board)):
            domain.append(i + 1)
        v = Variable(name, domain)
        futoshiki.add_var(v)
        var_row.append(v)
      variables.append(var_row)

    '''[[(1,1), '<', (2,1)], [(4,5), '>', (4,6)]]'''

    '''all inequality '''
    ineq_constraints = []
    for ine in inequality:

      var1_row = ine[0][0] - 1
      var1_col = ine[0][1] - 1

      var2_row = ine[2][0] - 1
      var2_col = ine[2][1] - 1

      var1 = variables[var1_row][var1_col]
      var2 = variables[var2_row][var2_col]

      cons_name = str(var1) + ' ' + ine[1] + ' ' + str(var2)
      cons_scope = [var1, var2]
      new_cons = Constraint(cons_name, cons_scope)

      var1_domain = var1.domain()
      var2_domain = var2.domain()

      sign = ine[1]

      for v1d in var1_domain:
        for v2d in var2_domain:
          if sign == '<':
            if v1d < v2d:
              new_cons.add_satisfying_tuples([(v1d, v2d)])
          else:
            if v1d > v2d:
              new_cons.add_satisfying_tuples([(v1d, v2d)])
      ineq_constraints.append(new_cons)
    
    '''all row constratints not repeated'''
    row_constraints = []
    for row_var in variables:
      cons = itertools.combinations(row_var, 2)
      for i in cons:
        cons_name = str(i);
        cons_scope = []
        for v in i:
          cons_scope.append(v)
        row_constraints.append(Constraint(cons_name,cons_scope))


    
    '''all column constraints not repeated'''
    col_contraints = []
    for c in range(len(board)):
      column_vars = []
      for r in range(len(board)):
        column_vars.append(variables[r][c])
      cons = itertools.combinations(column_vars, 2)
      for i in cons:
        cons_name = str(i);
        cons_scope = []
        for v in i:
          cons_scope.append(v)
        col_contraints.append(Constraint(cons_name,cons_scope))


    '''adding tuples to row constratints'''
    for rc in row_constraints:
      rc_var = rc.get_scope()
      if rc_var[1].domain_size() != 1 and rc_var[0].domain_size() != 1:
        tups = itertools.permutations(rc_var[0].domain(), 2)
      elif rc_var[1].domain_size() == 1 and rc_var[0].domain_size() == 1:
        tups = itertools.product(rc_var[0].domain(), rc_var[1].domain())
      else:
        adj_dom = []
        if rc_var[1].domain_size() != 1:
          adj_dom = rc_var[1].domain()
          adj_dom.remove(rc_var[0].domain()[0])
          tups = itertools.product(rc_var[0].domain(), adj_dom)
        else:
          adj_dom = rc_var[0].domain()
          print(adj_dom)
          print(rc_var[1].domain()[0])
          adj_dom.remove(rc_var[1].domain()[0])
          tups = itertools.product(adj_dom, rc_var[1].domain())

      for t in tups:
        rc.add_satisfying_tuples([t])

        
    '''adding tuples to column constratints'''
    for cl in col_contraints:
      cl_var = cl.get_scope()
      if cl_var[1].domain_size() != 1 and cl_var[0].domain_size() != 1:
        tups = itertools.permutations(cl_var[0].domain(), 2)
      elif cl_var[1].domain_size() == 1 and cl_var[0].domain_size() == 1:
        tups = itertools.product(cl_var[0].domain(), cl_var[1].domain())
      else:
        adj_dom = []
        if cl_var[1].domain_size() != 1:
          adj_dom = cl_var[1].domain()
          adj_dom.remove(cl_var[0].domain()[0])
          tups = itertools.product(cl_var[0].domain(), adj_dom)
        else:
          adj_dom = cl_var[0].domain()
          adj_dom.remove(cl_var[1].domain()[0])
          tups = itertools.product(adj_dom, cl_var[1].domain())

      for t in tups:
        cl.add_satisfying_tuples([t])


    '''adding constraints to csp'''
    for cons in row_constraints:
      futoshiki.add_constraint(cons)

    for cons in col_contraints:
      futoshiki.add_constraint(cons)

    for cons in ineq_constraints:
      futoshiki.add_constraint(cons)

    return futoshiki, variables

##############################

def futoshiki_csp_model_2(initial_futoshiki_board):
    '''Return a CSP object representing a futoshikiv CSP problem along 
       with an array of variables for the problem. That is return

       sudoku_csp, variable_array

       where sudoku_csp is a csp representing sudoku using model_1
       and variable_array is a list of lists

       [ [  ]
         [  ]
         .
         .
         .
         [  ] ]

       such that variable_array[i][j] is the Variable (object) that
       you built to represent the value to be placed in cell i,j of
       the sudokup board (indexed from (0,0) to (8,8))

    The input board takes the same input format (a list of 9 lists
    specifying the board as sudoku_csp_model_1.
    
    The variables of model_2 are the same as for model_1: a variable
    for each cell of the board, with domain equal to {1-9} if the
    board has a 0 at that position, and domain equal {i} if the board
    has a fixed number i at that cell.

    However, model_2 has different constraints. In particular, instead
    of binary non-equals constaints model_2 has 27 all-different
    constraints: all-different constraints for the variables in each
    of the 9 rows, 9 columns, and 9 sub-squares. Each of these
    constraints is over 9-variables (some of these variables will have
    a single value in their domain). model_2 should create these
    all-different constraints between the relevant variables, then
    invoke enforce_gac on those constraints.
      

    ---------------inequalities -----------------------------------
      inequalities are another list of lists. 
      ex. [(1,1), '<', (2,1)], [(4,5), '>', (4,6)]]
      (row number, column number)

    '''

    futoshiki = CSP('F1')
    board = initial_futoshiki_board[0]
    inequality = initial_futoshiki_board[1]
    '''[[(1,1), '<', (2,1)], [(4,5), '>', (4,6)]]'''

    '''Variables'''
    variables = []
    for row in range(len(board)):
      var_row = []
      for column in range(len(board)):
        name = str(row + 1) + ',' + str(column + 1)
        if board[row][column] != 0:
          domain = [board[row][column]]
        else:
          domain = []
          for i in range(len(board)):
            domain.append(i + 1)
        v = Variable(name, domain)
        futoshiki.add_var(v)
        var_row.append(v)
      variables.append(var_row)
    
    '''all inequality '''
    ineq_constraints = []
    for ine in inequality:

      var1_row = ine[0][0] - 1
      var1_col = ine[0][1] - 1

      var2_row = ine[2][0] - 1
      var2_col = ine[2][1] - 1

      var1 = variables[var1_row][var1_col]
      var2 = variables[var2_row][var2_col]

      cons_name = str(var1) + ' ' + ine[1] + ' ' + str(var2)
      cons_scope = [var1, var2]
      new_cons = Constraint(cons_name, cons_scope)

      var1_domain = var1.domain()
      var2_domain = var2.domain()

      sign = ine[1]

      for v1d in var1_domain:
        for v2d in var2_domain:
          if sign == '<':
            if v1d < v2d:
              new_cons.add_satisfying_tuples([(v1d, v2d)])
          else:
            if v1d > v2d:
              new_cons.add_satisfying_tuples([(v1d, v2d)])
      ineq_constraints.append(new_cons)    
    
    '''all row constratints not repeated'''
    row_constraints = []
    for row_num in variables:
      cons_scope = []
      for row_var in row_num:
        cons_scope.append(row_var)
        cons_name = str(row_num);
      row_constraints.append(Constraint(cons_name,cons_scope))


    
    '''all column constraints not repeated'''
    col_contraints = []
    for c in range(len(board)):
      column_vars = []
      for r in range(len(board)):
        column_vars.append(variables[r][c])
      cons_scope = []
      for v in column_vars:
        cons_scope.append(v)
      cons_name = str(column_vars)
      col_contraints.append(Constraint(cons_name,cons_scope))

    '''adding tuples to row constratints'''
    for rc in row_constraints:
      domain = []
      for i in range(len(board)):
        domain.append(i + 1)
      insert_back = []
      rc_var = rc.get_scope()
      for v in  range(len(rc_var)):
        if rc_var[v].domain_size() == 1:
          safe = (rc_var[v].domain()[0], v)
          domain.remove(rc_var[v].domain()[0])
          insert_back.append(safe)
      a = itertools.permutations(domain, len(domain))
      for d in a :
        tup = list(d)
        for ins in insert_back:
          tup.insert(ins[1], ins[0])
        rc.add_satisfying_tuples([tup])



    '''adding tuples to column constratints'''
    for cc in col_contraints:
      domain = []
      for i in range(len(board)):
        domain.append(i + 1)
      insert_back = []
      cc_var = cc.get_scope()
      for v in  range(len(cc_var)):
        if cc_var[v].domain_size() == 1:
          safe = (cc_var[v].domain()[0], v)
          domain.remove(cc_var[v].domain()[0])
          insert_back.append(safe)
      a = itertools.permutations(domain, len(domain))
      for d in a :
        tup = list(d)
        for ins in insert_back:
          tup.insert(ins[1], ins[0])
        cc.add_satisfying_tuples([tup])

    '''adding constraints to csp'''
    for cons in row_constraints:
      futoshiki.add_constraint(cons)

    for cons in col_contraints:
      futoshiki.add_constraint(cons)

    for cons in ineq_constraints:
      futoshiki.add_constraint(cons)
    return futoshiki, variables


'''if __name__=="__main__":
  futoshiki_csp_model_1([[
      [0,7,0,8,5,0,0,0],
      [0,8,0,0,0,1,5,0],
      [0,0,0,3,0,0,4,0],
      [0,3,0,0,0,0,0,0],
      [1,0,5,0,0,0,7,0],
      [7,0,0,0,0,0,0,2],
      [0,0,1,0,0,6,0,0],
      [2,0,3,7,0,0,0,6]], 
      [[(1,1), '<', (2,1)], [(4,5), '>', (4, 6)]]])'''