"""
This file verifies result of the assumptions problem given to flagmatic. 
Good night and good luck.


Run from within Sage (tested with 6.1.1 on Ubuntu 12.4)
"""

import os

from sage.misc.misc import SAGE_TMP 
from sage.rings.all import Integer, Rational, RR, QQ
from sage.matrix.constructor import *
    

def verify_assumptions_problem(sdpout=None, certificate=None, verified=None):
    """
    Verify the result given via the AssumptionsProblem.
    
    INPUT:
    
    - sdpout: # location of the sdp.out file (given by CSDP solver)
    
    - certificate: # location of the file that was created by the
                   # 'leave_footprint()' method of the
                   # AssumptionsProblem

    - verified: # location of the file where the result/verdict is to
                # be written
    
    EXAMPLE:

    sage: verify_assumptions_problem() # sdp.out is in default
                                       # location, certificate also
                                       # verified in current location
    """


    #----------------------- helper function -----------------------

    def parse_product_density(string):
        """
        The string is expected in the format 'H F1 F2 a b' and it means
        p(F1,F2,H) = a/b.
        """
        s = string.strip() # lose whitespaces around string
        H,f1,f2,a,b = s.split()
        return list([Integer(H), Integer(f1), Integer(f2), Rational(Integer(a)/Integer(b))])
    
    def parse_quantum_graph(string):
        """
        The expected string is a list of 2-tuples (graph,
        density). The whole thing is a string with possible
        whitespaces around it, e.g.
        '[(5:1213142324, -1/10), (5:121314232434, -1/5)]\n'
        """
        s = string.strip()[1:-1] # lose whitespaces and square brackets
        listified = s.replace('(', '').replace(')', '').split(', ')

        return zip(listified[0::2], map(Rational, listified[1::2]))


    def readblock(store_to):
        
        ln = certfile.readline().strip()
        while ln:
            store_to.append(ln)
            ln = certfile.readline().strip()


    #------------------ file handling -------------------------

    sdpout_path = os.path.join(unicode(SAGE_TMP), 'sdp.out')
    cert_path = os.path.join(unicode(SAGE_TMP), 'assumptions_problem.cert')
    verified_path = 'verification.rslt'

    # if user specified files given use them
    if sdpout: default_sdpout_path = sdpout
    if certificate: default_cert_path = certificate
    if verified: default_verified_path = verified

    # open files
    try:

        sdpfile = open(sdpout_path, 'r')
        certfile = open(cert_path, 'r')
        verifile = open(verified_path, 'w')

    except IOError:

        print "Trouble opening one of the following files:"
        print sdpout_path + 'for reading'
        print cert_path + 'for reading'
        print verified_path + 'for writing'
        
    #------------------- learn from files ---------------------
    
    
    admissible_graphs = list()
    types = list()
    flags = list() # list of lists (one for each type)
    flag_product_densities = list() # list of lists (one for each type)
    density_graphs = list() # list of lists (one for each density graph [[assumption*flag]])

    # read graphs
    ln = certfile.readline().strip()
    if ln == 'Admissible Graphs': 

        certfile.readline() # read off empty line
        readblock(admissible_graphs)

    num_admissible_graphs = len(admissible_graphs)
    

    # read types
    ln = certfile.readline().strip()
    if ln == 'Types': 

        certfile.readline() # read off empty line
        readblock(types)

    num_types = len(types)
    

    # read flags
    ln = certfile.readline().strip()
    if ln == 'Flags':

        certfile.readline() # read off empty line
        for i in range(num_types): 

            tflags = list()
            readblock(tflags)
            flags.append(tflags)


    # read flag product densities 
    # i.e. p(F,F',H) for each type
    ln = certfile.readline().strip()
    if ln == 'Flag Product Densities':

        certfile.readline() # read off empty line
        for i in range(num_types):

            tproducts = list()
            readblock(tproducts)
            tproducts = [parse_product_density(x) for x in tproducts]
            flag_product_densities.append(tproducts)
    
    
    # read density graphs
    ln = certfile.readline().strip()
    if ln == 'Density Graphs':

        certfile.readline() # read off empty line
        ln = certfile.readline()
        while not ln == '':

            density_graphs.append(parse_quantum_graph(ln))
            ln = certfile.readline()
    
    num_density_graphs = len(density_graphs)


    # sdp.out file -----------------------------

    Q_matrices = list() #[zero_matrix(RR, len(flags[x])) for x in range(len(flags))] # we have one coeff matrix for each type; size is equal to num_flags on that type
    coeffs = list()
    
    # initialize Q_matrices
    for i in range(num_types):
        Q_matrices.append(list())
        for j in range(len(flags[i])):
            Q_matrices[i].append([0 for x in flags[i]])

    sdpfile.readline() # read off the first line
    for l in sdpfile:

        line = l.strip()
        if not line[0] == '2':
            pass # not interested in primal SDP

        else:
            
            data = line.split()
            
            if data[1] == '1': pass # this is just an objective value
            
            block = int(data[1])-2 # python indexes from 0 not 1, and blocks start at 2
            i = int(data[2])-1 # python indexes from 0
            j = int(data[3])-1 
            val = float(data[4])

            if block in range(num_types):
                Q_matrices[block][i][j] = val
                Q_matrices[block][j][i] = val
            
            if block in range(num_types, num_types+1):
                pass
            
            if block in range(num_types+1, num_types+2):
                coeffs.append(val)


    # verify ------------------------------------

    # check if coeffs are non-negative and if they add to 1
    
    verifile.write("Sum of quantum graphs coefficients is "+str(sum(coeffs)) + "\n")

    ALL_NONNEGATIVE = True
    for coeff in coeffs:
        if coeff < 0:
            verifile.write("There is a negative coefficient: " + str(coeff))
            ALL_NONNEGATIVE = False
            break

    if ALL_NONNEGATIVE:
        verifile.write("All coeffs are non-negative.")
            

    # check if Q_matrices are sdp
    verifile.write("\n\nSDP Matrices \n \n")
    i = 0
    for m in Q_matrices:
        verifile.write("Type " + str(i) + " eigenvalues" + ":\n")
        verifile.write(str(matrix(m).eigenvalues()) + "\n") # give eigenvalues for the moment

        i += 1
    
    # check whether coeffs in front of admissible graphs are non-positive
    L = max([len(x) for x in admissible_graphs])
    graph_coeffs = list()
    verifile.write("\n\nGraph Coefficients\n")
    index_graph = 0
    for graph in admissible_graphs: # for each admissible graph compute its coeff

        coeff_graph = 0
        
        # contribution from [[p^tQp]]
        tp_i = 0
        for tp in flag_product_densities:
            for dens in tp:
                if dens[0] == index_graph and dens[1] == dens[2]:
                    coeff_graph += dens[3]*Q_matrices[tp_i][dens[1]][dens[2]]
                elif dens[0] == index_graph:
                    coeff_graph += dens[3]*Q_matrices[tp_i][dens[1]][dens[2]]*2 # not on diagonal
            tp_i += 1

        # contribution from coeffs
        index_dg = 0
        for dg in density_graphs:
            for g,d in dg:
                if g == graph: coeff_graph += coeffs[index_dg]*d
            index_dg += 1
        
        graph_coeffs.append(coeff_graph)

        # write into file
        verifile.write("\n"+ graph + " "*(L-len(graph)) + "\t " + str(coeff_graph))

        index_graph += 1
