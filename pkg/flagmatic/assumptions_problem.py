# -*- coding: utf-8 -*-
"""

flagmatic 2

Copyright (c) 2012, E. R. Vaughan. All rights reserved.

Redistribution and use in source and binary forms, with or without modification,
are permitted provided that the following conditions are met:

1) Redistributions of source code must retain the above copyright notice, this
list of conditions and the following disclaimer.

2) Redistributions in binary form must reproduce the above copyright notice,
this list of conditions and the following disclaimer in the documentation and/or
other materials provided with the distribution.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND
ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR
ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
(INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON
ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

"""

from sage.rings.all import Integer, Rational
from sage.misc.misc import SAGE_TMP
from os.path import join

from hypergraph_flag import make_graph_block, print_graph_block
from three_graph_flag import *
from graph_flag import *
from oriented_graph_flag import *
from multigraph_flag import *
from problem import *

class AssumptionsProblem(Problem):

    def __init__(self, flag_cls, order=None, **kwargs):    

        Problem.__init__(self, flag_cls, order, **kwargs)

        self._assumptions = []
        self._assumption_flags = []
        self._classic_assumptions = [] # assumptions without labels

    def clear_densities(self):
        
        self._density_graphs = []
        self._active_densities = []
        self._density_coeff_blocks = []        
        self._compute_densities()

    def set_inactive_densities(self, *args):
        r"""
        Specifies that the coefficients of certain densities should be zero.
        
        INPUT:
        
        - arguments should be integers, specifying the indices of densities that should be
          marked as being "inactive".
        """
        for arg in args:
            di = int(arg)
            if not di in range(len(self._density_graphs)):
                raise ValueError
            if di in self._active_densities:
                self._active_densities.remove(di)
            else:
                sys.stdout.write("Warning: density %d is already inactive.\n" % di)

    def add_classic_assumptions(self, *args):
        """Add simple assumptions on densities of linear combinations of admissible graphs(flags).
        
        INPUT:

        - (assumption1, assumption2, ...), where 
        assumption = ([(graph, coeff), ..., (graph_n, coeff_n)], bound, type)
        here 'type' = 0 (if equality bound), -1 (if upper bound given, i.e. >=).

        EXAMPLE:

        - Input: p.add_classic_assumptions(([("3:1223",1)], 1/2, -1)) will
        be interpreted as: d(P_3) >= 1/2. If want d(P_3) <= 1/2, feed
        the function with ([("3:1223", -1)], -1/2, -1)

        - Input: p.add_classic_assumptions(([("3:1223",1)], 1/2, 0)) will be
        interpreted as: d(P_3) = 1/2, i.e. the same as the following
        input: 
        p.add_classic_assumptions(([("3:1223",1)], 1/2, -1), ([("3:1223",-1)], 1/2, -1))
        which is interpreted as:
         d(P_3) >=  1/2
        -d(P_3) >=  1/2
        """

        for arg in args:
            
            ass_lincomb = list() # will store this assumption (rewritten arg to the form ass >= 0, or ass = 0)
            
            for g in self.graphs:

                coeff_g = -1*arg[1] # express bound in terms of admissible graphs

                for term in arg[0]: # run through all terms in linear combination of the assumption
                    coeff = term[1]
                    ass_graph = GraphFlag(term[0])
                    coeff_g += term[1]*g.subgraph_density(GraphFlag(term[0]))

                ass_lincomb.append(coeff_g)

            if arg[2] == 0: # if assumption was equality 'lincomb = bound'
                
                self._classic_assumptions.append(ass_lincomb)
                self._classic_assumptions.append([-1*x for x in ass_lincomb]) # 
            
            else: # if assumption was inequality 'lincomb >= bound'
                
                self._classic_assumptions.append(ass_lincomb)


    def print_classic_assumptions(self, display_zero_densities=False):
        
        if display_zero_densities:
            for j in range(len(self._classic_assumptions)):
                ass_j = self._classic_assumptions[j]
                textform = "0 <= c" + str(j) + "*("
                for i in range(len(self._graphs)):
                    textform = textform + str(ass_j[i])+"*'"+self.graphs[i].__str__()+ "' "
                textform = textform.strip()+ ")"
                print textform
        else:
            for j in range(len(self._classic_assumptions)):
                ass_j = self._classic_assumptions[j]
                textform = "0 <= c" + str(j) + "*("
                for i in range(len(self._graphs)):
                    if not ass_j[i] == 0:
                        textform = textform + str(ass_j[i])+"*'"+self.graphs[i].__str__()+ "' "
                textform = textform.strip()+ ")"
                print textform


    def add_assumption(self, typegraph, lincomb, const=0, equality=False):
        """
        Convert assumption from the general form:
        [linear combination of flags on one type] >= c   OR
        [linear combination of flags on one type] == c 

        into an assumptions of the form
        [linear combination of flags on one type] >= 0

        INPUT:
        
        - typegraph: # it is the common type or the entire assumption,
                     # e.g. "3:121323" for labelled triangle
        
        - lincomb: # this is the linear combination of terms (flag,
                   # coef) as a list, i.e. LHS of the assumption
        
        - const: # RHS of the assumption (should be some rational in
                 # form a/b or a)
        
        - equality: # whether the assumption is equality True or
                    # inequality False; default is False

        EXAMPLE:
        
        # assume edge density = 1/2: 
        problem = GraphAssumptionsProblem(4)
        problem.add_assumption("0:", [("2:12(0)", 1)], 1/2, equality=True)
        
        """

        if self._flag_cls().r == 2:

            try:
                tg = GraphFlag(typegraph)
                tg.make_minimal_isomorph()

                cst = Rational(const)
                eq = equality
                indep = False
                
                lcomb = [(GraphFlag(g), Rational(c)) for g,c in lincomb]
                for term in lcomb: term[0].make_minimal_isomorph()  # convert flag to the one Flagmatic knows
                
                # if RHS nonzero, add a type to the LHS with -const coefficient (works with '0:' type as well)
                if const:
                    fg = GraphFlag(tg._repr_() + "("+str(tg.n)+")")
                    lcomb.append((fg, -cst))
                    # maker RHS zero. (not necessary though, not used again)
                    cst = 0

            except ValueError:
                print "You are trying to feed this function unhealthy things!"

        elif self._flag_cls().r == 3:

            try:
                tg = ThreeGraphFlag(typegraph)
                tg.make_minimal_isomorph()

                cst = Rational(const)
                eq = equality
                indep = False
                
                lcomb = [(ThreeGraphFlag(g), Rational(c)) for g,c in lincomb]
                for term in lcomb: term[0].make_minimal_isomorph()  # convert flag to the one Flagmatic knows

                
                # if RHS nonzero, add a type to the LHS with -const coefficient (works with '0:' type as well)
                if const:
                    fg = ThreeGraphFlag(tg._repr_() + "("+str(tg.n)+")")
                    lcomb.append((fg, -cst))
                    # make RHS zero. (not necessary though, not used again)
                    cst = 0

            except ValueError:
                print "You are trying to feed this function unhealthy things!"
            

        # translate the assumption to the simple ones and add them one by one

        if eq: # assumption is equality

            indep = True # in this case assumption does not to go the objective function
            minus_lcomb = [(g,-c) for g,c in lcomb]

            self.add_ass(tg, lcomb, independent=indep)
            self.add_ass(tg, minus_lcomb, independent=indep)


        else: # assumption is already inequality

            self.add_ass(tg, lcomb, independent=indep)
                          
        
    def add_ass(self, tg, terms, independent=False):
        """
        Not intended to be called by user. Use add_assumption() instead. 
        Adds assumption of the form [linear combintaion of flags on same type] >= 0
        
        INPUT:

        - tg: # it is the common type or the entire assumption,
              # e.g. GraphFlag("3:121323") for labelled triangle
        
        - terms: # this is the linear combination of terms (flag,
                 # coef) as a list, i.e. LHS of the assumption
        

        - independent # no restrictions on coefficients by which the
                      # assumptions are multiplied, except for
                      # non-negativity; default is False

        EXAMPLE:
        
        # assume edge density = 1/2: 
        problem = GraphAssumptionsProblem(4)
        problem.add_assumption(GraphFlag("0:"), [(GraphFlag("2:12(0)"), 1), (GraphFlag("1:(0)"), -1/2)]
        problem.add_assumption(GraphFlag("0:"), [(GraphFlag("2:12(0)"), -1), (GraphFlag("1:(0)"), 1/2)])
        """
        
        # DO NOT clear densities if not adding first assumption
        if not self._assumptions:
            self.clear_densities()

        self.state("set_objective", "yes")
        
        m = self.n - max([t[0].n for t in terms]) + tg.n    # m := order of flags that multiply assumption -> 'assumption_flags'

        # generate flags to multiply assumptions with
        assumption_flags = self._flag_cls.generate_flags(m, tg, forbidden_edge_numbers=self._forbidden_edge_numbers,
                                                    forbidden_graphs=self._forbidden_graphs,
                                                    forbidden_induced_graphs=self._forbidden_induced_graphs)

        num_densities = len(assumption_flags)
        sys.stdout.write("Added %d quantum graphs.\n" % num_densities) # one quantum graph per assumption_flag
        
        num_graphs = len(self._graphs)
        quantum_graphs = [[Integer(0) for i in range(num_graphs)] for j in range(num_densities)]

        assumption_flags_block = make_graph_block(assumption_flags, m)
        graph_block = make_graph_block(self._graphs, self.n)

        for i in range(len(terms)): # run through terms in the assumption
            fg = terms[i][0] # flag graph of term i
            flags_block = make_graph_block([fg], fg.n) 
            rarray = self._flag_cls.flag_products(graph_block, tg, flags_block, assumption_flags_block)
            for row in rarray:
                gi = row[0]
                j = row[1]  # always 0 because always multiplying the same
                k = row[2]
                value = Integer(row[3]) / Integer(row[4])
                quantum_graphs[k][gi] += value * terms[i][1] # k = index in num_densities, gi = index in num_graphs

        # just making a record    
        self._assumptions.append((tg, terms))
        self._assumption_flags.append(assumption_flags)
        
        num_previous_densities = len(self._density_graphs)

        # filling density graphs
        for qg in quantum_graphs:
            dg = []
            for gi in range(num_graphs):
                if qg[gi] != 0:
                    dg.append((self._graphs[gi], qg[gi]))
            self._density_graphs.append(dg)

        # update active densities (indices of active density graphs // not admissible graphs!)
        new_density_indices = range(num_previous_densities, num_previous_densities + len(quantum_graphs))
        self._active_densities.extend(new_density_indices)
        
        if not independent: # if independent==False (default)
            # make assumptions look like one big assumption => will
            # force coefficients to sum to 1 (must be some strictly
            # positive)
            if not self._density_coeff_blocks: 
                self._density_coeff_blocks.append(new_density_indices)
            else:
                self._density_coeff_blocks[0].extend(new_density_indices)

        self._compute_densities()


    def _augment_certificate(self, data):
        
        if len(self._assumptions) == 0:
            return
        
#         axiom_strings = []
#         for axiom in self._axioms:
#             axs = []
#             for g, coeff in axiom[1]:
#                 if coeff == 1:
#                     axs.append(str(g))
#                 else:
#                     cs = str(coeff)
#                     if " " in cs:
#                         cs = "(%s)" % cs
#                     axs.append("%s*%s" % (cs, g))
#             axiom_strings.append("[%s] %s >= 0" % (axiom[0], " + ".join(axs)))

        assumption_strings = ["[%s] %s >= 0" %
            (assumption[0], self._flag_cls.format_combination(assumption[1]))
            for assumption in self._assumptions]
        
        data["assumptions"] = assumption_strings
        data["assumption_flags"] = self._assumption_flags
        
        data["admissible_graph_densities"] = self._densities
        data["density_coefficients"] = self._exact_density_coeffs

    def add_codegree_assumption(self, value, independent=True):

        if not self._flag_cls().r == 3:
            raise NotImplementedError
    
        self.add_assumption("2:", [("3:123(2)", 1)], value, equality=False, independent=independent)

    def add_degree_assumption(self, value, independent=True):
    
        if self._flag_cls().oriented:
            raise NotImplementedError
    
        if self._flag_cls().r == 3:
            self.add_assumption("1:", [("3:123(1)", 1)], value, equality=False, independent=independent)

        elif self._flag_cls().r == 2:
            self.add_assumption("1:", [("2:12(1)", 1)], value, equality=False, independent=independent)

    # TODO: fix this!

    def add_equal_degrees_assumption(self, independent=True):
    
        if self._flag_cls().oriented:
            raise NotImplementedError
    
        if self._flag_cls().r == 3:
    
            tg = ThreeGraphFlag("2:")
            f1 = ThreeGraphFlag("4:134(2)")
            f2 = ThreeGraphFlag("4:123134(2)")
            f3 = ThreeGraphFlag("4:123124134(2)")
            f4 = ThreeGraphFlag("4:234(2)")
            f5 = ThreeGraphFlag("4:123234(2)")
            f6 = ThreeGraphFlag("4:123124234(2)")
            self.add_assumption(tg, [(f1, Integer(1)), (f2, Integer(1)), (f3, Integer(1)),
                (f4, Integer(-1)), (f5, Integer(-1)), (f6, Integer(-1))], independent=independent)

        elif self._flag_cls().r == 2:

            tg = GraphFlag("2:")
            f1 = GraphFlag("3:13(2)")
            f2 = GraphFlag("3:23(2)")
            self.add_assumption(tg, [(f1, Integer(1)), (f2, -Integer(1))], independent=independent)
            tg = GraphFlag("2:12")
            f1 = GraphFlag("3:1213(2)")
            f2 = GraphFlag("3:1223(2)")
            self.add_assumption(tg, [(f1, Integer(1)), (f2, -Integer(1))], independent=independent)

    def add_out_degree_assumption(self, value, independent=True):
    
        if not (self._flag_cls().r == 2 and self._flag_cls().oriented):
            raise NotImplementedError
    
        tg = OrientedGraphFlag("1:")
        f1 = OrientedGraphFlag("2:12(1)")
        f2 = OrientedGraphFlag("1:(1)")
        self.add_assumption(tg, [(f1, Integer(1)), (f2, -value)], independent=independent)

    def add_in_degree_assumption(self, value, independent=True):
    
        if not (self._flag_cls().r == 2 and self._flag_cls().oriented):
            raise NotImplementedError
    
        tg = OrientedGraphFlag("1:")
        f1 = OrientedGraphFlag("2:21(1)")
        f2 = OrientedGraphFlag("1:(1)")
        self.add_assumption(tg, [(f1, Integer(1)), (f2, -value)], independent=independent)

    def make_codegree_problem(self, value):

        self.clear_densities()
        self.add_codegree_assumption(value, False)

    def make_degree_problem(self, value):

        self.clear_densities()
        self.add_degree_assumption(value, False)

    def show_large_densities(self, larger_than=1e-4):

        self.state("run_sdp_solver", "ensure_yes")

        num_densities = len(self._densities)

        densities_to_use = []
        for j in range(num_densities):
            if self._sdp_density_coeffs[j] > larger_than:
                densities_to_use.append(j)

        sys.stdout.write("Densities: %s\n" % (densities_to_use,))

        sys.stdout.write("Coefficients: %s\n" % ([self._sdp_density_coeffs[j] for j in densities_to_use],))

        sys.stdout.write("Other densities: %s\n" % ([di for di in range(num_densities) if not di in densities_to_use],))

    def show_independent_densities(self):

        self.state("run_sdp_solver", "ensure_yes")
    
        num_sharps = len(self._sharp_graphs)
        num_densities = len(self._densities)
    
        densities_to_use = []
        
        if len(self._sdp_density_coeffs) > 0:
            density_indices = sorted(range(num_densities), key=lambda i: -self._sdp_density_coeffs[i])
        else:
            density_indices = range(num_densities)
        
        DR = matrix(self._field, 0, num_sharps, sparse=True)
        EDR = matrix(self._field, 0, num_sharps, sparse=True)
                
        sys.stdout.write("Constructing DR matrix")
        
        for j in density_indices:
            new_row = matrix(QQ, [[self._densities[j][gi] for gi in self._sharp_graphs]], sparse=True)
            if new_row.is_zero():
                continue
            try:
                X = EDR.solve_left(new_row)
                continue
            except ValueError:
                DR = DR.stack(new_row)
                EDR = EDR.stack(new_row)
                EDR.echelonize()
                densities_to_use.append(j)
                sys.stdout.write(".")
                sys.stdout.flush()
            
        sys.stdout.write("\n")
        sys.stdout.write("Rank is %d.\n" % DR.nrows())

        sys.stdout.write("Densities: %s\n" % (densities_to_use,))

        sys.stdout.write("Coefficients: %s\n" % ([self._sdp_density_coeffs[j] for j in densities_to_use],))
    
    def problem_with_densities(self, densities_to_use):
    
        if len(densities_to_use) == 0:
            raise ValueError
    
        if len(self._assumptions) != 1 or hasattr(self, "_free_densities"):
            raise NotImplementedError
    
        new_densities = [self._densities[j] for j in densities_to_use]
        new_assumption_flags = [self._assumption_flags[0][j] for j in densities_to_use]
        
        new_problem = copy(self)
        new_problem._densities = new_densities
        new_problem._assumption_flags = [new_assumption_flags]
        
        if hasattr(new_problem, "_sdp_Q_matrices"):
            del new_problem._sdp_Q_matrices
        if hasattr(new_problem, "_sdp_Qdash_matrices"):
            del new_problem._sdp_Qdash_matrices
        if hasattr(new_problem, "_exact_Q_matrices"):
            del new_problem._exact_Q_matrices
        if hasattr(new_problem, "_exact_Qdash_matrices"):
            del new_problem._exact_Qdash_matrices
        if hasattr(new_problem, "_sdp_density_coeffs"):
            del new_problem._sdp_density_coeffs
        if hasattr(new_problem, "_exact_density_coeffs"):
            del new_problem._exact_density_coeffs
        if hasattr(new_problem, "_sdp_bounds"):
            del new_problem._sdp_bounds
        if hasattr(new_problem, "_bounds"):
            del new_problem._bounds
        
        new_problem.state("set_objective", "yes")

        return new_problem




    def leave_footprint(self, filename=None):
        """
        Write a file with info necessary for verifying the result of
        the current assumptions problem.
        """
        fname = os.path.join(unicode(SAGE_TMP),"assumptions_problem.cert")
        
        if filename:
            fname = filename
        
        try:
            fout = open(fname, 'w')
        except IOError:
            print "Something is wrong with your filename..."

        fout.write("Admissible Graphs\n\n")
        for graph in self.graphs:
            fout.write(str(graph) + '\n')

        fout.write("\nTypes\n\n")
        for i in range(len(self.types)):
            fout.write(str(self.types[i]) + '\n')
 
        fout.write("\nFlags\n\n")
        for tflags in self.flags:
            for flag in tflags:
                fout.write(str(flag) + '\n')
            fout.write('\n')

        fout.write("Flag Product Densities\n\n")
        for tproducts in self._product_densities_arrays:
            for prod in tproducts:
                fout.write(' '.join([str(x) for x in prod]) + '\n')
            fout.write("\n")
        
        fout.write("Density Graphs\n\n")
        for dg in self._density_graphs:
            fout.write(str(dg))
            fout.write("\n")
        
        fout.close()
        
        print "Footprint in", fname



def GraphAssumptionsProblem(order=None, **kwargs):
    r"""
    Returns an AssumptionsProblem object, that will represent a Turán-type graph axioms
    problem. For help with AssumptionsProblem objects, enter

    sage: help(AssumptionsProblem)
    """
    return AssumptionsProblem(GraphFlag, order, **kwargs)

def ThreeGraphAssumptionsProblem(order=None, **kwargs):
    r"""
    Returns an AssumptionsProblem object, that will represent a Turán-type 3-graph axioms
    problem. For help with AssumptionsProblem objects, enter

    sage: help(AssumptionsProblem)
    """
    return AssumptionsProblem(ThreeGraphFlag, order, **kwargs)
