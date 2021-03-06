problem = GraphProblem(5, forbid=(3,3), density="5:1223344551")#, type_orders=[3])
construction = GraphBlowupConstruction("5:1223344551")
problem.set_extremal_construction(construction)
problem.solve_sdp()
problem.make_exact()