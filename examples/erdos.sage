
"""
pd = GraphAssumptionsProblem(3, forbid="3:121323")
#pd.add_classic_assumptions(([("3:12", 1)], 1/6, -1))
#pd.clear_densities()
pd.add_assumption("1:", [("2:12(1)", 1), ("1:(1)", -1/2)]) # assumption: 1-rooted edge density >= 1/2
#pd.add_assumption("2:", [("2:12(2)", 1), ("2:(2)", -1/2), ("2:12(2)", -1/2)]) # assumption: 1-rooted edge density >= 1/2
pd.solve_sdp(show_output=True, solver="csdp")
pd.leave_footprint()
verify_assumptions_problem()
"""


pd = GraphAssumptionsProblem(5)
pd.add_assumption("3:121323", [("4:1213231424(3)", -1), ("4:1213231434(3)", -1), ("4:1213233424(3)", -1), ("4:121323142434(3)", -1)])
pd.add_assumption("0:", [("2:12(0)", 1), ("1:(0)", -1/2)])
pd.add_assumption("0:", [("2:12(0)", -1), ("1:(0)", 1/2)])
pd.solve_sdp(show_output=True, solver="csdp")
pd.leave_footprint()
verify_assumptions_problem()


#humanise_all()

