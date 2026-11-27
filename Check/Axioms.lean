module

public import Solution
public import RankRings

@[expose] public section
/-! Prints the axioms of the results. Expected for each: `propext`, `Classical.choice`, `Quot.sound`. -/

#print axioms RankRingsChallenge.elek_countable
#print axioms RankRingsChallenge.elek_complex
#print axioms RankRingsChallenge.finite_form
#print axioms RankRings.main_countable_char0
#print axioms RankRings.main_complex
#print axioms RankRings.finite_form
#print axioms RankRings.finite_form_char0
#print axioms RankRings.finite_form_of_char0
#print axioms RankRings.char_contrast
#print axioms RankRings.exists_config_modL
#print axioms RankRings.ineq_C
#print axioms RankRings.exotic_RR
#print axioms RankRings.no_config
#print axioms RankRings.Gen.no_config
#print axioms RankRings.rr_regular
#print axioms RankRings.eps_char0
#print axioms RankRings.eps_char0_paper
#print axioms RankRings.finite_form_paper
#print axioms RankRings.config_modL
#print axioms RankRings.rel_modL
#print axioms RankRings.finite_form_modL

end
