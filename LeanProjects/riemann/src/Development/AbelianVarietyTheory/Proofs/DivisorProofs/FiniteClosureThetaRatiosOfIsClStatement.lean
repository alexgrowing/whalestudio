import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteClosureThetaRatiosOfIsCl
import Mathlib
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_closure_theta_ratios_of_isCl' : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (M : RatModel o Ω) (J : Type) (t : J → Ω), M.IsCl t → Module.Finite (Subfield.closure (Set.range (algebraMap o Ω) ∪ {x | ∃ i j : S.Gam × J, x = S.th j.1 * t j.2 / (S.th i.1 * t i.2)})) Ω := by
  first | exact @GlobalTheory.ZH.finite_closure_theta_ratios_of_isCl | exact GlobalTheory.ZH.finite_closure_theta_ratios_of_isCl | (intros; apply GlobalTheory.ZH.finite_closure_theta_ratios_of_isCl <;> assumption)
