import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LpCharCompatibilities
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MonodromyZeroOfWeilDeligneRepClassIff
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lp_char_compatibilities : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (a b c : WD h) (s : ℝ), (a.lpSum b).lpChar c = (a.lpChar c).lpSum (b.lpChar c) ∧ (a.lpTw s).lpChar c = (a.lpChar c).lpTw s ∧ a.lpChar (c.lpTw s) = (a.lpChar c).lpTw s ∧ (a.lpChar b).lpChar c = a.lpChar (b.lpChar c) ∧ (WD.lpZero h).lpChar c = WD.lpZero h ∧ (c.unr → c.lpDim = 1 → c.frobEig = {1} → a.lpChar c = a) := by
  first | exact @GlobalTheory.WeilDeligne.lpChar_laws_closed | exact GlobalTheory.WeilDeligne.lpChar_laws_closed | (intros; apply GlobalTheory.WeilDeligne.lpChar_laws_closed <;> assumption)
