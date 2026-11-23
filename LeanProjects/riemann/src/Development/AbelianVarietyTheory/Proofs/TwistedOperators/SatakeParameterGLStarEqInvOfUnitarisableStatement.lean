import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SatakeParameterGLStarEqInvOfUnitarisable
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.satakeParameterGL_star_eq_inv_of_unitarisable : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V) (x : V) (B : Multiset ℂˣ), GlobalTheory.LGrp.IsUnitarisable ρ → IsSatVecGL w ρ x B → B.map star = B.map (·⁻¹) := by
  first | exact @GlobalTheory.LFun.UnitaryParam.map_star_eq_map_inv | exact GlobalTheory.LFun.UnitaryParam.map_star_eq_map_inv | (intros; apply GlobalTheory.LFun.UnitaryParam.map_star_eq_map_inv <;> assumption)
