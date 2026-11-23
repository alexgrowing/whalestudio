import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SatakeParameterOfSpherical
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.satake_parameter_of_spherical : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V), GlobalTheory.LGrp.IsSpherical ρ (KGL w n) → (∀ h ∈ Hecke ℂ (KGL w n), ∃ c : ℂ, ∀ x ∈ fixed ρ (KGL w n), heckeVec ρ (KGL w n) h x = c • x) → ∃ B, HasSatGL w ρ B := by
  first | exact @GlobalTheory.LFun.ExSatGL.exists_hasSatGL | exact GlobalTheory.LFun.ExSatGL.exists_hasSatGL | (intros; apply GlobalTheory.LFun.ExSatGL.exists_hasSatGL <;> assumption)
