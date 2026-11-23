import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSatakeParameterSphericalUnramifiedUnitary
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_satake_parameter_spherical_unramifiedUnitary : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (ϖ : w.adicCompletion E) (σ : w.adicCompletion E →+* w.adicCompletion E) (q n : ℕ), IsUnramInv ϖ σ q → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GU σ n) V), ρ.IsIrreducible → IsAdmissible ρ → GlobalTheory.LGrp.IsSpherical ρ (KU σ n) → ∃ α, HasSatU ϖ q ρ α := by
  first | exact @GlobalTheory.LFun.ExSatU.exists_hasSatU | exact GlobalTheory.LFun.ExSatU.exists_hasSatU | (intros; apply GlobalTheory.LFun.ExSatU.exists_hasSatU <;> assumption)
