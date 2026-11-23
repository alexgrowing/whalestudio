import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPowEqPowOfWeilDegreeEqSmooth
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MonodromyZeroOfWeilDeligneRepClassIff
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module GlobalTheory.WeilDeligne
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pow_eq_pow_of_weilDegree_eq_smooth : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ (Weil h) V), IsSmooth ρ → ∀ σ τ : Weil h, deg σ = deg τ → ∃ m : ℕ, 0 < m ∧ ρ σ ^ m = ρ τ ^ m := by
  first | exact @GlobalTheory.WeilDeligne.exists_pow_eq_pow_of_deg_eq | exact GlobalTheory.WeilDeligne.exists_pow_eq_pow_of_deg_eq | (intros; apply GlobalTheory.WeilDeligne.exists_pow_eq_pow_of_deg_eq <;> assumption)
