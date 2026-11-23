import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TemperedOfLpDimLeOneOfUnitEigenvalues
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MonodromyZeroOfWeilDeligneRepClassIff
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tempered_of_lpDim_le_one_of_unit_eigenvalues : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (a : WD h), a.lpDim ≤ 1 → (∀ φ : Weil h, deg φ = 1 → ∀ α ∈ a.eig φ, ‖α‖ = 1) → a.tempered := by
  first | exact @GlobalTheory.WeilDeligne.WD.tempered_of_lpDim_le_one_of_norm_eig | exact GlobalTheory.WeilDeligne.WD.tempered_of_lpDim_le_one_of_norm_eig | (intros; apply GlobalTheory.WeilDeligne.WD.tempered_of_lpDim_le_one_of_norm_eig <;> assumption)
