import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.HighestVectorsRegularLine
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WtRInjective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CPoly
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualWeightSpacesSpanStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorCharInjective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeightPolynomialTraceIdentityStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DominanceOfWeylCharacterCoeffStatement

noncomputable section
open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCountG GlobalTheory.CompanionTheory.RealCount.Tope

namespace GlobalTheory.CompanionTheory.RealCountG.TopeG

theorem cPoly_coeff {n : ℕ} (s : Finset (Fin n → ℤ)) (c : (Fin n → ℤ) → ℂ) (μ : Fin n → ℤ) :
    (cPoly s c).coeff μ = if μ ∈ s then c μ else 0 := by
  classical
  unfold cPoly
  rw [AddMonoidAlgebra.coeff_sum, Finsupp.finset_sum_apply]
  simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  rw [Finset.sum_ite_eq']

theorem trOn_dualT_id {n : ℕ} (E : KMod n) (S : Submodule ℂ (E.V →L[ℂ] ℂ)) :
    trOn S (dualT E 1 : (E.V →L[ℂ] ℂ) →ₗ[ℂ] (E.V →L[ℂ] ℂ)) = Module.finrank ℂ S := by
  have h1 : (dualT E 1 : (E.V →L[ℂ] ℂ) →ₗ[ℂ] (E.V →L[ℂ] ℂ)) = LinearMap.id := by
    ext ξ v
    simp [dualT]
  rw [h1]
  unfold trOn
  rw [dif_pos (fun x hx => by simpa using hx)]
  have h2 : (LinearMap.id : (E.V →L[ℂ] ℂ) →ₗ[ℂ] (E.V →L[ℂ] ℂ)).restrict (fun x (hx : x ∈ S) => hx) = LinearMap.id := by
    ext x; rfl
  rw [h2, LinearMap.trace_id]

theorem topeG : ∀ {n : ℕ} (lam : Fin n → ℤ), Antitone lam → ∀ (E : KMod n) (T : E.V →L[ℂ] E.V), IsLefK lam E T →
    (⨆ μ, wtDual E μ) = ⊤ ∧ ∀ μ, wtDual E μ ≠ ⊥ → DomLE (wtR μ) (m0 lam) := by
  intro n lam hlam E T hT
  have hspan := GlobalTheory.T.dual_weight_spaces_span E
  have hind := GlobalTheory.CompanionTheory.RealCount.Tope.wtDual_iSupIndep E
  have hfin : Set.Finite {μ | wtDual E μ ≠ ⊥} := WellFoundedGT.finite_ne_bot_of_iSupIndep hind
  set s := hfin.toFinset with hs
  have hmem : ∀ μ, wtDual E μ ≠ ⊥ → μ ∈ s := fun μ h => by simpa [hs] using h
  obtain ⟨h1, -⟩ := GlobalTheory.T.weight_polynomial_trace_identity lam E T hT hspan hind s hmem
  refine ⟨hspan, fun μ hμ => GlobalTheory.T.dominance_of_weyl_character_coeff lam hlam _ h1 μ ?_⟩
  rw [cPoly_coeff, if_pos (hmem μ hμ), trOn_dualT_id]
  have : Module.finrank ℂ (wtDual E μ) ≠ 0 := fun h0 => hμ (Submodule.finrank_eq_zero.1 h0)
  exact_mod_cast this

end GlobalTheory.CompanionTheory.RealCountG.TopeG
