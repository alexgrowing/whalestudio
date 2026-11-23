import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RiemannLatticeEigenProjectionStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.QuotientLatticeByIsotropicSubmoduleStatement
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

namespace GlobalTheory.CompanionTheory.Ar.QuotUniv

theorem hermitian_transport_along_orthogonal_complement :
    ∀ (g g' : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ), Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm *ᵥ star z).re) → ∀ (S : Submodule ℂ (Fin g → ℂ)) (q : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)), Function.Surjective q → LinearMap.ker q = S → (∀ z : Fin g → ℂ, ∃ s ∈ S, ∀ v ∈ S, (z - s) ⬝ᵥ Hm *ᵥ star v = 0) → ∃ Hm' : Matrix (Fin g') (Fin g') ℂ, Hm'.IsHermitian ∧ (∀ z : Fin g' → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm' *ᵥ star z).re) ∧ ∀ x y : Fin g → ℂ, (∀ v ∈ S, x ⬝ᵥ Hm *ᵥ star v = 0) → q y ⬝ᵥ Hm' *ᵥ star (q x) = y ⬝ᵥ Hm *ᵥ star x := by
  intro g g' Hm hHm hpos S q hq hker hproj
  have hconj : ∀ x y : Fin g → ℂ, star (x ⬝ᵥ Hm *ᵥ star y) = y ⬝ᵥ Hm *ᵥ star x := by
    intro x y
    rw [← Matrix.star_dotProduct_star, Matrix.star_mulVec, star_star, hHm.eq,
      ← Matrix.dotProduct_mulVec]
  have hmemS : ∀ z, q z = 0 → z ∈ S := fun z hz => by
    rw [← hker]
    exact LinearMap.mem_ker.2 hz
  choose z hz using fun i : Fin g' => hq (Pi.single i 1)
  choose s hsS hs using fun i => hproj (z i)
  let A : Matrix (Fin g') (Fin g) ℂ := Matrix.of fun i => z i - s i
  have hAq : ∀ i, q (z i - s i) = Pi.single i 1 := by
    intro i
    have hs0 : q (s i) = 0 := by
      have : s i ∈ LinearMap.ker q := by rw [hker]; exact hsS i
      exact LinearMap.mem_ker.1 this
    rw [map_sub, hz i, hs0, sub_zero]
  have hT : ∀ u : Fin g' → ℂ, Matrix.vecMul u A = ∑ i, u i • (z i - s i) := by
    intro u
    ext a
    simp [A, Matrix.vecMul, dotProduct, Finset.sum_apply]
  have hTq : ∀ u, q (Matrix.vecMul u A) = u := by
    intro u
    rw [hT, map_sum]
    simp_rw [map_smul, hAq]
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  have hTorth : ∀ u, ∀ v ∈ S, Matrix.vecMul u A ⬝ᵥ Hm *ᵥ star v = 0 := by
    intro u v hv
    rw [hT, sum_dotProduct]
    exact Finset.sum_eq_zero fun i _ => by rw [smul_dotProduct, hs i v hv, smul_zero]
  have hkey : ∀ u u' : Fin g' → ℂ, u ⬝ᵥ (A * Hm * A.conjTranspose) *ᵥ star u' =
      Matrix.vecMul u A ⬝ᵥ Hm *ᵥ star (Matrix.vecMul u' A) := by
    intro u u'
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec u A,
      Matrix.star_vecMul]
  have hlift : ∀ x : Fin g → ℂ, (∀ v ∈ S, x ⬝ᵥ Hm *ᵥ star v = 0) →
      Matrix.vecMul (q x) A = x := by
    intro x hx
    have hdS : Matrix.vecMul (q x) A - x ∈ S := hmemS _ (by rw [map_sub, hTq, sub_self])
    have hd0 : (Matrix.vecMul (q x) A - x) ⬝ᵥ Hm *ᵥ star (Matrix.vecMul (q x) A - x) = 0 := by
      rw [sub_dotProduct, hTorth _ _ hdS, hx _ hdS, sub_zero]
    by_contra hne
    have := hpos _ (sub_ne_zero.2 hne)
    rw [hd0, Complex.zero_re] at this
    exact lt_irrefl _ this
  refine ⟨A * Hm * A.conjTranspose, Matrix.isHermitian_mul_mul_conjTranspose A hHm, ?_, ?_⟩
  · intro u hu
    rw [hkey]
    apply hpos
    intro h0
    apply hu
    rw [← hTq u, h0, map_zero]
  · intro x y hx
    rw [hkey, hlift x hx, ← sub_eq_zero, ← sub_dotProduct, ← hconj,
      hx (Matrix.vecMul (q y) A - y) (hmemS _ (by rw [map_sub, hTq, sub_self])), star_zero]

end GlobalTheory.CompanionTheory.Ar.QuotUniv
