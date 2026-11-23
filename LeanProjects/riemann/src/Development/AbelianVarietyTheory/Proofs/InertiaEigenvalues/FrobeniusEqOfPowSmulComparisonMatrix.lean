import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Imports
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemBallOfGaugeLt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComparisonMatrixFrobeniusDiscStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormBreuilKisinHomUniformizerFrobeniusLeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TopBasisDiscRegularStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section
namespace GlobalTheory.BSP.Height
private theorem matrix_map_smul {R S : Type*} [CommRing R] [CommRing S] {d : ℕ} (F : R →+* S) (c : R)
    (M : Matrix (Fin d) (Fin d) R) : (c • M).map F = F c • M.map F := by
  ext i j; simp

private theorem frobenius_height_matrix_relation {R D : Type*} [CommRing R] [CommRing D] {d : ℕ} (t : R →+* D)
    (ht : Function.Injective t) (φ : R →+* R) (Φ : D →+* D) (hΦ : ∀ a, Φ (t a) = t (φ a)) (n k m : ℕ) (a b : R)
    (Af Ag x : Matrix (Fin d) (Fin d) R) (ε : Matrix (Fin d) (Fin d) D) (hx : x.map t = (n : D) ^ k • ε)
    (key : t b ^ m • (Af.map t * ε.map Φ) = t a ^ m • (ε * Ag.map t)) :
    b ^ m • (Af * x.map φ) = a ^ m • (x * Ag) := by
  have hxφ : (x.map φ).map t = (n : D) ^ k • ε.map Φ := by
    have h1 : (x.map φ).map t = (x.map t).map Φ := by
      ext i j; simp only [Matrix.map_apply]; exact (hΦ (x i j)).symm
    rw [h1, hx]; ext i j; simp
  apply Matrix.map_injective ht
  simp only [Matrix.map_mul, matrix_map_smul, map_pow]
  rw [hxφ, hx, Matrix.mul_smul, Matrix.smul_mul, smul_comm _ ((n : D) ^ k), smul_comm _ ((n : D) ^ k), key]

theorem phi_eq_of_rel_pow : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s), bk.IsPer τ → ∀ (B : Obj l ↥(OL K)) (f g : Hom bk.prism B) (ι : Type), TopBasis (BK.hf f) bk.J ι → ∀ (k : ℕ) (x : Matrix (Fin d) (Fin d) B.A) (ε : Matrix (Fin d) (Fin d) (Disc l (BK.hf f X) bk.ρ₀)), ht.Rel (BK.hf f X) f g ε → x.map (toDisc l (BK.hf f X) bk.ρ₀) = ((l : ℕ) : Disc l (BK.hf f X) bk.ρ₀) ^ k • ε → BK.hf g bk.E ^ (ht.a + s.N) • (ht.A.map (BK.hf f) * x.map B.D.φ) = BK.hf f bk.E ^ (ht.a + s.N) • (x * ht.A.map (BK.hf g)) := by
  intro l _ K bk d ρ τ s ht hper B f g ι hb k x ε hrel hx
  obtain ⟨hinj, hE, -, -⟩ := GlobalTheory.T.toDisc_injective_and_nonZeroDivisors_of_topBasis l K bk B.A (BK.hf f) ι hb
  have hφ : ‖toDisc l (BK.hf f X) bk.ρ₀ (B.D.φ (BK.hf f X))‖ ≤ bk.ρ₀ := (GlobalTheory.T.norm_breuilKisinHom_uniformizer_frobenius_le l K bk B f f).2
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : Disc l (BK.hf f X) bk.ρ₀ →+* Disc l (BK.hf f X) bk.ρ₀, IsDiscMap B.D.φ Φ :=
    ⟨_, isDiscMap_map B.D.φ hφ⟩
  exact frobenius_height_matrix_relation _ hinj B.D.φ Φ hΦ.ext l k _ _ _ _ _ x ε hx
    (GlobalTheory.T.comparisonMatrix_frobenius_disc l K bk d ρ τ s ht hper B f hE f g ε hrel Φ hΦ)

end GlobalTheory.BSP.Height
