import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Imports
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BasisMatrixMapCancelLeftStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormBreuilKisinHomUniformizerFrobeniusLeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinTwoHomsERegularAssociatedStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.Height

theorem mem_nonZeroDivisors_of_associated' {R : Type} [CommRing R] {a b : R} (h : Associated a b)
    (ha : a ∈ nonZeroDivisors R) : b ∈ nonZeroDivisors R := by
  obtain ⟨v, rfl⟩ := h
  exact mul_mem_nonZeroDivisors.mpr ⟨ha, v.isUnit.mem_nonZeroDivisors⟩

theorem mul_cancel_of_rel {R : Type} [CommRing R] {n : Type} [Fintype n] {N : ℕ} {ef eg eh : R}
    (hg : eg ∈ nonZeroDivisors R) (hh : eh ∈ nonZeroDivisors R) {Pf Pg Ph ε₁ ε₂ ε₃ : Matrix n n R}
    (r1 : eg ^ N • (Pf * ε₁) = ef ^ N • Pg) (r2 : eh ^ N • (Pg * ε₂) = eg ^ N • Ph)
    (r3 : eh ^ N • (Pf * ε₃) = ef ^ N • Ph) : Pf * (ε₁ * ε₂) = Pf * ε₃ := by
  have key : (eg ^ N * eh ^ N) • (Pf * (ε₁ * ε₂)) = (eg ^ N * eh ^ N) • (Pf * ε₃) := by
    calc (eg ^ N * eh ^ N) • (Pf * (ε₁ * ε₂))
        = eh ^ N • ((eg ^ N • (Pf * ε₁)) * ε₂) := by
          rw [Matrix.smul_mul, smul_smul, Matrix.mul_assoc, mul_comm]
      _ = eh ^ N • ((ef ^ N • Pg) * ε₂) := by rw [r1]
      _ = ef ^ N • (eh ^ N • (Pg * ε₂)) := by
          rw [Matrix.smul_mul, smul_smul, smul_smul, mul_comm]
      _ = ef ^ N • (eg ^ N • Ph) := by rw [r2]
      _ = eg ^ N • (ef ^ N • Ph) := by rw [smul_smul, smul_smul, mul_comm]
      _ = eg ^ N • (eh ^ N • (Pf * ε₃)) := by rw [r3]
      _ = (eg ^ N * eh ^ N) • (Pf * ε₃) := by rw [smul_smul]
  have hc : eg ^ N * eh ^ N ∈ nonZeroDivisors R :=
    mul_mem_nonZeroDivisors.mpr ⟨pow_mem hg _, pow_mem hh _⟩
  ext i j
  have e := congrFun (congrFun key i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at e
  exact (mul_cancel_left_mem_nonZeroDivisors hc).mp e

theorem rel_mul : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s) (B : Obj l ↥(OL K)) (f₀ : Hom bk.prism B), toDisc l (BK.hf f₀ X) bk.ρ₀ (BK.hf f₀ bk.E) ∈ nonZeroDivisors (Disc l (BK.hf f₀ X) bk.ρ₀) → ∀ (f g h : Hom bk.prism B) (ε₁ ε₂ ε₃ : Matrix (Fin d) (Fin d) (Disc l (BK.hf f₀ X) bk.ρ₀)), ht.Rel (BK.hf f₀ X) f g ε₁ → ht.Rel (BK.hf f₀ X) g h ε₂ → ht.Rel (BK.hf f₀ X) f h ε₃ → ε₁ * ε₂ = ε₃ := by
  intro l _ K bk d ρ τ s ht B f₀ h0 f g h ε₁ ε₂ ε₃ h1 h2 h3
  have hn : ∀ k : Hom bk.prism B, ‖toDisc l (BK.hf f₀ X) bk.ρ₀ (BK.hf k X)‖ ≤ bk.ρ₀ := fun k =>
    (GlobalTheory.T.norm_breuilKisinHom_uniformizer_frobenius_le l K bk B f₀ k).1
  have hE : ∀ k : Hom bk.prism B,
      toDisc l (BK.hf f₀ X) bk.ρ₀ (BK.hf k bk.E) ∈ nonZeroDivisors (Disc l (BK.hf f₀ X) bk.ρ₀) := fun k =>
    mem_nonZeroDivisors_of_associated' ((GlobalTheory.T.breuilKisin_two_homs_E_regular_associated l K bk B f₀ k).2.1.map (toDisc l (BK.hf f₀ X) bk.ρ₀)) h0
  have mf := isDiscMap_map (BK.hf f) (hn f)
  have mg := isDiscMap_map (BK.hf g) (hn g)
  have mh := isDiscMap_map (BK.hf h) (hn h)
  have hF : Disc.map (BK.hf f) (hn f) (toDisc l (X : bk.S) bk.ρ₀ bk.E) ∈
      nonZeroDivisors (Disc l (BK.hf f₀ X) bk.ρ₀) := by
    rw [mf.ext]; exact hE f
  exact GlobalTheory.T.basis_matrix_map_cancel_left l K bk d ρ τ s ht (Disc l (BK.hf f₀ X) bk.ρ₀) _ hF _ _
    (mul_cancel_of_rel (hE g) (hE h) (h1 _ _ mf mg) (h2 _ _ mg mh) (h3 _ _ mf mh))

end GlobalTheory.BSP.Height
