import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LastColsVal
open MeasureTheory GlobalTheory.SplitFlip ValuativeRel
open scoped Matrix
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

noncomputable section

namespace GlobalTheory.FullRankCoinv.UnitMinor

theorem det_one_updateCol_eq {K : Type} [Field K] {n : ℕ} (i : Fin n) (c : Fin n → K) :
    ((1 : Matrix (Fin n) (Fin n) K).updateCol i c).det = c i := by
  rw [← Matrix.cramer_apply, Matrix.cramer_one]; rfl

theorem exists_minor_det_ne_zero {K : Type} [Field K] {n d : ℕ} (Y : Matrix (Fin n) (Fin d) K)
    (hY : Y.rank = n) : ∃ f : Fin n ↪ Fin d, (Y.submatrix id f).det ≠ 0 := by
  classical
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' K (fun j => Yᵀ j)
  have htop : Submodule.span K (Set.range (fun j => Yᵀ j)) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [Module.finrank_fin_fun]; rw [Matrix.rank_eq_finrank_span_cols] at hY; exact hY
  have hsp : ⊤ ≤ Submodule.span K (Set.range ((fun j => Yᵀ j) ∘ a)) := by rw [hspan, htop]
  let b := Module.Basis.mk hli hsp
  let e : κ ≃ Fin n := b.indexEquiv (Pi.basisFun K (Fin n))
  let f : Fin n ↪ Fin d := e.symm.toEmbedding.trans ⟨a, ha⟩
  refine ⟨f, ?_⟩
  have hli' : LinearIndependent K (fun i => (Y.submatrix id f)ᵀ i) := by
    have : (fun i => (Y.submatrix id f)ᵀ i) = ((fun j => Yᵀ j) ∘ a) ∘ e.symm := by
      funext i r; rfl
    rw [this]; exact hli.comp _ e.symm.injective
  have hu := Matrix.linearIndependent_cols_iff_isUnit.mp hli'
  exact ((Matrix.isUnit_iff_isUnit_det _).mp hu).ne_zero

theorem submatrix_mul_left {K : Type} [Field K] {n d : ℕ} (B : Matrix (Fin n) (Fin n) K)
    (Y : Matrix (Fin n) (Fin d) K) (g : Fin n ↪ Fin d) :
    (B * Y).submatrix id g = B * Y.submatrix id g := by
  ext r s; simp [Matrix.mul_apply]

theorem exists_GL_mul_mem_unitMinorSet (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n d : ℕ) (Y : Matrix (Fin n) (Fin d) k) (hY : Y.rank = n) :
    ∃ E : GL (Fin n) k, E.val * Y ∈ unitMinorSet k n d := by
  classical
  obtain ⟨f0, hf0⟩ := exists_minor_det_ne_zero Y hY
  haveI : Nonempty (Fin n ↪ Fin d) := ⟨f0⟩
  obtain ⟨f, hf⟩ := Finite.exists_max (fun g : Fin n ↪ Fin d => valuation k (Y.submatrix id g).det)
  have hAdet : (Y.submatrix id f).det ≠ 0 := by
    intro h0
    have h1 := hf f0
    simp only [h0, map_zero] at h1
    exact hf0 ((map_eq_zero _).mp (le_antisymm h1 zero_le'))
  have hAu : IsUnit (Y.submatrix id f).det := isUnit_iff_ne_zero.mpr hAdet
  let E : GL (Fin n) k := Matrix.GeneralLinearGroup.mkOfDetNeZero (Y.submatrix id f)⁻¹
    (by rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']; exact inv_ne_zero hAdet)
  have hEv : E.val = (Y.submatrix id f)⁻¹ := rfl
  set Z := E.val * Y with hZ
  have hZf : Z.submatrix id f = 1 := by
    rw [hZ, submatrix_mul_left, hEv, Matrix.nonsing_inv_mul _ hAu]
  have hZg : ∀ g : Fin n ↪ Fin d, valuation k (Z.submatrix id g).det ≤ 1 := by
    intro g
    rw [hZ, submatrix_mul_left, hEv, Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv',
      map_mul, map_inv₀, inv_mul_le_one₀ (zero_lt_iff.mpr (by simpa using hAdet))]
    exact hf g
  refine ⟨E, fun i j => ?_, f, by rw [hZf, Matrix.det_one, map_one]⟩
  rw [Valuation.mem_integer_iff]
  show valuation k (Z i j) ≤ 1
  by_cases hj : ∃ i', f i' = j
  · obtain ⟨i', rfl⟩ := hj
    have := congrFun (congrFun hZf i) i'
    simp only [Matrix.submatrix_apply, id] at this
    rw [this, Matrix.one_apply]
    split_ifs <;> simp
  · push_neg at hj
    have hsub : Z.submatrix id (f.setValue i j) = (1 : Matrix (Fin n) (Fin n) k).updateCol i (fun r => Z r j) := by
      ext r s
      by_cases hs : s = i
      · subst hs; simp [Function.Embedding.setValue_eq]
      · rw [Matrix.updateCol_ne hs]
        have h2 : f.setValue i j s = f s := by
          simp [Function.Embedding.setValue, hs, hj s]
        simp only [Matrix.submatrix_apply, id, h2]
        exact congrFun (congrFun hZf r) s
    have := hZg (f.setValue i j)
    rwa [hsub, det_one_updateCol_eq] at this

end GlobalTheory.FullRankCoinv.UnitMinor
