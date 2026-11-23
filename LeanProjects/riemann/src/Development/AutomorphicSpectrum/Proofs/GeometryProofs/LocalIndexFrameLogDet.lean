import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PlaceEqOneOfNotMem
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RelIndexMulVec
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StandardRankOneLatticeOfLocal
open NumberField Matrix IsDedekindDomain GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame

namespace GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame

variable {L : Type} [Field L] [NumberField L] {n : ℕ}

theorem place_eq_zpow_ordE (v : FinitePlace L) {x : L} (hx : x ≠ 0) :
    v x = ((Ideal.absNorm v.maximalIdeal.asIdeal : ℕ) : ℝ) ^ (-Formalism.L2.Ker.ordE v.maximalIdeal x) := by
  have hw : IsDedekindDomain.HeightOneSpectrum.valuation L v.maximalIdeal x ≠ 0 := by
    rwa [ne_eq, Valuation.zero_iff]
  rw [← NumberField.FinitePlace.norm_embedding_eq, NumberField.FinitePlace.norm_embedding,
    NumberField.HeightOneSpectrum.adicAbv_def]
  unfold Formalism.L2.Ker.ordE
  rw [neg_neg]
  obtain ⟨k, hk⟩ : ∃ k : ℤ, IsDedekindDomain.HeightOneSpectrum.valuation L v.maximalIdeal x = WithZero.exp k :=
    ⟨_, (WithZero.exp_log hw).symm⟩
  rw [hk, WithZero.log_exp, WithZeroMulInt.toNNReal_neg_apply _ (WithZero.exp_ne_zero)]
  simp [WithZero.exp]

theorem relIndex_map_of_integral (v : FinitePlace L) (S : Matrix (Fin n) (Fin n) L)
    (hS : ∀ i j, v (S i j) ≤ 1) (hdet : S.det ≠ 0) (f : (Fin n → L) →+ (Fin n → L))
    (hf : ∀ x, f x = S *ᵥ x) (Λ : AddSubgroup (Fin n → L)) (hΛ : ∀ x, x ∈ Λ ↔ ∀ i, v (x i) ≤ 1) :
    Λ.map f ≤ Λ ∧ (((Λ.map f).relIndex Λ : ℕ) : ℝ) = (v S.det)⁻¹ := by
  have hint : ∀ a : L, v a ≤ 1 ↔ Formalism.L2.Col.IntAt v.maximalIdeal a := fun a => by
    rw [place_le_one_iff, GlobalTheory.CharValCompare.intAt_iff]
  have hle : Λ.map f ≤ Λ := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := AddSubgroup.mem_map.mp hz
    rw [hΛ] at hy ⊢
    intro i
    rw [hf]
    show v (∑ j, S i j * y j) ≤ 1
    exact place_sum_le_one v _ _ (fun j _ => place_mul_le_one v (hS i j) (hy j))
  refine ⟨hle, ?_⟩
  have key := GlobalTheory.IdxDet.relIndex_mulVec L (Fin n) v.maximalIdeal S Λ (Λ.map f) hdet
    (fun x => by rw [hΛ]; exact forall_congr' fun i => hint (x i))
    (fun x => by
      rw [AddSubgroup.mem_map]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y, hy, hf y⟩
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y, hy, hf y⟩)
    hle
  rw [place_eq_zpow_ordE v hdet, _root_.zpow_neg, inv_inv]
  have key' := congrArg (fun q : ℚ => (q : ℝ)) key
  push_cast at key'
  exact key'

theorem gIdx_locAt_frame (L : Type) [Field L] [NumberField L] (n : ℕ) (v : FinitePlace L)
    (T : Matrix (Fin n) (Fin n) L) (hdet : T.det ≠ 0) :
    gIdx (locAt v (frame T)).toAddSubgroup
      (locAt v (frame (1 : Matrix (Fin n) (Fin n) L))).toAddSubgroup = Real.log (v T.det) := by
  set Λ := (locAt v (frame (1 : Matrix (Fin n) (Fin n) L))).toAddSubgroup with hΛdef
  have hΛ : ∀ x, x ∈ Λ ↔ ∀ i, v (x i) ≤ 1 := fun x => mem_locAt_frame_one
  obtain ⟨M, hM⟩ : ∃ M : (Fin n → L) →+ (Fin n → L), ∀ x, M x = T *ᵥ x :=
    ⟨(Matrix.mulVecLin T).toAddMonoidHom, fun x => rfl⟩
  have hTΛ : (locAt v (frame T)).toAddSubgroup = Λ.map M := by
    ext x
    rw [Submodule.mem_toAddSubgroup, mem_locAt_frame, AddSubgroup.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, (hΛ y).2 hy, hM y⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, (hΛ y).1 hy, hM y⟩
  have hMinj : Function.Injective M := by
    intro x y hxy
    rw [hM, hM] at hxy
    have h := congrArg (fun z => T⁻¹ *ᵥ z) hxy
    simpa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul T (isUnit_iff_ne_zero.mpr hdet)] using h
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (NumberField.RingOfIntegers L))
    (Finset.univ : Finset (Fin n × Fin n)) (fun p => T p.1 p.2)
  set c : L := algebraMap (NumberField.RingOfIntegers L) L b with hcdef
  have hc0 : c ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2
  have hcv : v c ≤ 1 := place_int_le_one v b
  have hcT : ∀ i j, v ((c • T) i j) ≤ 1 := by
    intro i j
    obtain ⟨r, hr⟩ := hb (i, j) (Finset.mem_univ _)
    rw [Matrix.smul_apply]
    have : c • T i j = algebraMap (NumberField.RingOfIntegers L) L r := by
      rw [hr, smul_eq_mul, Algebra.smul_def]
      all_goals rfl
    rw [this]
    exact place_int_le_one v r
  have hcI : ∀ i j, v ((c • (1 : Matrix (Fin n) (Fin n) L)) i j) ≤ 1 := by
    intro i j
    rw [Matrix.smul_apply, Matrix.one_apply]
    split_ifs
    · simpa using hcv
    · simpa using place_int_le_one v 0
  obtain ⟨a, ha⟩ : ∃ a : (Fin n → L) →+ (Fin n → L), ∀ x, a x = c • x :=
    ⟨DistribSMul.toAddMonoidHom _ c, fun x => rfl⟩
  have hdetI : (c • (1 : Matrix (Fin n) (Fin n) L)).det = c ^ n := by
    rw [Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one]
  have hdetT : (c • T).det = c ^ n * T.det := by
    rw [Matrix.det_smul, Fintype.card_fin]
  have hcn : c ^ n ≠ 0 := pow_ne_zero _ hc0
  have h1 := relIndex_map_of_integral v (c • (1 : Matrix (Fin n) (Fin n) L)) hcI
    (by rw [hdetI]; exact hcn) a (fun x => by rw [ha]; ext i; simp [Matrix.mulVec, dotProduct, Matrix.one_apply]) Λ hΛ
  have h2 := relIndex_map_of_integral v (c • T) hcT (by rw [hdetT]; exact mul_ne_zero hcn hdet) (a.comp M)
    (fun x => by
      rw [AddMonoidHom.comp_apply, ha, hM]
      ext i
      simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]) Λ hΛ
  have hpos : ∀ y : L, y ≠ 0 → 0 < v y := fun y hy => NumberField.FinitePlace.pos_iff.mpr hy
  have hr1 : (Λ.map a).relIndex Λ ≠ 0 := by
    intro h0
    have := h1.2
    rw [h0, Nat.cast_zero, hdetI] at this
    exact (inv_pos.mpr (hpos _ hcn)).ne' this.symm
  have hr2 : (Λ.map (a.comp M)).relIndex Λ ≠ 0 := by
    intro h0
    have := h2.2
    rw [h0, Nat.cast_zero, hdetT] at this
    exact (inv_pos.mpr (hpos _ (mul_ne_zero hcn hdet))).ne' this.symm
  rw [hTΛ, gIdx_frac Λ M a hMinj (fun x => by rw [ha, hM, hM, ha, Matrix.mulVec_smul]) h1.1 hr1 h2.1 hr2,
    h1.2, h2.2, hdetI, hdetT, Real.log_inv, Real.log_inv]
  have hm : v (c ^ n * T.det) = v (c ^ n) * v T.det := by
    rw [NumberField.FinitePlace.coe_apply, NumberField.FinitePlace.coe_apply,
      NumberField.FinitePlace.coe_apply, map_mul]
  rw [hm, Real.log_mul (hpos _ hcn).ne' (hpos _ hdet).ne']
  ring

end GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame
