import Mathlib
import ReciprocityTheory.DualLattices.NearIdentityColengthStatement

namespace ReciprocityTheory.PGsh

open Matrix

section

variable {K : Type} [Field K] (v : Valuation K NNReal) {ι : Type} [Fintype ι] [DecidableEq ι]

def IsIntegralMat (U : Matrix ι ι K) : Prop := ∀ i j, v (U i j) ≤ 1

def IsIntegralVec (c : ι → K) : Prop := ∀ j, v (c j) ≤ 1

variable {v}

theorem IsIntegralMat.det_le_one {U : Matrix ι ι K} (hU : IsIntegralMat v U) : v U.det ≤ 1 := by
  rw [Matrix.det_apply']
  refine v.map_sum_le fun σ _ => ?_
  rw [map_mul, map_prod]
  have hs : v ((Equiv.Perm.sign σ : ℤ) : K) = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> rw [h] <;> simp
  rw [hs, one_mul]
  exact Finset.prod_le_one (fun _ _ => zero_le) fun i _ => hU _ _

private theorem nnreal_mul_le_one {a b : NNReal} (ha : a ≤ 1) (hb : b ≤ 1) : a * b ≤ 1 := by
  simpa using mul_le_mul ha hb (zero_le) zero_le_one

theorem IsIntegralMat.mulVec {U : Matrix ι ι K} {c : ι → K} (hU : IsIntegralMat v U)
    (hc : IsIntegralVec v c) : IsIntegralVec v (U *ᵥ c) := by
  intro i
  show v (∑ j, U i j * c j) ≤ 1
  exact v.map_sum_le fun j _ => by rw [map_mul]; exact _root_.ReciprocityTheory.PGsh.nnreal_mul_le_one (hU i j) (hc j)

theorem IsIntegralMat.mul {U V : Matrix ι ι K} (hU : IsIntegralMat v U)
    (hV : IsIntegralMat v V) : IsIntegralMat v (U * V) := by
  intro i j
  rw [Matrix.mul_apply]
  exact v.map_sum_le fun k _ => by rw [map_mul]; exact _root_.ReciprocityTheory.PGsh.nnreal_mul_le_one (hU i k) (hV k j)

theorem isIntegralVec_single (j : ι) : IsIntegralVec v (Pi.single j (1 : K)) := by
  intro k
  by_cases hk : k = j
  · subst hk; simp
  · simp [hk]

end

structure Lat {K : Type} [Field K] (v : Valuation K NNReal) (ι : Type) [Fintype ι]
    [DecidableEq ι] where

  B : Matrix ι ι K
  det_ne : B.det ≠ 0

namespace Lat

variable {K : Type} [Field K] {v : Valuation K NNReal} {ι : Type} [Fintype ι] [DecidableEq ι]

def pts (L : Lat v ι) : Set (ι → K) := {x | ∃ c, IsIntegralVec v c ∧ x = L.B *ᵥ c}

def std (v : Valuation K NNReal) (ι : Type) [Fintype ι] [DecidableEq ι] : Lat v ι :=
  ⟨1, by simp⟩

def mulRight (L : Lat v ι) (U : Matrix ι ι K) (hU : U.det ≠ 0) : Lat v ι :=
  ⟨L.B * U, by rw [Matrix.det_mul]; exact mul_ne_zero L.det_ne hU⟩

theorem isUnit_det (L : Lat v ι) : IsUnit L.B.det :=
  isUnit_iff_ne_zero.mpr L.det_ne

theorem pts_subset_iff (L' L : Lat v ι) :
    L'.pts ⊆ L.pts ↔ IsIntegralMat v (L.B⁻¹ * L'.B) := by
  constructor
  · intro h i j
    obtain ⟨c, hc, hx⟩ := h ⟨Pi.single j 1, ReciprocityTheory.PGsh.isIntegralVec_single j, rfl⟩
    have hM : (L.B⁻¹ * L'.B) *ᵥ Pi.single j 1 = c := by
      rw [← Matrix.mulVec_mulVec, hx, Matrix.mulVec_mulVec,
        Matrix.nonsing_inv_mul _ (isUnit_det L), Matrix.one_mulVec]
    have e := congrFun hM i
    simp [Matrix.mulVec, dotProduct, Pi.single_apply] at e
    rw [e]
    exact hc i
  · intro hM x ⟨c, hc, hx⟩
    refine ⟨(L.B⁻¹ * L'.B) *ᵥ c, hM.mulVec hc, ?_⟩
    rw [hx, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_det L),
      Matrix.one_mul]

theorem v_det_eq_one_of_integral {U V : Matrix ι ι K} (hU : IsIntegralMat v U)
    (hV : IsIntegralMat v V) (hUV : U * V = 1) : v U.det = 1 := by
  refine le_antisymm hU.det_le_one ?_
  calc (1 : NNReal) = v U.det * v V.det := by
        rw [← map_mul, ← Matrix.det_mul, hUV, Matrix.det_one, map_one]
    _ ≤ v U.det * 1 := mul_le_mul_of_nonneg_left hV.det_le_one (zero_le)
    _ = v U.det := mul_one _

private theorem valuation_lat_det_ne_zero (L : ReciprocityTheory.PGsh.Lat v ι) : v L.B.det ≠ 0 :=
  (Valuation.ne_zero_iff v).mpr L.det_ne

private theorem valuation_det_inv_mul_eq_div (L' L : ReciprocityTheory.PGsh.Lat v ι) :
    v (L.B⁻¹ * L'.B).det = v L'.B.det / v L.B.det := by
  rw [Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', map_mul, map_inv₀,
    div_eq_inv_mul]

theorem v_det_eq_of_pts_eq {L₁ L₂ : Lat v ι} (h : L₁.pts = L₂.pts) :
    v L₁.B.det = v L₂.B.det := by
  have h₁ := (pts_subset_iff L₁ L₂).mp h.subset
  have h₂ := (pts_subset_iff L₂ L₁).mp h.symm.subset
  have hMN : (L₂.B⁻¹ * L₁.B) * (L₁.B⁻¹ * L₂.B) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc L₁.B,
      Matrix.mul_nonsing_inv _ (isUnit_det L₁), Matrix.one_mul,
      Matrix.nonsing_inv_mul _ (isUnit_det L₂)]
  have := v_det_eq_one_of_integral h₁ h₂ hMN
  rw [valuation_det_inv_mul_eq_div] at this
  exact (div_eq_one_iff_eq (valuation_lat_det_ne_zero L₂)).mp this

noncomputable def dual (L : Lat v ι) : Lat v ι :=
  ⟨(L.Bᵀ)⁻¹, by
    rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv', Matrix.det_transpose]
    exact inv_ne_zero L.det_ne⟩

end Lat

section colen

variable {K : Type} [Field K] {v : Valuation K NNReal} {ι : Type} [Fintype ι] [DecidableEq ι]

noncomputable def colen (L' L : Lat v ι) : NNReal := v L'.B.det / v L.B.det

theorem colen_eq_v_det (L' L : Lat v ι) : colen L' L = v (L.B⁻¹ * L'.B).det := by
  rw [_root_.ReciprocityTheory.PGsh.Lat.valuation_det_inv_mul_eq_div]
  rfl

theorem colen_congr {L₁' L₂' L₁ L₂ : Lat v ι} (h' : L₁'.pts = L₂'.pts) (h : L₁.pts = L₂.pts) :
    colen L₁' L₁ = colen L₂' L₂ := by
  unfold colen
  rw [ReciprocityTheory.PGsh.Lat.v_det_eq_of_pts_eq h', ReciprocityTheory.PGsh.Lat.v_det_eq_of_pts_eq h]

theorem colen_le_one {L' L : Lat v ι} (h : L'.pts ⊆ L.pts) : colen L' L ≤ 1 := by
  rw [colen_eq_v_det]
  exact ((ReciprocityTheory.PGsh.Lat.pts_subset_iff L' L).mp h).det_le_one

theorem colen_trans (L'' L' L : Lat v ι) : colen L'' L = colen L'' L' * colen L' L := by
  unfold colen
  rw [div_mul_div_comm, mul_comm (v L''.B.det),
    mul_div_mul_left _ _ (_root_.ReciprocityTheory.PGsh.Lat.valuation_lat_det_ne_zero L')]

theorem colen_self (L : Lat v ι) : colen L L = 1 :=
  div_self (_root_.ReciprocityTheory.PGsh.Lat.valuation_lat_det_ne_zero L)

theorem colen_pos (L' L : Lat v ι) : 0 < colen L' L :=
  pos_iff_ne_zero.mpr
    (div_ne_zero (_root_.ReciprocityTheory.PGsh.Lat.valuation_lat_det_ne_zero L') (_root_.ReciprocityTheory.PGsh.Lat.valuation_lat_det_ne_zero L))

theorem colen_eq_one_iff (hZ : ColengthZeroStatement) {L' L : Lat v ι} (h : L'.pts ⊆ L.pts) :
    colen L' L = 1 ↔ L'.pts = L.pts := by
  constructor
  · intro h1
    have hM := (ReciprocityTheory.PGsh.Lat.pts_subset_iff L' L).mp h
    rw [colen_eq_v_det] at h1
    have hInv := hZ K v ι _ hM h1
    rw [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ (ReciprocityTheory.PGsh.Lat.isUnit_det L)] at hInv
    exact Set.Subset.antisymm h ((ReciprocityTheory.PGsh.Lat.pts_subset_iff L L').mpr hInv)
  · intro he
    rw [colen_congr he rfl, colen_self]

private theorem valuation_det_dual_eq_inv {K : Type} [Field K] {v : Valuation K NNReal} {ι : Type} [Fintype ι] [DecidableEq ι] (L : Lat v ι) :
    v L.dual.B.det = (v L.B.det)⁻¹ := by
  show v ((L.Bᵀ)⁻¹).det = _
  rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv', Matrix.det_transpose, map_inv₀]

theorem colen_dual (L' L : Lat v ι) : colen L.dual L'.dual = colen L' L := by
  unfold colen
  rw [valuation_det_dual_eq_inv, valuation_det_dual_eq_inv, inv_div_inv]

theorem dual_subset {L' L : Lat v ι} (h : L'.pts ⊆ L.pts) : L.dual.pts ⊆ L'.dual.pts := by
  have hM := (ReciprocityTheory.PGsh.Lat.pts_subset_iff L' L).mp h
  rw [ReciprocityTheory.PGsh.Lat.pts_subset_iff]
  show IsIntegralMat v (((L'.Bᵀ)⁻¹)⁻¹ * (L.Bᵀ)⁻¹)
  rw [Matrix.nonsing_inv_nonsing_inv _ (by rw [Matrix.det_transpose]; exact ReciprocityTheory.PGsh.Lat.isUnit_det L'),
    ← Matrix.transpose_nonsing_inv, ← Matrix.transpose_mul]
  intro i j
  exact hM j i

end colen

end ReciprocityTheory.PGsh
