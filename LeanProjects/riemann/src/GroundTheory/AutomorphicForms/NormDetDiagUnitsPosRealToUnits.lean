import Mathlib
import GroundTheory.AutomorphicForms.ReductionMahler

open NumberField IsDedekindDomain Topology Filter Set Matrix
open scoped NumberField.AdeleRing RestrictedProduct
open GroundTheory.Global GroundTheory.Global.IdeleGroup

namespace GroundTheory.Automorphic

noncomputable section

namespace Reduction

theorem eq_one_of_isCompact {G : Type*} [Group G] [TopologicalSpace G] {H : Subgroup G}
    (hH : IsCompact (H : Set G)) (f : G →* {r : ℝ // 0 < r}) (hf : Continuous fun g => (f g : ℝ))
    {h : G} (hh : h ∈ H) : f h = 1 := by
  obtain ⟨M, hM⟩ := hH.exists_bound_of_continuousOn hf.continuousOn
  have hbound : ∀ m : ℕ, (f h : ℝ) ^ m ≤ M ∧ ((f h : ℝ)⁻¹) ^ m ≤ M := fun m => by
    have h1 := hM (h ^ m) (pow_mem hh m)
    have h2 := hM ((h⁻¹) ^ m) (pow_mem (inv_mem hh) m)
    rw [map_pow, Positive.val_pow, Real.norm_eq_abs, abs_of_pos (pow_pos (f h).2 m)] at h1
    rw [map_pow, map_inv, Positive.val_pow, Positive.coe_inv, Real.norm_eq_abs,
      abs_of_pos (pow_pos (inv_pos.2 (f h).2) m)] at h2
    exact ⟨h1, h2⟩
  refine Subtype.ext ?_
  rw [Positive.val_one]
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have h1 : 1 < (f h : ℝ)⁻¹ := (one_lt_inv₀ (f h).2).2 hlt
    obtain ⟨m, hm⟩ := (tendsto_pow_atTop_atTop_of_one_lt h1).eventually_gt_atTop M |>.exists
    exact absurd (hbound m).2 (not_le.2 hm)
  · obtain ⟨m, hm⟩ := (tendsto_pow_atTop_atTop_of_one_lt hgt).eventually_gt_atTop M |>.exists
    exact absurd (hbound m).1 (not_le.2 hm)

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

def normDet (w : InfinitePlace K) : GL (Fin n) w.Completion →* {r : ℝ // 0 < r} where
  toFun g := ⟨‖(g : Matrix (Fin n) (Fin n) w.Completion).det‖, norm_pos_iff.2 (by
    have := (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit
    exact this.ne_zero)⟩
  map_one' := by ext; simp
  map_mul' g h := by ext; simp [Matrix.det_mul]

theorem continuous_normDet (w : InfinitePlace K) :
    Continuous fun g : GL (Fin n) w.Completion => (normDet (n := n) w g : ℝ) :=
  (Continuous.matrix_det (Units.continuous_val (M := Matrix (Fin n) (Fin n) w.Completion))).norm

theorem norm_det_of_mem_archCompact {w : InfinitePlace K} {k : GL (Fin n) w.Completion}
    (hk : k ∈ archCompact w) : ‖(k : Matrix (Fin n) (Fin n) w.Completion).det‖ = 1 := by
  have := eq_one_of_isCompact (isCompact_archCompact w) (normDet w) (continuous_normDet w) hk
  exact congrArg Subtype.val this

theorem norm_det_infAt_of_mem_maxCompact {k : AdelicGLn.AdelicGL K n} (hk : k ∈ maxCompact)
    (w : InfinitePlace K) : ‖(infAt w k : Matrix (Fin n) (Fin n) w.Completion).det‖ = 1 :=
  norm_det_of_mem_archCompact (hk.1 w)

theorem infAt_diagUnits (w : InfinitePlace K) (f : Fin n → IdeleGroup K) :
    infAt w (diagUnits n f) = diagUnits n (fun i => infiniteProj w (f i)) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [infAt_apply, coe_diagUnits, coe_diagUnits, diagonal_apply, diagonal_apply]
  split_ifs
  · rw [coe_infiniteProj]
  · rfl

theorem infAt_diagUnits_posIdele (w : InfinitePlace K) (r : Fin n → ℝ) (hr : ∀ i, 0 < r i) :
    infAt w (diagUnits n fun i => posIdele (K := K) (r i) (hr i)) =
      diagUnits n (fun i => posRealToUnits w ⟨r i ^ w.mult, pow_pos (hr i) _⟩) := by
  rw [infAt_diagUnits]
  congr 1
  funext i
  exact infiniteProj_posIdele (r i) (hr i) w

theorem norm_posRealToUnits (w : InfinitePlace K) {r : ℝ} (hr : 0 < r) :
    ‖((posRealToUnits w ⟨r ^ w.mult, pow_pos hr _⟩ : (w.Completion)ˣ) : w.Completion)‖ = r := by
  have h := norm_posRealElem_pow w (pow_pos hr w.mult).le
  have hm : w.mult ≠ 0 := InfinitePlace.mult_ne_zero
  exact (pow_left_inj₀ (norm_nonneg _) hr.le hm).1 h

theorem norm_det_diagUnits_posRealToUnits (w : InfinitePlace K) (r : Fin n → ℝ) (hr : ∀ i, 0 < r i) :
    ‖((diagUnits n (fun i => posRealToUnits w ⟨r i ^ w.mult, pow_pos (hr i) _⟩) :
      GL (Fin n) w.Completion) : Matrix (Fin n) (Fin n) w.Completion).det‖ = ∏ i, r i := by
  rw [coe_diagUnits, det_diagonal, norm_prod]
  exact Finset.prod_congr rfl fun i _ => norm_posRealToUnits w (hr i)

theorem prodEquiv_diagUnits_posIdele_snd (r : Fin n → ℝ) (hr : ∀ i, 0 < r i) :
    (AdelicGLn.prodEquiv K n (diagUnits n fun i => posIdele (K := K) (r i) (hr i))).2 = 1 := by
  refine Units.ext (Matrix.ext fun a b => ?_)
  rw [AdelicGLn.prodEquiv_apply_snd, coe_diagUnits, diagonal_apply]
  split_ifs with h
  · subst h
    refine RestrictedProduct.ext _ _ fun v => ?_
    have := posIdele_finite (K := K) (r a) (hr a) v
    exact this.trans (by simp; rfl)
  · rw [Units.val_one, Matrix.one_apply_ne h]
    rfl

end Reduction

end

end GroundTheory.Automorphic
