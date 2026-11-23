import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NOfibCut

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Matrix

namespace Formalism.L2.SG.Pf.NcReal.JX.NOf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace Alg

variable {D : D7} (X : HidaSetting D)

theorem hsw (x y : (VS D).V) : (VS D).hT y x = star ((VS D).hT x y) := ((VS D).herm.eq x y).symm

theorem hfe (a b : Fin D.R.rS) : (VS D).hT (X.fY a) (X.eX b) = if a = b then 1 else 0 := by
  rw [hsw, X.ef b a]
  by_cases h : a = b
  · subst h; simp
  · simp [h, Ne.symm h]

theorem hT_sumL {ι : Type*} (s : Finset ι) (c : ι → D.host.E) (y : ι → (VS D).V) (x : (VS D).V) :
    (VS D).hT (∑ i ∈ s, c i • y i) x = ∑ i ∈ s, star (c i) * (VS D).hT (y i) x := by
  simp [map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply]

theorem hT_sumR {ι : Type*} (s : Finset ι) (c : ι → D.host.E) (y : ι → (VS D).V) (x : (VS D).V) :
    (VS D).hT x (∑ i ∈ s, c i • y i) = ∑ i ∈ s, c i * (VS D).hT x (y i) := by
  simp [map_sum, map_smul, smul_eq_mul]

theorem hT_smulL (c : D.host.E) (x y : (VS D).V) : (VS D).hT (c • x) y = star c * (VS D).hT x y := by
  simp [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply]

theorem coef_e (S : Set (Fin D.R.rS)) {x : (VS D).V} (hx : x ∈ Submodule.span D.host.E (X.eX '' S)) :
    x = ∑ b, (VS D).hT (X.fY b) x • X.eX b ∧ ∀ b, b ∉ S → (VS D).hT (X.fY b) x = 0 := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, ha, rfl⟩ := hy
    refine ⟨?_, fun b hb => ?_⟩
    · simp only [hfe, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    · rw [hfe, if_neg]; rintro rfl; exact hb ha
  | zero => simp
  | add x y _ _ hx hy =>
    refine ⟨?_, fun b hb => ?_⟩
    · conv_lhs => rw [hx.1, hy.1]
      simp only [map_add, add_smul, Finset.sum_add_distrib]
    · rw [map_add, hx.2 b hb, hy.2 b hb, add_zero]
  | smul c x _ hx =>
    refine ⟨?_, fun b hb => ?_⟩
    · conv_lhs => rw [hx.1]
      simp only [map_smul, smul_eq_mul, Finset.smul_sum, smul_smul]
    · rw [map_smul, hx.2 b hb, smul_zero]

theorem coef_range {x : (VS D).V} (hx : x ∈ Submodule.span D.host.E (Set.range X.eX)) :
    x = ∑ b, (VS D).hT (X.fY b) x • X.eX b := by
  rw [← Set.image_univ] at hx
  exact (coef_e X Set.univ hx).1

theorem pW_inW (y : (VS D).V) : InW X (pW X y) := by
  intro c
  constructor
  · simp only [pW, map_sub, hT_sumR, X.ee, X.ef, mul_zero, Finset.sum_const_zero, sub_zero, mul_ite, mul_one,
      Finset.sum_ite_eq, Finset.mem_univ, if_true, sub_self]
  · simp only [pW, map_sub, hT_sumR, X.ff, hfe, mul_zero, Finset.sum_const_zero, sub_zero, mul_ite, mul_one,
      Finset.sum_ite_eq, Finset.mem_univ, if_true, sub_self]

theorem decomp (y : (VS D).V) :
    y = ∑ d, (VS D).hT (X.fY d) y • X.eX d + ∑ d, (VS D).hT (X.eX d) y • X.fY d + pW X y := by
  simp only [pW]; abel

theorem pW_of_inW {w : (VS D).V} (hw : InW X w) : pW X w = w := by
  simp only [pW, (hw _).1, (hw _).2, zero_smul, Finset.sum_const_zero, sub_zero]

theorem pW_add (x y : (VS D).V) : pW X (x + y) = pW X x + pW X y := by
  simp only [pW, map_add, add_smul, Finset.sum_add_distrib]; abel

theorem pW_smul (c : D.host.E) (x : (VS D).V) : pW X (c • x) = c • pW X x := by
  simp only [pW, map_smul, smul_eq_mul, mul_smul, ← Finset.smul_sum, smul_sub]

theorem pW_e (a : Fin D.R.rS) : pW X (X.eX a) = 0 := by
  simp only [pW, X.ee, hfe, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Finset.sum_const_zero, sub_zero, sub_self]

theorem pW_sum_e (c : Fin D.R.rS → D.host.E) : pW X (∑ d, c d • X.eX d) = 0 := by
  induction (Finset.univ : Finset (Fin D.R.rS)) using Finset.induction_on with
  | empty => simp [pW]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, pW_add, pW_smul, pW_e, smul_zero, zero_add, ih]

theorem hT_w_e {w : (VS D).V} (hw : InW X w) (a : Fin D.R.rS) : (VS D).hT w (X.eX a) = 0 := by
  rw [hsw, (hw a).1, star_zero]

theorem hT_w_f {w : (VS D).V} (hw : InW X w) (a : Fin D.R.rS) : (VS D).hT w (X.fY a) = 0 := by
  rw [hsw, (hw a).2, star_zero]

theorem parseval (y y' : (VS D).V) :
    (VS D).hT y y' = ∑ d, star ((VS D).hT (X.fY d) y) * (VS D).hT (X.eX d) y' +
      ∑ d, star ((VS D).hT (X.eX d) y) * (VS D).hT (X.fY d) y' + (VS D).hT (pW X y) (pW X y') := by
  have h1 : (VS D).hT (pW X y) y' = (VS D).hT (pW X y) (pW X y') := by
    conv_lhs => rw [decomp X y']
    rw [map_add, map_add, hT_sumR, hT_sumR]
    simp only [hT_w_e X (pW_inW X y), hT_w_f X (pW_inW X y), mul_zero, Finset.sum_const_zero, zero_add]
  conv_lhs => rw [decomp X y]
  rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, hT_sumL, hT_sumL, h1]

section N

variable {X} {u : D.what₂.Word} {n : (VS D).V ≃ₗ[D.host.E] (VS D).V}

theorem iso (hn : NFl X u n) (x y : (VS D).V) : (VS D).hT (n x) (n y) = (VS D).hT x y := hn.1 x y

theorem iso_symm (hn : NFl X u n) (x y : (VS D).V) : (VS D).hT (n.symm x) y = (VS D).hT x (n y) := by
  rw [← iso hn (n.symm x) y, LinearEquiv.apply_symm_apply]

theorem ne_mem (hn : NFl X u n) (a : Fin D.R.rS) :
    n (X.eX a) - X.eX a ∈ Submodule.span D.host.E (X.eX '' {b | b.1 < a.1}) := by
  have hx : X.eX a ∈ Xflag (lf D (X.Fu u)) (a.1 + 1) := by
    change X.eX a ∈ Submodule.span D.host.E ((X.Fu u).e '' {i | i.1 < a.1 + 1})
    rw [X.Fu_e]
    exact Submodule.subset_span ⟨a, by simp, rfl⟩
  have := hn.2.1 a.1 _ hx
  change _ ∈ Submodule.span D.host.E ((X.Fu u).e '' {i | i.1 < a.1}) at this
  rwa [X.Fu_e] at this

theorem Xq_expand (hn : NFl X u n) (a : Fin D.R.rS) : n (X.eX a) = ∑ b, Xq X n b a • X.eX b := by
  have h := (coef_e X _ (ne_mem hn a)).1
  have e : n (X.eX a) = (n (X.eX a) - X.eX a) + X.eX a := by abel
  conv_lhs => rw [e, h]
  conv_rhs => rw [show (∑ b, Xq X n b a • X.eX b) = ∑ b, ((VS D).hT (X.fY b) (n (X.eX a) - X.eX a) +
    (if b = a then 1 else 0)) • X.eX b from Finset.sum_congr rfl fun b _ => by
      rw [map_sub, hfe, sub_add_cancel]; rfl]
  simp only [add_smul, Finset.sum_add_distrib, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

theorem Xq_entry (hn : NFl X u n) (b a : Fin D.R.rS) :
    Xq X n b a = (VS D).hT (X.fY b) (n (X.eX a) - X.eX a) + if b = a then 1 else 0 := by
  rw [map_sub, hfe, sub_add_cancel]; rfl

theorem Xq_lower (hn : NFl X u n) {b a : Fin D.R.rS} (h : a < b) : Xq X n b a = 0 := by
  rw [Xq_entry hn, (coef_e X _ (ne_mem hn a)).2 b (by simp only [Set.mem_setOf_eq, not_lt]; exact le_of_lt h),
    if_neg (ne_of_gt h), add_zero]

theorem Xq_diag (hn : NFl X u n) (a : Fin D.R.rS) : Xq X n a a = 1 := by
  rw [Xq_entry hn, (coef_e X _ (ne_mem hn a)).2 a (by simp), if_pos rfl, zero_add]

theorem inW_orth {w : (VS D).V} (hw : InW X w) : w ∈ orth (VS D) (Xsp (lf D (X.Fu u))) := by
  change w ∈ orth (VS D) (Submodule.span D.host.E (Set.range (X.Fu u).e))
  rw [X.Fu_e]
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker]
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy => obtain ⟨a, rfl⟩ := hy; exact (hw a).1
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, LinearMap.add_apply, hx, hy, add_zero]
  | smul c x _ hx => rw [hT_smulL, hx, mul_zero]

theorem nw (hn : NFl X u n) {w : (VS D).V} (hw : InW X w) :
    n w = w + ∑ d, (VS D).hT (X.fY d) (n w) • X.eX d := by
  have h1 := hn.2.2 w (inW_orth hw)
  change _ ∈ Submodule.span D.host.E (Set.range (X.Fu u).e) at h1
  rw [X.Fu_e] at h1
  have h2 := coef_range X h1
  have e : ∀ d, (VS D).hT (X.fY d) (n w - w) = (VS D).hT (X.fY d) (n w) := fun d => by
    rw [map_sub, (hw d).2, sub_zero]
  simp only [e] at h2
  rw [← h2]; abel

theorem row (hn : NFl X u n) (b : Fin D.R.rS) {w : (VS D).V} (hw : InW X w) :
    (VS D).hT (X.fY b) (n w) = (VS D).hT (xq X n b) w := by
  rw [← iso_symm hn, parseval X _ w]
  simp only [(hw _).1, (hw _).2, mul_zero, Finset.sum_const_zero, zero_add, pW_of_inW X hw]
  rfl

def Bq (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E :=
  fun d a => (VS D).hT (X.eX d) (n (X.fY a))

theorem XB (hn : NFl X u n) : (Xq X n)ᴴ * Bq (X := X) n = 1 := by
  ext b a
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Bq]
  rw [← hT_sumL, ← Xq_expand hn, iso hn, X.ef, Matrix.one_apply]

theorem ff_rel (hn : NFl X u n) (a c : Fin D.R.rS) :
    ((Aq X n)ᴴ * Bq (X := X) n + (Bq (X := X) n)ᴴ * Aq X n) a c +
      (VS D).hT (pW X (n (X.fY a))) (pW X (n (X.fY c))) = 0 := by
  have h := parseval X (n (X.fY a)) (n (X.fY c))
  rw [iso hn, X.ff] at h
  rw [h, Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply, Aq, Bq]

theorem omega_rel (hn : NFl X u n) (a : Fin D.R.rS) {w : (VS D).V} (hw : InW X w) :
    (VS D).hT (pW X (n (X.fY a))) w = -∑ d, star (Bq (X := X) n d a) * (VS D).hT (xq X n d) w := by
  have h := parseval X (n (X.fY a)) (n w)
  rw [iso hn] at h
  have he : ∀ d, (VS D).hT (X.eX d) (n w) = 0 := fun d => by
    rw [nw hn hw, map_add, hT_sumR, (hw d).1, zero_add]
    simp only [X.ee, mul_zero, Finset.sum_const_zero]
  have hp : pW X (n w) = w := by
    conv_lhs => rw [nw hn hw]
    rw [pW_add, pW_sum_e, add_zero, pW_of_inW X hw]
  simp only [he, mul_zero, Finset.sum_const_zero, zero_add, row hn _ hw, hp] at h
  rw [(hw a).2] at h
  simp only [Bq]
  linear_combination -h

theorem xq_inW (d : Fin D.R.rS) : InW X (xq X n d) := pW_inW X _

theorem gram_omega (hn : NFl X u n) (a c : Fin D.R.rS) :
    (VS D).hT (pW X (n (X.fY a))) (pW X (n (X.fY c))) =
      ((Bq (X := X) n)ᴴ * Gq D (xq X n) * Bq (X := X) n) a c := by
  rw [omega_rel hn a (pW_inW X (n (X.fY c)))]
  have h2 : ∀ d, (VS D).hT (xq X n d) (pW X (n (X.fY c))) =
      -∑ d', Bq (X := X) n d' c * (VS D).hT (xq X n d) (xq X n d') := by
    intro d
    rw [hsw, omega_rel hn c (xq_inW d)]
    simp only [star_neg, star_sum, star_mul', star_star, ← hsw]
  simp only [h2, Matrix.mul_apply, Matrix.conjTranspose_apply, Gq, Finset.mul_sum, Finset.sum_mul, mul_neg,
    Finset.sum_neg_distrib, neg_neg]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d' _ => Finset.sum_congr rfl fun d _ => by ring

theorem Xq_det (hn : NFl X u n) : (Xq X n).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular]
  · simp [Xq_diag hn]
  · intro i j hij
    exact Xq_lower hn hij

end N

end Alg

open Alg in

theorem dictGram_holds : DictGram := by
  intro D X u n hn
  refine ⟨fun b a h => Xq_lower hn h, fun a => Xq_diag hn a, fun b => pW_inW X _, ?_⟩
  have hdet : IsUnit (Xq X n).det := by rw [Xq_det hn]; exact isUnit_one
  have hB : Bq (X := X) n = ((Xq X n)⁻¹)ᴴ := by
    rw [Matrix.conjTranspose_nonsing_inv]
    exact (Matrix.inv_eq_right_inv (XB hn)).symm
  have hBh : (Bq (X := X) n)ᴴ = (Xq X n)⁻¹ := by rw [hB, Matrix.conjTranspose_conjTranspose]
  have hM : Mq X n = (Bq (X := X) n)ᴴ * Aq X n := by rw [hBh]; rfl
  have hMh : (Mq X n)ᴴ = (Aq X n)ᴴ * Bq (X := X) n := by
    rw [hM, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have hG : Gp D (Xq X n) (xq X n) = (Bq (X := X) n)ᴴ * Gq D (xq X n) * Bq (X := X) n := by
    rw [Gp, hBh, hB]
  rw [hMh, hM, hG]
  refine Matrix.ext fun a c => ?_
  have := ff_rel hn a c
  rw [gram_omega hn a c] at this
  simp only [Matrix.add_apply, Matrix.neg_apply] at this ⊢
  linear_combination this

end Formalism.L2.SG.Pf.NcReal.JX.NOf
