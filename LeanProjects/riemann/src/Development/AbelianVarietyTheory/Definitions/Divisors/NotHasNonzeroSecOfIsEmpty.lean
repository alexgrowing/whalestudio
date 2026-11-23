import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.QCoh GlobalTheory.CechPic

namespace GlobalTheory.PositivityModel

variable {k : Type} [Field k] {X : Scheme.{0}} [Algebra k Γ(X, ⊤)] {H L N A : LB X}

theorem not_hasNonzeroSec_of_isEmpty [IsEmpty X] : ¬ HasNonzeroSec L := by
  rintro ⟨s, hs⟩
  refine hs (DVR.SecOps.sec_ext fun i => ?_)
  have : L.U i = ⊥ := by ext x; exact isEmptyElim x
  have : Subsingleton Γ(X, L.U i) := by rw [this]; infer_instance
  exact Subsingleton.elim _ _

theorem empty_values [IsEmpty X] : ¬ IsBig k L ∧ ¬ IsPsEff L := by
  refine ⟨fun h => not_hasNonzeroSec_of_isEmpty h.frequently_hasNonzeroSec.exists.choose_spec,
    fun h => ?_⟩
  obtain ⟨_, -, hs⟩ := h.2
  obtain ⟨_, -, hr⟩ := hs 1 le_rfl
  exact not_hasNonzeroSec_of_isEmpty hr

theorem isNef_of_dim_le_zero (hX : topologicalKrullDim X ≤ 0) (hL : L.IsLB) : IsNef k L :=
  ⟨hL, fun Z hZ => by
    have h := (topologicalKrullDim_subspace_le X (Z : Set X)).trans hX
    rw [hZ.2] at h
    exact absurd h (by decide)⟩

theorem genericPoint_mem [IsIntegral X] (hd : topologicalKrullDim X = 1) {Z : Closeds X}
    (hZ : IsCompleteCurve k Z) : genericPoint X ∈ Z := by
  by_contra hn
  have h := topologicalKrullDim_add_one_le Z.isClosed isClosed_univ fun x _ =>
    ⟨genericPoint X, trivial, hn, genericPoint_specializes x⟩
  have h' := h.trans ((topologicalKrullDim_subspace_le X Set.univ).trans hd.le)
  rw [hZ.2] at h'
  exact absurd h' (by decide)

theorem isNef_of_isPsEff [IsIntegral X] (hd : topologicalKrullDim X = 1) (h : IsPsEff N) :
    IsNef k N := by
  obtain ⟨A, hA, hs⟩ := h.2
  refine ⟨h.1, fun Z hZ => ?_⟩
  by_contra! hneg
  have key : ∀ m : ℕ, 1 ≤ m → 0 ≤ m * interNumRed k Z ![N] + interNumRed k Z ![A] := by
    intro m hm
    obtain ⟨r, hr, hs⟩ := hs m hm
    obtain ⟨s, hs⟩ := hasNonzeroSec_iff.1 hs
    have hT := isLB_tens (isLB_lbPow h.1 m) hA.isLB
    have h0 := (hZ.interNumRed_nonneg_of_sec hA (isLB_lbPow hT r) s (genericPoint_mem hd hZ) hs).1
    rw [hZ.interNumRed_lbPow hA hT, hZ.interNumRed_of_cls_eq_add hA hT (isLB_lbPow h.1 m) hA.isLB rfl,
      hZ.interNumRed_lbPow hA h.1] at h0
    exact nonneg_of_mul_nonneg_right h0 (Nat.cast_pos.2 hr)
  have hp := hA.interNumRed_pos hZ
  have := key ((interNumRed k Z ![A]).toNat + 1) (by omega)
  push_cast at this
  rw [Int.toNat_of_nonneg hp.le] at this
  nlinarith

section Space
open ProjSpace
variable (k) (D : ℕ)

theorem point_values (n : ℤ) : IsNef k (lbZPow (O1 k 0) n) ∧ IsBig k (lbZPow (O1 k 0) n) ∧
    IsPsEff (lbZPow (O1 k 0) n) := by
  have hO := O1_isLB k 0
  have hn := Twist.isLB_lbZPow hO n
  have hb : IsBig k (lbZPow (O1 k 0) n) := by
    refine (isBig_iff (algebraMap_top_eq k 0) (isProjOver_str k 0) (topologicalKrullDim_eq k 0)).2
      ⟨hn, 1, one_pos, Frequently.of_forall fun m => ?_⟩
    obtain ⟨e⟩ := ProjCoh.nonempty_coh_zero_equiv k (m * n)
    have h1 : lbH0 k (lbZPow (O1 k 0) (m * n)) = 1 := e.finrank_eq.trans (Module.finrank_self k)
    rw [lineBundleGlobalSectionsDim_congr_picardClass (isLB_lbPow hn m) (Twist.isLB_lbZPow hO (m * n))
      (by rw [cls_lbPow hn, cls_lbZPow hO, cls_lbZPow hO]; module), h1]
    simp
  exact ⟨isNef_of_dim_le_zero (topologicalKrullDim_eq k 0).le hn, hb,
    hb.isPsEff (isAmple_projective_O_one k 0)⟩

theorem isPsEff_iff (n : ℤ) : IsPsEff (lbZPow (O1 k (D + 1)) n) ↔ 0 ≤ n := by
  have hO := O1_isLB k (D + 1)
  have hA := isAmple_projective_O_one k (D + 1)
  have := isNoetherian_of_isProjOver (isProjOver_str k (D + 1))
  refine ⟨fun h => ?_, fun h => ?_⟩
  · by_contra! hn
    obtain ⟨r, hr, hs⟩ := h.exists_hasNonzeroSec hA (m := 2) one_le_two
    have hs' : HasNonzeroSec (lbZPow (O1 k (D + 1)) (r * (2 * n + 1))) :=
      hs.of_cls_eq (Twist.isLB_lbZPow hO _) (isLB_lbPow (isLB_tens (isLB_lbPow h.1 2) hO) r) (by
        rw [cls_lbPow_tens_lbPow h.1 hO, cls_lbZPow hO, cls_lbZPow hO]; module)
    have := ProjCoh.subsingleton_coh_zero k (N := D + 1) (by omega) (n := r * (2 * n + 1))
      (mul_neg_of_pos_of_neg (by exact_mod_cast hr) (by omega))
    exact not_nontrivial _ (hasNonzeroSec_iff_nontrivial.1 hs')
  · lift n to ℕ using h
    have : 0 < lbH0 k (lbPow (O1 k (D + 1)) n) := by
      rw [sectionDim_twistingSheaf_pow]; exact Nat.choose_pos (by omega)
    exact ((lineBundleHasNonzeroSection_of_globalSectionsDim_pos this).isPsEff (isLB_lbPow hO n) hA).of_cls_eq
      (Twist.isLB_lbZPow hO _) rfl

theorem isBig_iff' (n : ℤ) : IsBig k (lbZPow (O1 k (D + 1)) n) ↔ 0 < n := by
  have hO := O1_isLB k (D + 1)
  have hA := isAmple_projective_O_one k (D + 1)
  refine ⟨fun h => ?_, fun h => ?_⟩
  · refine ((isPsEff_iff k D n).1 (h.isPsEff hA)).lt_of_ne ?_
    rintro rfl
    exact (triv_nef_not_big k D).2.2 (h.of_cls_eq (LB.isLB_triv _)
      (by rw [cls_lbZPow hO, cls_triv, zero_zsmul]))
  · lift n to ℕ using h.le
    exact ((isBig_twistingSheaf k (D + 1)).pow (algebraMap_top_eq k _) (isProjOver_str k _)
      (n := n) (by omega)).of_cls_eq (Twist.isLB_lbZPow hO _)
      rfl

theorem isNef_iff_line (n : ℤ) : IsNef k (lbZPow (O1 k 1) n) ↔ 0 ≤ n := by
  have hO := O1_isLB k 1
  have hA := isAmple_projective_O_one k 1
  refine ⟨fun h => ?_, fun h => isNef_of_isPsEff (topologicalKrullDim_eq k 1)
    ((isPsEff_iff k 0 n).2 h)⟩
  by_contra! hn
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = -((m + 1 : ℕ) : ℤ) := ⟨(-n - 1).toNat, by push_cast; omega⟩
  have h' : IsNef k (lbPow (dual (O1 k 1)) (m + 1)) := h.of_cls_eq (isLB_lbPow (isLB_dual hO) _)
    (by rw [cls_lbPow (isLB_dual hO), cls_dual hO, cls_lbZPow hO]; module)
  exact not_isNef_dual_twistingSheaf k ((isNef_pow_iff hA (isLB_dual hO) (by omega)).1 h')

theorem degree_line (n : ℤ) :
    interNumRed k (⊤ : Closeds (PSpace k 1)) ![lbZPow (O1 k 1) n] = n := by
  have hO := O1_isLB k 1
  have hn := Twist.isLB_lbZPow hO n
  rw [InterModel.interNumRed_eq_interNumOn k (𝟙 _) ⊤ (by simp), interNumOn_id, interNum_one k _ hn]
  obtain ⟨i⟩ := nonempty_twist_iso_of_cls_eq (structureModule (PSpace k 1))
    (Twist.isLB_lbZPow hn (-1)) (Twist.isLB_lbZPow hO (-n))
    (by rw [cls_lbZPow hn, cls_lbZPow hO, cls_lbZPow hO]; module)
  obtain ⟨j⟩ := nonempty_twist_iso_of_cls_eq (structureModule (PSpace k 1))
    (Twist.isLB_lbZPow hO 0) (LB.isLB_triv _)
    (by rw [cls_lbZPow hO, cls_triv, zero_zsmul])
  have h1 := (chi_congr k i).trans (ProjCoh.chi_sheafO k 1 (-n))
  have h0 := (chi_congr k j).symm.trans (ProjCoh.chi_sheafO k 1 0)
  rw [chi_congr k (Twist.trivIso (structureModule (PSpace k 1))), h0, h1]
  simp

end Space

end GlobalTheory.PositivityModel
