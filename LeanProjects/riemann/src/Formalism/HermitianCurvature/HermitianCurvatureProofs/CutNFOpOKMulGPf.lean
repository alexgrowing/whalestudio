import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFOpOKMulG
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFTopDomEmpty
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.BetaSesquilinearity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section term

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def mulTerm (c : B.Mat k r → ℝ) (T : B.DTerm k r Wp Wq) : B.DTerm k r Wp Wq where
  coef := fun g => ((c g : ℝ) : ℂ) • T.coef g
  coefAdj := fun g => ((c g : ℝ) : ℂ) • T.coefAdj g
  word := T.word
  word_lie := T.word_lie
  adj_id := by
    intro x A B'
    unfold B.hsInner
    simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply]
    rw [TBBx2.Tri.hsVec_smul, TBBx2.Tri.hsVec_smul, inner_smul_right, inner_smul_left]
    have h := T.adj_id x A B'
    unfold B.hsInner at h
    rw [h]
    simp

def mulOpG (c : B.Mat k r → ℝ) (Th : B.DiffOp k r Wp Wq) : B.DiffOp k r Wp Wq := Th.map (mulTerm c)

theorem mulOpG_apply (c : B.Mat k r → ℝ) (Th : B.DiffOp k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp))
    (g : B.Mat k r) : B.opApply (mulOpG c Th) F g = ((c g : ℝ) : ℂ) • B.opApply Th F g := by
  unfold mulOpG B.opApply
  induction Th with
  | nil => simp
  | cons T Th ih =>
    simp only [List.map_cons, List.sum_cons, smul_add]
    rw [← ih]
    congr 1

theorem mulOpG_order (c : B.Mat k r → ℝ) (Th : B.DiffOp k r Wp Wq) : B.opOrder (mulOpG c Th) = B.opOrder Th := by
  unfold B.opOrder mulOpG
  rw [List.map_map]
  rfl

def lcomp : ((Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) →L[ℂ]
    (((Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) →L[ℂ] ((Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp))) :=
  ContinuousLinearMap.compL ℂ (Wq →L[ℂ] Wp) (Wq →L[ℂ] Wp) (Wq →L[ℂ] Wp)

theorem ckOn_clm {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    {m : ℕ∞} {UU : Set (B.Mat k r)} (L : E →L[ℂ] F) {f : B.Mat k r → E} (hf : B.CkOn m UU f) :
    B.CkOn m UU (fun g => L (f g)) := by
  unfold B.CkOn at hf ⊢
  intro g₀ hg₀
  obtain ⟨U, f', hU, hg, hf', ef⟩ := hf g₀ hg₀
  refine ⟨U, fun g => L (f' g), hU, hg, ?_, ?_⟩
  · exact ((L.restrictScalars ℝ).contDiff.comp_contDiffOn hf').congr (fun g _ => rfl)
  · intro g hgU hgG
    show L (f g) = L (f' g)
    rw [ef g hgU hgG]

theorem ckOn_apply {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    {m : ℕ∞} {UU : Set (B.Mat k r)} {a : B.Mat k r → (E →L[ℂ] F)} {f : B.Mat k r → E} (ha : B.CkOn m UU a)
    (hf : B.CkOn m UU f) : B.CkOn m UU (fun g => a g (f g)) := by
  unfold B.CkOn at ha hf ⊢
  intro g₀ hg₀
  obtain ⟨U₁, a', hU₁, hg₁, ha', ea⟩ := ha g₀ hg₀
  obtain ⟨U₂, f', hU₂, hg₂, hf', ef⟩ := hf g₀ hg₀
  refine ⟨U₁ ∩ U₂, fun g => a' g (f' g), hU₁.inter hU₂, ⟨hg₁, hg₂⟩, ?_, ?_⟩
  · have h1 : ContDiffOn ℝ m (fun g => (a' g).restrictScalars ℝ) (U₁ ∩ U₂) :=
      (ContinuousLinearMap.restrictScalarsL ℂ E F ℝ ℝ).contDiff.comp_contDiffOn
        (ha'.mono Set.inter_subset_left)
    exact h1.clm_apply (hf'.mono Set.inter_subset_right)
  · intro g hg hgG
    show a g (f g) = a' g (f' g)
    rw [ea g hg.1 hgG, ef g hg.2 hgG]

theorem Dw_clm {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    (L : E →L[ℂ] F) : ∀ (w : List (Bool × B.Mat k r)), (∀ x ∈ w, B.inLie k r x.2) →
    ∀ {f : B.Mat k r → E}, B.CkOn ⊤ (B.GV k r) f →
      ∀ g ∈ B.GV k r, Dw w (fun h => L (f h)) g = L (Dw w f g)
  | [], _, _, _, _, _ => rfl
  | x :: w, hw, f, hf, g, hg => by
    have hw' : ∀ y ∈ w, B.inLie k r y.2 := fun y hy => hw y (by simp [hy])
    have hx : B.inLie k r x.2 := hw x (by simp)
    show Dx x (Dw w (fun h => L (f h))) g = L (Dx x (Dw w f) g)
    rw [Dx_congr hx (Dw_clm L w hw' hf) g hg]
    have hD : B.CkOn 1 (B.GV k r) (Dw w f) := CkOn_Dw hw' (by
      have : ((1 : ℕ∞) + (w.length : ℕ∞)) ≤ ⊤ := le_top
      exact sCkOn_mono this hf)
    have h1 := CkOn_diff hx hD hg hg
    have h2 := (L.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
    rw [Dx_eq]
    exact h2.deriv

theorem comp_bound {A Φ : B.Mat k r → ((Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp))}
    (hA : B.CkOn ⊤ (B.GV k r) A) (hΦ : B.CkOn ⊤ (B.GV k r) Φ) (m : ℕ) (Ca Cb κ d : ℝ)
    (hCa : ∀ u w : List (B.Mat k r), (∀ X ∈ u, B.unitLie k r X) → (∀ X ∈ w, B.unitLie k r X) →
      u.length + w.length ≤ m → ∀ g ∈ B.GV k r, ‖B.dLR u w A g‖ ≤ Ca * B.gN g ^ κ)
    (hCb : ∀ u w : List (B.Mat k r), (∀ X ∈ u, B.unitLie k r X) → (∀ X ∈ w, B.unitLie k r X) →
      u.length + w.length ≤ m → ∀ g ∈ B.GV k r, ‖B.dLR u w Φ g‖ ≤ Cb * B.gN g ^ d)
    (u w : List (B.Mat k r)) (hu : ∀ X ∈ u, B.unitLie k r X) (hw : ∀ X ∈ w, B.unitLie k r X)
    (hl : u.length + w.length ≤ m) (g : B.Mat k r) (hg : g ∈ B.GV k r) :
    ‖B.dLR u w (fun x => (A x).comp (Φ x)) g‖ ≤
      2 ^ m * ‖lcomp (Wp := Wp) (Wq := Wq)‖ * max Ca 0 * max Cb 0 * B.gN g ^ (κ + d) := by
  have hg1 : 1 ≤ B.gN g := gN_ge_one hg
  have hg0 : 0 < B.gN g := lt_of_lt_of_le one_pos hg1
  have hlie := lie_LR (fun X hX => (hu X hX).1) (fun X hX => (hw X hX).1)
  have ha : B.CkOn ⊤ (B.GV k r) (fun x => lcomp (Wp := Wp) (Wq := Wq) (A x)) := ckOn_clm lcomp hA
  have hap : (fun x => (A x).comp (Φ x)) = ap (fun x => lcomp (Wp := Wp) (Wq := Wq) (A x)) Φ := rfl
  rw [hap, dLR_eq]
  have hPr : Pr ∅ (B.GV k r) ((wL u ++ wR w).length : ℕ∞) (fun x => lcomp (Wp := Wp) (Wq := Wq) (A x)) Φ :=
    ⟨sCkOn_mono le_top ha, sCkOn_mono le_top hΦ, fun _ _ h => h.elim⟩
  have hM : ∀ w₁ w₂ : List (Bool × B.Mat k r), w₁.Sublist (wL u ++ wR w) → w₂.Sublist (wL u ++ wR w) →
      w₁.length + w₂.length = (wL u ++ wR w).length →
      ‖Dw w₁ (fun x => lcomp (Wp := Wp) (Wq := Wq) (A x)) g‖ * ‖Dw w₂ Φ g‖ ≤
        (‖lcomp (Wp := Wp) (Wq := Wq)‖ * (max Ca 0 * B.gN g ^ κ)) * (max Cb 0 * B.gN g ^ d) := by
    intro w₁ w₂ h₁ h₂ _
    obtain ⟨u₁, v₁, hu₁, hv₁, rfl⟩ := sub_LR h₁
    obtain ⟨u₂, v₂, hu₂, hv₂, rfl⟩ := sub_LR h₂
    have hl1 : u₁.length + v₁.length ≤ m := by
      have := hu₁.length_le; have := hv₁.length_le; omega
    have hl2 : u₂.length + v₂.length ≤ m := by
      have := hu₂.length_le; have := hv₂.length_le; omega
    have ea : Dw (wL u₁ ++ wR v₁) (fun x => lcomp (Wp := Wp) (Wq := Wq) (A x)) g =
        lcomp (Dw (wL u₁ ++ wR v₁) A g) :=
      Dw_clm lcomp _ (lie_LR (fun X hX => (hu X (hu₁.subset hX)).1) (fun X hX => (hw X (hv₁.subset hX)).1)) hA g hg
    have b1 : ‖Dw (wL u₁ ++ wR v₁) (fun x => lcomp (Wp := Wp) (Wq := Wq) (A x)) g‖ ≤
        ‖lcomp (Wp := Wp) (Wq := Wq)‖ * (max Ca 0 * B.gN g ^ κ) := by
      rw [ea]
      refine (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
      rw [← dLR_eq]
      exact (hCa u₁ v₁ (fun X hX => hu X (hu₁.subset hX)) (fun X hX => hw X (hv₁.subset hX)) hl1 g hg).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hg0.le _))
    have b2 : ‖Dw (wL u₂ ++ wR v₂) Φ g‖ ≤ max Cb 0 * B.gN g ^ d := by
      rw [← dLR_eq]
      exact (hCb u₂ v₂ (fun X hX => hu X (hu₂.subset hX)) (fun X hX => hw X (hv₂.subset hX)) hl2 g hg).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hg0.le _))
    exact mul_le_mul b1 b2 (norm_nonneg _) (by positivity)
  have hb := leib_bound isOpen_empty (fun g hg => Or.inr hg) g hg _ (wL u ++ wR w) _ Φ hlie hPr hM
  have hlen : (wL u ++ wR w).length ≤ m := by simp [wL, wR]; omega
  have h2 : (2 : ℝ) ^ (wL u ++ wR w).length ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) hlen
  rw [Real.rpow_add hg0]
  calc ‖Dw (wL u ++ wR w) (ap (fun x => lcomp (Wp := Wp) (Wq := Wq) (A x)) Φ) g‖
      ≤ 2 ^ (wL u ++ wR w).length *
        ((‖lcomp (Wp := Wp) (Wq := Wq)‖ * (max Ca 0 * B.gN g ^ κ)) * (max Cb 0 * B.gN g ^ d)) := hb
    _ ≤ 2 ^ m * ((‖lcomp (Wp := Wp) (Wq := Wq)‖ * (max Ca 0 * B.gN g ^ κ)) * (max Cb 0 * B.gN g ^ d)) :=
        mul_le_mul_of_nonneg_right h2 (by positivity)
    _ = 2 ^ m * ‖lcomp (Wp := Wp) (Wq := Wq)‖ * max Ca 0 * max Cb 0 * (B.gN g ^ κ * B.gN g ^ d) := by ring

theorem smul_eq_comp (z : ℂ) (Φ : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) :
    z • Φ = (z • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)).comp Φ := by
  ext A x
  simp

end term

theorem deg_le (C : ℝ) (P : M.Par) (N : ℕ) :
    (((2 * P.r + 2) * N : ℕ) : ℝ) + C * ((P.r : ℝ) + 1) * CutMP.nDim P.k P.r * ((N : ℝ) + 1) ≤
      (max C 0 + 2) * ((P.r : ℝ) + 1) * CutMP.nDim P.k P.r * ((N : ℝ) + 1) := by
  unfold CutMP.nDim
  have e : (((2 * P.r + 2) * N : ℕ) : ℝ) = (2 * (P.r : ℝ) + 2) * N := by push_cast; ring
  rw [e]
  set n := ((2 * P.r + P.k + 1 : ℕ) : ℝ) with hn_def
  have hn : 1 ≤ n := by
    rw [hn_def]
    exact_mod_cast (by omega : 1 ≤ 2 * P.r + P.k + 1)
  have hr : (0 : ℝ) ≤ P.r := Nat.cast_nonneg _
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hX : 0 ≤ ((P.r : ℝ) + 1) * n * ((N : ℝ) + 1) := by
    have : 0 ≤ n := by linarith
    positivity
  have h1 : C * (((P.r : ℝ) + 1) * n * ((N : ℝ) + 1)) ≤ max C 0 * (((P.r : ℝ) + 1) * n * ((N : ℝ) + 1)) :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) hX
  have h2 : 1 * ((N : ℝ) + 1) ≤ n * ((N : ℝ) + 1) := mul_le_mul_of_nonneg_right hn (by positivity)
  have h3 : ((P.r : ℝ) + 1) * N ≤ ((P.r : ℝ) + 1) * (n * ((N : ℝ) + 1)) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  linarith [h1, h3]

def gpow {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) (N : ℕ) (g : B.Mat P.k P.r) : ℂ :=
  ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ N : ℝ) : ℂ)

theorem operator_multiplication_admissible : NFOpOKMulG := by
  intro C
  refine ⟨max C 0 + 2, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p N Th hTh
  obtain ⟨hS, hCm, hG, hO⟩ := hTh
  have hpoly : U.IsPolyDeg ((2 * P.r + 2) * N) (gpow p N) := by
    have h := nf_isPolyDeg_pow (Formalism.FourierDecayAlt.P.gram_function_polynomial P.k P.r p.T.base.z p.T.base.z') N
    refine ⟨h.choose, h.choose_spec.1, fun g => ?_⟩
    rw [← h.choose_spec.2 g]; unfold gpow; push_cast; rfl
  obtain ⟨hsA, hgA, -⟩ := CutMP.polynomial_decay_admissible P.k P.r Wp Wq 0 ((2 * P.r + 2) * N)
    (nfMulOp (Wp := Wp) (Wq := Wq) (gpow p N)) (nfMulOp_poly hpoly)
  have hlen0 : 0 < (nfMulOp (Wp := Wp) (Wq := Wq) (gpow p N)).length := by simp [nfMulOp]
  have hT0 := List.getElem_mem hlen0
  have hT0c : ((nfMulOp (Wp := Wp) (Wq := Wq) (gpow p N))[0]'hlen0).coef =
      fun g => gpow p N g • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp) := rfl
  have hA_ck : ∀ UU : Set (B.Mat P.k P.r),
      B.CkOn ⊤ UU (fun g => gpow p N g • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)) := by
    intro UU; rw [← hT0c]; exact ((hsA UU) _ hT0).1
  have hA_glob := ((hgA (((2 * P.r + 2) * N : ℕ) : ℝ) le_rfl) _ hT0).2.2
  rw [hT0c] at hA_glob
  have hcoef : ∀ (X : B.Mat P.k P.r → ((Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp))),
      (fun g => ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ N : ℝ) : ℂ) • X g) =
        fun g => (gpow p N g • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)).comp (X g) := by
    intro X; funext g; exact smul_eq_comp _ _
  refine ⟨mulOpG (fun g => Gf P.k P.r p.T.base.z p.T.base.z' g ^ N) Th, ⟨?_, ?_, ?_, ?_⟩,
    fun F g => mulOpG_apply _ Th F g⟩
  · intro T' hT'
    obtain ⟨T, hT, rfl⟩ := List.mem_map.1 hT'
    refine ⟨?_, ?_⟩
    · show B.CkOn ⊤ _ (fun g => ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ N : ℝ) : ℂ) • T.coef g)
      rw [hcoef]; exact ckOn_apply (ckOn_clm lcomp (hA_ck _)) (hS T hT).1
    · show B.CkOn ⊤ _ (fun g => ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ N : ℝ) : ℂ) • T.coefAdj g)
      rw [hcoef]; exact ckOn_apply (ckOn_clm lcomp (hA_ck _)) (hS T hT).2
  · intro pp hpp f hf g hg
    rw [mulOpG_order] at hf
    have hfun : B.opApply (mulOpG (fun g => Gf P.k P.r p.T.base.z p.T.base.z' g ^ N) Th) f =
        fun x => ((Gf P.k P.r p.T.base.z p.T.base.z' x ^ N : ℝ) : ℂ) • B.opApply Th f x :=
      funext (mulOpG_apply _ Th f)
    rw [mulOpG_apply, hCm pp hpp f hf g hg, hfun]
    unfold B.rho
    rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, TBBx2.Gf_sgs p.T.base pp hpp g]
  · intro T' hT'
    obtain ⟨T, hT, rfl⟩ := List.mem_map.1 hT'
    obtain ⟨hTc, hTa, hTb⟩ := hG T hT
    refine ⟨?_, ?_, fun m => ?_⟩
    · show B.CkOn ⊤ _ (fun g => ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ N : ℝ) : ℂ) • T.coef g)
      rw [hcoef]; exact ckOn_apply (ckOn_clm lcomp (hA_ck _)) hTc
    · show B.CkOn ⊤ _ (fun g => ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ N : ℝ) : ℂ) • T.coefAdj g)
      rw [hcoef]; exact ckOn_apply (ckOn_clm lcomp (hA_ck _)) hTa
    obtain ⟨Ca, hCa⟩ := hA_glob m
    obtain ⟨Cb, hCb⟩ := hTb m
    refine ⟨2 ^ m * ‖lcomp (Wp := Wp) (Wq := Wq)‖ * max Ca 0 * max Cb 0, fun u w hu hw hl g hg => ?_⟩
    have hg1 : 1 ≤ B.gN g := gN_ge_one hg
    have hdeg := deg_le C P N
    have hpow : B.gN g ^ ((((2 * P.r + 2) * N : ℕ) : ℝ) + C * ((P.r : ℝ) + 1) * CutMP.nDim P.k P.r * ((N : ℝ) + 1)) ≤
        B.gN g ^ ((max C 0 + 2) * ((P.r : ℝ) + 1) * CutMP.nDim P.k P.r * ((N : ℝ) + 1)) :=
      Real.rpow_le_rpow_of_exponent_le hg1 hdeg
    have hK : 0 ≤ 2 ^ m * ‖lcomp (Wp := Wp) (Wq := Wq)‖ * max Ca 0 * max Cb 0 := by positivity
    constructor
    · show ‖B.dLR u w (fun g => ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ N : ℝ) : ℂ) • T.coef g) g‖ ≤ _
      rw [hcoef]
      exact (comp_bound (hA_ck _) hTc m Ca Cb _ _ (fun u w hu hw hl g hg => (hCa u w hu hw hl g hg).1)
        (fun u w hu hw hl g hg => (hCb u w hu hw hl g hg).1) u w hu hw hl g hg).trans
        (mul_le_mul_of_nonneg_left hpow hK)
    · show ‖B.dLR u w (fun g => ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ N : ℝ) : ℂ) • T.coefAdj g) g‖ ≤ _
      rw [hcoef]
      exact (comp_bound (hA_ck _) hTa m Ca Cb _ _ (fun u w hu hw hl g hg => (hCa u w hu hw hl g hg).1)
        (fun u w hu hw hl g hg => (hCb u w hu hw hl g hg).2) u w hu hw hl g hg).trans
        (mul_le_mul_of_nonneg_left hpow hK)
  · rw [mulOpG_order]
    have h1 : C * CutMP.nDim P.k P.r * ((N : ℝ) + 1) ≤ (max C 0 + 2) * CutMP.nDim P.k P.r * ((N : ℝ) + 1) := by
      have hn : (0 : ℝ) ≤ CutMP.nDim P.k P.r := by unfold CutMP.nDim; positivity
      have hN : (0 : ℝ) ≤ (N : ℝ) + 1 := by positivity
      have : C ≤ max C 0 + 2 := by have := le_max_left C 0; linarith
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right this hn) hN
    exact hO.trans h1

end

end Formalism.FourierDecayAlt.P.CutBP
