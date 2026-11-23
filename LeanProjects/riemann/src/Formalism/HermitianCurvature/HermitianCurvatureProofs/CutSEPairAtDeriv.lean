import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSELeib

open MeasureTheory Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.P5.HerB Formalism.FourierDecayAlt.P5.HerC
  Formalism.FourierDecayAlt.P5.HerD

section Lin

variable {r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem pi_single_decomp (l : Fin r) (h : ℂ) :
    (Pi.single l h : Fin r → ℂ) = h.re • (Pi.single l 1 : Fin r → ℂ) + h.im • (Pi.single l Complex.I : Fin r → ℂ) := by
  ext i
  by_cases hi : i = l
  · subst hi
    simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same]
    rw [Complex.real_smul, Complex.real_smul, mul_one]
    exact (Complex.re_add_im h).symm
  · simp [Pi.single_eq_of_ne hi]

theorem clm_single_wirt (L : (Fin r → ℂ) →L[ℝ] E) (l : Fin r) (h : ℂ) :
    L (Pi.single l h) = h • ((1 / 2 : ℂ) • (L (Pi.single l 1) - Complex.I • L (Pi.single l Complex.I))) +
      conj h • ((1 / 2 : ℂ) • (L (Pi.single l 1) + Complex.I • L (Pi.single l Complex.I))) := by
  rw [pi_single_decomp l h, map_add, map_smul, map_smul]
  rw [← Complex.coe_smul, ← Complex.coe_smul]
  simp only [smul_add, smul_sub, smul_smul]
  match_scalars
  · apply Complex.ext <;> simp <;> ring
  · apply Complex.ext <;> simp <;> ring

end Lin

def dSl {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (A B : E) : ℂ →L[ℝ] E :=
  (ContinuousLinearMap.id ℝ ℂ).smulRight A + Complex.conjCLE.toContinuousLinearMap.smulRight B

theorem dSl_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (A B : E) (h : ℂ) :
    dSl A B h = h • A + conj h • B := rfl

theorem glue_succ_update_eq {r : ℕ} (l : Fin r) (c : Fin r → ℂ) (s : ℂ) (c' : Cf r l.succ) :
    glue l.succ (Function.update c l s) c' = Function.update (glue l.succ c c') l s := by
  funext j
  by_cases hj : j = l
  · subst hj
    have : ¬ (j.succ.val ≤ j.val) := by simp [Fin.val_succ]
    simp [glue, this]
  · rw [Function.update_of_ne hj]
    unfold glue
    split_ifs <;> simp [Function.update_of_ne hj]

theorem omX_update_iff {r : ℕ} (y : Fin r → ℂ) (l : Fin r) {s s' : ℂ} (hs : s ≠ 0) (hs' : s' ≠ 0) :
    Function.update y l s ∈ OmX r ↔ Function.update y l s' ∈ OmX r := by
  simp only [OmX, Set.mem_setOf_eq]
  constructor
  · intro h i
    by_cases hi : i = l
    · subst hi
      simpa using hs'
    · have h1 := h i
      rwa [Function.update_of_ne hi] at h1 ⊢
  · intro h i
    by_cases hi : i = l
    · subst hi
      simpa using hs
    · have h1 := h i
      rwa [Function.update_of_ne hi] at h1 ⊢

theorem omX_update_any {r : ℕ} (y : Fin r → ℂ) (l : Fin r) {t : ℂ} (ht : t ≠ 0)
    (h : Function.update y l t ∉ OmX r) (s : ℂ) : Function.update y l s ∉ OmX r := by
  by_cases hs : s = 0
  · subst hs
    intro hm
    exact hm l (by simp)
  · exact fun hm => h ((omX_update_iff y l ht hs).2 hm)

section Pt

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
  [FiniteDimensional ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem dT_apply (X : ActualOps k r z z' π π') (l : Fin r) (Φ : RadSp k r z z' π π') {x : Fin r → ℂ}
    (hx : x ∈ OmX r) (g : Mx k r) :
    (dT X l Φ : Fn k r (Wq →L[ℂ] Wp)) x g = Formalism.QuantumDeterminants.wirt l (fun x' => (Φ : Fn k r (Wq →L[ℂ] Wp)) x' g) x := by
  simp only [dT, Module.End.mul_apply, ActualOps.op_apply, crd, opL, ciOp, pOp, if_pos hx]
  rw [smul_smul, inv_mul_cancel₀ (hx l), one_smul]

theorem dTb_apply (X : ActualOps k r z z' π π') (l : Fin r) (Φ : RadSp k r z z' π π') {x : Fin r → ℂ}
    (hx : x ∈ OmX r) (g : Mx k r) :
    (dTb X l Φ : Fn k r (Wq →L[ℂ] Wp)) x g = Formalism.QuantumDeterminants.wirtBar l (fun x' => (Φ : Fn k r (Wq →L[ℂ] Wp)) x' g) x := by
  have hs : star (x l) ≠ 0 := by simpa using hx l
  simp only [dTb, Module.End.mul_apply, ActualOps.op_apply, crd, opL, cbiOp, pbOp, if_pos hx]
  rw [smul_smul, inv_mul_cancel₀ hs, one_smul]

theorem slice_hasFDerivAt (X : ActualOps k r z z' π π') (l : Fin r) (Φ : RadSp k r z z' π π') (y : Fin r → ℂ)
    (g : Mx k r) {s : ℂ} (hs : s ≠ 0) :
    HasFDerivAt (fun s' => (Φ : Fn k r (Wq →L[ℂ] Wp)) (Function.update y l s') g)
      (dSl ((dT X l Φ : Fn k r (Wq →L[ℂ] Wp)) (Function.update y l s) g)
        ((dTb X l Φ : Fn k r (Wq →L[ℂ] Wp)) (Function.update y l s) g)) s := by
  by_cases hD : (Function.update y l s, g) ∈ DomR k r z z'
  · set x := Function.update y l s with hxdef
    obtain ⟨-, hsm, -⟩ := Φ.2
    obtain ⟨U, F, hU, hxU, hF, hΦ⟩ := hsm (x, g) hD
    have hpc : Continuous (fun x' : Fin r → ℂ => (x', g)) := continuous_id.prodMk continuous_const
    have hev : (fun x' => (Φ : Fn k r (Wq →L[ℂ] Wp)) x' g) =ᶠ[𝓝 x] fun x' => F (x', g) := by
      filter_upwards [hpc.continuousAt.preimage_mem_nhds (hU.mem_nhds hxU)] with x' hx'
      exact hΦ (x', g) hx' hD.2.1
    have hFd : DifferentiableAt ℝ (fun x' => F (x', g)) x := by
      have h1 : DifferentiableAt ℝ F (x, g) :=
        (hF.contDiffAt (hU.mem_nhds hxU)).differentiableAt (by simp)
      exact h1.comp x (differentiableAt_id.prodMk (differentiableAt_const _))
    have hf : HasFDerivAt (fun x' => (Φ : Fn k r (Wq →L[ℂ] Wp)) x' g)
        (fderiv ℝ (fun x' => (Φ : Fn k r (Wq →L[ℂ] Wp)) x' g) x) x :=
      (hFd.hasFDerivAt.congr_of_eventuallyEq hev).differentiableAt.hasFDerivAt
    have hc := hf.comp s (hasFDerivAt_update (𝕜 := ℝ) y s)
    refine hc.congr_fderiv ?_
    have hxO : x ∈ OmX r := hD.1
    ext1 h
    rw [dSl_apply, dT_apply X l Φ hxO, dTb_apply X l Φ hxO, ContinuousLinearMap.comp_apply]
    symm
    have hp : (ContinuousLinearMap.pi (Pi.single l (ContinuousLinearMap.id ℝ ℂ)) : ℂ →L[ℝ] (Fin r → ℂ)) h =
        Pi.single l h := by
      ext j
      by_cases hj : j = l
      · subst hj; simp
      · simp [Pi.single_eq_of_ne hj]
    rw [hp, clm_single_wirt]
    simp only [Formalism.QuantumDeterminants.wirt, Formalism.QuantumDeterminants.wirtBar]
  · have hx0 : ∀ s', s' ≠ 0 → (Φ : Fn k r (Wq →L[ℂ] Wp)) (Function.update y l s') g = 0 := by
      intro s' hs'
      refine radSp_zero_off Φ (x := (Function.update y l s', g)) fun h => hD ?_
      exact ⟨(omX_update_iff y l hs hs').2 h.1, h.2⟩
    have hT : (dT X l Φ : Fn k r (Wq →L[ℂ] Wp)) (Function.update y l s) g = 0 :=
      radSp_zero_off (dT X l Φ) (x := (Function.update y l s, g)) hD
    have hTb : (dTb X l Φ : Fn k r (Wq →L[ℂ] Wp)) (Function.update y l s) g = 0 :=
      radSp_zero_off (dTb X l Φ) (x := (Function.update y l s, g)) hD
    rw [hT, hTb]
    have e0 : dSl (0 : Wq →L[ℂ] Wp) 0 = 0 := by ext1 h; simp [dSl_apply]
    rw [e0]
    refine (hasFDerivAt_const (0 : Wq →L[ℂ] Wp) s).congr_of_eventuallyEq ?_
    filter_upwards [isOpen_ne.mem_nhds hs] with s' hs'
    exact hx0 s' hs'

end Pt

section Main

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
  [FiniteDimensional ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

omit [FiniteDimensional ℂ Wp] in
theorem hsVec_add' (A A' : Wq →L[ℂ] Wp) : B.hsVec (A + A') = B.hsVec A + B.hsVec A' := by
  ext i
  simp [B.hsVec]

omit [FiniteDimensional ℂ Wp] in
theorem hsVec_smul' (a : ℂ) (A : Wq →L[ℂ] Wp) : B.hsVec (a • A) = a • B.hsVec A := by
  ext i
  simp [B.hsVec]

omit [FiniteDimensional ℂ Wp] in

def hsVecLin : (Wq →L[ℂ] Wp) →ₗ[ℂ] PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp) where
  toFun := B.hsVec
  map_add' := hsVec_add'
  map_smul' := hsVec_smul'

def hsVecR : (Wq →L[ℂ] Wp) →L[ℝ] PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp) :=
  (LinearMap.toContinuousLinearMap (hsVecLin (Wp := Wp) (Wq := Wq))).restrictScalars ℝ

theorem hsVecR_apply (A : Wq →L[ℂ] Wp) : hsVecR A = B.hsVec A := rfl

theorem hsInner_hasFDerivAt {φ ψ : ℂ → (Wq →L[ℂ] Wp)} {a1 b1 a2 b2 : Wq →L[ℂ] Wp} {s : ℂ}
    (hφ : HasFDerivAt φ (dSl a1 b1) s) (hψ : HasFDerivAt ψ (dSl a2 b2) s) :
    HasFDerivAt (fun s => B.hsInner (φ s) (ψ s))
      (wl (B.hsInner a1 (ψ s) + B.hsInner (φ s) b2) (B.hsInner b1 (ψ s) + B.hsInner (φ s) a2)) s := by
  have h1 := hsVecR.hasFDerivAt.comp s hψ
  have h2 := hsVecR.hasFDerivAt.comp s hφ
  have h3 := h1.inner ℂ h2
  refine h3.congr_fderiv ?_
  ext1 h
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply, fderivInnerCLM_apply, Function.comp_apply,
    hsVecR_apply, dSl_apply, wl_apply, hsVec_add', hsVec_smul', inner_add_left, inner_add_right, inner_smul_left,
    inner_smul_right, B.hsInner, Complex.conj_conj]
  ring

theorem norm_wl_le' (A B : ℂ) : ‖wl A B‖ ≤ ‖A‖ + ‖B‖ := by
  unfold wl
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · calc ‖A • ContinuousLinearMap.id ℝ ℂ‖ ≤ ‖A‖ * ‖ContinuousLinearMap.id ℝ ℂ‖ := norm_smul_le _ _
      _ ≤ ‖A‖ * 1 := mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (norm_nonneg _)
      _ = ‖A‖ := mul_one _
  · calc ‖B • Complex.conjCLE.toContinuousLinearMap‖
        ≤ ‖B‖ * ‖(Complex.conjCLE.toContinuousLinearMap : ℂ →L[ℝ] ℂ)‖ := norm_smul_le _ _
      _ ≤ ‖B‖ * 1 := mul_le_mul_of_nonneg_left
          (ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by simp) (norm_nonneg _)
      _ = ‖B‖ := mul_one _

theorem pairAt_off (μ : Measure (Mt k r)) (Φ Ψ : RadSp k r z z' π π') (x : Fin r → ℂ) (hx : x ∉ OmX r) :
    pairAt μ Φ Ψ x = 0 := by
  unfold pairAt
  have : ∀ g : Mt k r, B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) x (Matrix.of g))
      ((Ψ : Fn k r (Wq →L[ℂ] Wp)) x (Matrix.of g)) = 0 := fun g => by
    rw [radSp_zero_off Φ (x := (x, Matrix.of g)) (fun h => hx h.1)]
    exact Formalism.FourierDecayAlt.P5.HerA.hsInner_zero_left _
  simp [this]

theorem slice_bound (Ξ1 Ξ2 : RadSp k r z z' π π') (h1 : Ξ1 ∈ lcSub k r z z' π π') (l : Fin r) (y : Fin r → ℂ)
    {t : ℂ} (ht : Function.update y l t ∈ OmX r) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : Set (Mt k r), IsCompact C ∧ ∃ M : ℝ, ∀ s ∈ Metric.ball t δ, ∀ g : Mt k r,
      ‖B.hsInner ((Ξ1 : Fn k r (Wq →L[ℂ] Wp)) (Function.update y l s) (Matrix.of g))
        ((Ξ2 : Fn k r (Wq →L[ℂ] Wp)) (Function.update y l s) (Matrix.of g))‖ ≤ C.indicator (fun _ => M) g := by
  obtain ⟨U, hU, hxU, K, hKc, hKG, hK0⟩ := h1 _ ht
  have hcu : Continuous (fun s : ℂ => Function.update y l s) := continuous_const.update l continuous_id
  have hV : IsOpen ((fun s : ℂ => Function.update y l s) ⁻¹' (U ∩ OmX r)) :=
    (hU.inter (P.Qx3.isOpen_OmX r)).preimage hcu
  obtain ⟨δ0, hδ0, hball⟩ := Metric.isOpen_iff.mp hV t ⟨hxU, ht⟩
  have hcb : Metric.closedBall t (δ0 / 2) ⊆ (fun s : ℂ => Function.update y l s) ⁻¹' (U ∩ OmX r) :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  set C : Set (Mt k r) := (fun g : Mx k r => (Matrix.of.symm g : Mt k r)) '' (K ∩ Glev k r (Fin.last r)) with hCdef
  have hCmem : ∀ g : Mt k r, g ∈ C ↔ Matrix.of g ∈ K ∧ Matrix.of g ∈ Glev k r (Fin.last r) := by
    intro g; constructor
    · rintro ⟨g', hg', rfl⟩; simpa using hg'
    · intro hg; exact ⟨Matrix.of g, hg, rfl⟩
  have hCc : IsCompact C := (hKc.inter_right (P.Qx5.Glev_closed _)).image continuous_id
  have hmap : Continuous (fun p : ℂ × Mt k r => (Function.update y l p.1, (Matrix.of p.2 : Mx k r))) :=
    (hcu.comp continuous_fst).prodMk continuous_snd
  have hmaps : Set.MapsTo (fun p : ℂ × Mt k r => (Function.update y l p.1, (Matrix.of p.2 : Mx k r)))
      (Metric.closedBall t (δ0 / 2) ×ˢ C) (DomR k r z z') := by
    rintro ⟨s, g⟩ ⟨hs, hg⟩
    have := hcb hs
    rw [hCmem] at hg
    exact ⟨this.2, hg.2, hKG hg.1⟩
  have c1 : ContinuousOn (fun p : ℂ × Mt k r => (Ξ1 : Fn k r (Wq →L[ℂ] Wp)) (Function.update y l p.1) (Matrix.of p.2))
      (Metric.closedBall t (δ0 / 2) ×ˢ C) := (radSp_continuousOn Ξ1).comp hmap.continuousOn hmaps
  have c2 : ContinuousOn (fun p : ℂ × Mt k r => (Ξ2 : Fn k r (Wq →L[ℂ] Wp)) (Function.update y l p.1) (Matrix.of p.2))
      (Metric.closedBall t (δ0 / 2) ×ˢ C) := (radSp_continuousOn Ξ2).comp hmap.continuousOn hmaps
  have hcont : ContinuousOn (fun p : ℂ × Mt k r => B.hsInner
      ((Ξ1 : Fn k r (Wq →L[ℂ] Wp)) (Function.update y l p.1) (Matrix.of p.2))
      ((Ξ2 : Fn k r (Wq →L[ℂ] Wp)) (Function.update y l p.1) (Matrix.of p.2))) (Metric.closedBall t (δ0 / 2) ×ˢ C) :=
    (Formalism.FourierDecayAlt.P.B6.hsInner_continuous (Wp := Wp) (Wq := Wq)).comp_continuousOn (c1.prodMk c2)
  obtain ⟨M, hM⟩ := ((isCompact_closedBall t (δ0 / 2)).prod hCc).exists_bound_of_continuousOn hcont
  refine ⟨δ0 / 2, by positivity, C, hCc, M, fun s hs g => ?_⟩
  by_cases hg : g ∈ C
  · rw [Set.indicator_of_mem hg]; exact hM (s, g) ⟨Metric.ball_subset_closedBall hs, hg⟩
  · rw [Set.indicator_of_notMem hg]
    have hz : (Ξ1 : Fn k r (Wq →L[ℂ] Wp)) (Function.update y l s) (Matrix.of g) = 0 := by
      by_cases hgG : Matrix.of g ∈ Glev k r (Fin.last r)
      · exact hK0 _ (hcb (Metric.ball_subset_closedBall hs)).1 _ hgG (fun hK => hg ((hCmem g).2 ⟨hK, hgG⟩))
      · exact radSp_zero_off Ξ1 (x := (Function.update y l s, Matrix.of g)) (fun h => hgG h.2.1)
    rw [hz, Formalism.FourierDecayAlt.P5.HerA.hsInner_zero_left, norm_zero]

theorem pairAt_hasFDerivAt (X : ActualOps k r z z' π π') (μ : Measure (Mt k r))
    (hμ : B.IsHaarOn (Glev k r (Fin.last r)) μ) (l : Fin r) (Φ Ψ : RadSp k r z z' π π')
    (hΦ : Φ ∈ lcSub k r z z' π π') (hΨ : Ψ ∈ lcSub k r z z' π π') (y : Fin r → ℂ) {t : ℂ} (ht : t ≠ 0)
    (hyO : Function.update y l t ∈ OmX r) :
    HasFDerivAt (fun s => pairAt μ Φ Ψ (Function.update y l s))
      (wl (pairAt μ (dT X l Φ) Ψ (Function.update y l t) + pairAt μ Φ (dTb X l Ψ) (Function.update y l t))
        (pairAt μ (dTb X l Φ) Ψ (Function.update y l t) + pairAt μ Φ (dT X l Ψ) (Function.update y l t))) t := by
  have hTΦ : dT X l Φ ∈ lcSub k r z z' π π' := op_lc X l 2 _ (op_lc X l 0 _ hΦ)
  have hTbΦ : dTb X l Φ ∈ lcSub k r z z' π π' := op_lc X l 5 _ (op_lc X l 3 _ hΦ)
  have hTΨ : dT X l Ψ ∈ lcSub k r z z' π π' := op_lc X l 2 _ (op_lc X l 0 _ hΨ)
  have hTbΨ : dTb X l Ψ ∈ lcSub k r z z' π π' := op_lc X l 5 _ (op_lc X l 3 _ hΨ)
  obtain ⟨δ1, hδ1, C1, hC1, M1, hB1⟩ := slice_bound (dT X l Φ) Ψ hTΦ l y hyO
  obtain ⟨δ2, hδ2, C2, hC2, M2, hB2⟩ := slice_bound Φ (dTb X l Ψ) hΦ l y hyO
  obtain ⟨δ3, hδ3, C3, hC3, M3, hB3⟩ := slice_bound (dTb X l Φ) Ψ hTbΦ l y hyO
  obtain ⟨δ4, hδ4, C4, hC4, M4, hB4⟩ := slice_bound Φ (dT X l Ψ) hΦ l y hyO
  have htn : 0 < ‖t‖ := norm_pos_iff.2 ht
  set δ : ℝ := min (min (min δ1 δ2) (min δ3 δ4)) ‖t‖ with hδdef
  have hδ : 0 < δ := lt_min (lt_min (lt_min hδ1 hδ2) (lt_min hδ3 hδ4)) htn
  have hb : ∀ s ∈ Metric.ball t δ, s ∈ Metric.ball t δ1 ∧ s ∈ Metric.ball t δ2 ∧ s ∈ Metric.ball t δ3 ∧
      s ∈ Metric.ball t δ4 ∧ s ≠ 0 := by
    intro s hs
    have hs' : dist s t < δ := hs
    have e1 : δ ≤ δ1 := (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
    have e2 : δ ≤ δ2 := (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
    have e3 : δ ≤ δ3 := (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    have e4 : δ ≤ δ4 := (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
    have e5 : δ ≤ ‖t‖ := min_le_right _ _
    refine ⟨lt_of_lt_of_le hs' e1, lt_of_lt_of_le hs' e2, lt_of_lt_of_le hs' e3, lt_of_lt_of_le hs' e4, ?_⟩
    rintro rfl
    rw [dist_comm, dist_zero_right] at hs'
    linarith
  have iA : Integrable (fun g : Mt k r =>
      B.hsInner ((dT X l Φ : Fn k r (Wq →L[ℂ] Wp)) (Function.update y l t) (Matrix.of g))
          ((Ψ : Fn k r (Wq →L[ℂ] Wp)) (Function.update y l t) (Matrix.of g)) +
        B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) (Function.update y l t) (Matrix.of g))
          ((dTb X l Ψ : Fn k r (Wq →L[ℂ] Wp)) (Function.update y l t) (Matrix.of g))) μ :=
    (int_lc μ hμ hTΦ hΨ _).add (int_lc μ hμ hΦ hTbΨ _)
  have iB : Integrable (fun g : Mt k r =>
      B.hsInner ((dTb X l Φ : Fn k r (Wq →L[ℂ] Wp)) (Function.update y l t) (Matrix.of g))
          ((Ψ : Fn k r (Wq →L[ℂ] Wp)) (Function.update y l t) (Matrix.of g)) +
        B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) (Function.update y l t) (Matrix.of g))
          ((dT X l Ψ : Fn k r (Wq →L[ℂ] Wp)) (Function.update y l t) (Matrix.of g))) μ :=
    (int_lc μ hμ hTbΦ hΨ _).add (int_lc μ hμ hΦ hTΨ _)
  have iC : ∀ (C : Set (Mt k r)) (M : ℝ), IsCompact C → Integrable (fun g : Mt k r => C.indicator (fun _ => M) g) μ :=
    fun C M hC => (integrable_indicator_iff hC.measurableSet).mpr (integrableOn_const (hμ.finite_compact C hC).ne)
  have key := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := μ) (𝕜 := ℝ)
    (F := fun s (g : Mt k r) => B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) (Function.update y l s) (Matrix.of g))
      ((Ψ : Fn k r (Wq →L[ℂ] Wp)) (Function.update y l s) (Matrix.of g)))
    (F' := fun s (g : Mt k r) => wl
      (B.hsInner ((dT X l Φ : Fn k r (Wq →L[ℂ] Wp)) (Function.update y l s) (Matrix.of g))
          ((Ψ : Fn k r (Wq →L[ℂ] Wp)) (Function.update y l s) (Matrix.of g)) +
        B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) (Function.update y l s) (Matrix.of g))
          ((dTb X l Ψ : Fn k r (Wq →L[ℂ] Wp)) (Function.update y l s) (Matrix.of g)))
      (B.hsInner ((dTb X l Φ : Fn k r (Wq →L[ℂ] Wp)) (Function.update y l s) (Matrix.of g))
          ((Ψ : Fn k r (Wq →L[ℂ] Wp)) (Function.update y l s) (Matrix.of g)) +
        B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) (Function.update y l s) (Matrix.of g))
          ((dT X l Ψ : Fn k r (Wq →L[ℂ] Wp)) (Function.update y l s) (Matrix.of g))))
    (x₀ := t)
    (bound := fun g => (C1.indicator (fun _ => M1) g + C2.indicator (fun _ => M2) g) +
      (C3.indicator (fun _ => M3) g + C4.indicator (fun _ => M4) g))
    (s := Metric.ball t δ) (Metric.ball_mem_nhds t hδ)
    (Filter.Eventually.of_forall fun s => (int_lc μ hμ hΦ hΨ _).aestronglyMeasurable)
    (int_lc μ hμ hΦ hΨ _)
    ((iA.aestronglyMeasurable.smul_const (ContinuousLinearMap.id ℝ ℂ)).add
      (iB.aestronglyMeasurable.smul_const Complex.conjCLE.toContinuousLinearMap))
    (Filter.Eventually.of_forall fun g s hs => by
      obtain ⟨h1, h2, h3, h4, -⟩ := hb s hs
      refine (norm_wl_le' _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add (hB1 s h1 g) (hB2 s h2 g)))
        ((norm_add_le _ _).trans (add_le_add (hB3 s h3 g) (hB4 s h4 g)))))
    (((iC C1 M1 hC1).add (iC C2 M2 hC2)).add ((iC C3 M3 hC3).add (iC C4 M4 hC4)))
    (Filter.Eventually.of_forall fun g s hs => by
      obtain ⟨-, -, -, -, hs0⟩ := hb s hs
      exact hsInner_hasFDerivAt (slice_hasFDerivAt X l Φ y (Matrix.of g) hs0)
        (slice_hasFDerivAt X l Ψ y (Matrix.of g) hs0))
  have hint : ∫ g, wl
      (B.hsInner ((dT X l Φ : Fn k r (Wq →L[ℂ] Wp)) (Function.update y l t) (Matrix.of g))
          ((Ψ : Fn k r (Wq →L[ℂ] Wp)) (Function.update y l t) (Matrix.of g)) +
        B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) (Function.update y l t) (Matrix.of g))
          ((dTb X l Ψ : Fn k r (Wq →L[ℂ] Wp)) (Function.update y l t) (Matrix.of g)))
      (B.hsInner ((dTb X l Φ : Fn k r (Wq →L[ℂ] Wp)) (Function.update y l t) (Matrix.of g))
          ((Ψ : Fn k r (Wq →L[ℂ] Wp)) (Function.update y l t) (Matrix.of g)) +
        B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) (Function.update y l t) (Matrix.of g))
          ((dT X l Ψ : Fn k r (Wq →L[ℂ] Wp)) (Function.update y l t) (Matrix.of g))) ∂μ =
      wl (pairAt μ (dT X l Φ) Ψ (Function.update y l t) + pairAt μ Φ (dTb X l Ψ) (Function.update y l t))
        (pairAt μ (dTb X l Φ) Ψ (Function.update y l t) + pairAt μ Φ (dT X l Ψ) (Function.update y l t)) := by
    unfold wl
    rw [integral_add (iA.smul_const _) (iB.smul_const _), integral_smul_const, integral_smul_const,
      integral_add (int_lc μ hμ hTΦ hΨ _) (int_lc μ hμ hΦ hTbΨ _),
      integral_add (int_lc μ hμ hTbΦ hΨ _) (int_lc μ hμ hΦ hTΨ _)]
    rfl
  rw [hint] at key
  exact key

theorem pairing_derivative_formula : PairAtDeriv := by
  intro k r z z' Wp Wq _ _ _ _ _ _ π π' X μ hμ l Φ Ψ hΦ hΨ c hc c' t ht
  simp only [glue_succ_update_eq]
  set y := glue l.succ c c'
  by_cases hyO : Function.update y l t ∈ OmX r
  · exact pairAt_hasFDerivAt X μ hμ l Φ Ψ hΦ hΨ y ht hyO
  · have hoff : ∀ s, Function.update y l s ∉ OmX r := omX_update_any y l ht hyO
    have hfun : (fun s => pairAt μ Φ Ψ (Function.update y l s)) = fun _ => (0 : ℂ) :=
      funext fun s => pairAt_off μ Φ Ψ _ (hoff s)
    rw [hfun, pairAt_off μ (dT X l Φ) Ψ _ (hoff t), pairAt_off μ Φ (dTb X l Ψ) _ (hoff t),
      pairAt_off μ (dTb X l Φ) Ψ _ (hoff t), pairAt_off μ Φ (dT X l Ψ) _ (hoff t)]
    have hwl : wl (0 + 0) (0 + 0) = 0 := by
      ext x
      simp [wl]
    rw [hwl]
    exact hasFDerivAt_const 0 t

end Main

end Formalism.FourierDecayAlt.P.CutSE
