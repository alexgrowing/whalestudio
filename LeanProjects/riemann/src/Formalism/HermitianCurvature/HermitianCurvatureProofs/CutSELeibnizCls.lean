import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSELeib
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WaveOperatorLeL2Subspace
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSEOuterLeib
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSEPairAtDeriv

open MeasureTheory Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.P5.HerB Formalism.FourierDecayAlt.P5.HerC
  Formalism.FourierDecayAlt.P5.HerD

section Clos

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
  [FiniteDimensional ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}
  (X : ActualOps k r z z' π π') (μ : Measure (Mt k r)) (l : Fin r) (c : Fin r → ℂ)

theorem wOp_cons (j : Fin 6) (js : List (Fin 6)) (Φ : RadSp k r z z' π π') :
    wOp X l (j :: js) Φ = X.op l j (wOp X l js Φ) := by
  simp only [wOp, List.map_cons, List.prod_cons]
  rfl

theorem wOp_nil_sg (Φ : RadSp k r z z' π π') : wOp X l [] Φ = Φ := by
  simp only [wOp, List.map_nil, List.prod_nil]
  rfl

theorem wOp_op (js : List (Fin 6)) (j : Fin 6) (Φ : RadSp k r z z' π π') :
    wOp X l js (X.op l j Φ) = wOp X l (js ++ [j]) Φ := by
  simp only [wOp, List.map_append, List.map_cons, List.map_nil, List.prod_append, List.prod_cons,
    List.prod_nil, _root_.mul_one]
  rfl

theorem wOp_lc (js : List (Fin 6)) : ∀ Φ ∈ lcSub k r z z' π π', wOp X l js Φ ∈ lcSub k r z z' π π' := by
  intro Φ hΦ
  induction js with
  | nil => rwa [wOp_nil_sg]
  | cons j js ih =>
    rw [wOp_cons]
    exact Formalism.FourierDecayAlt.P5.HerC.op_lc X l j _ ih

theorem slDom_zero : SlDom μ l c (0 : RadSp k r z z' π π') := by
  have hz : B.hsInner (0 : Wq →L[ℂ] Wp) 0 = 0 := by
    unfold B.hsInner
    rw [show B.hsVec (0 : Wq →L[ℂ] Wp) = 0 from map_zero hsVecLin, inner_zero_left]
  have h0 : ∀ p : Fin r → ℂ, pairAt μ (0 : RadSp k r z z' π π') 0 p = 0 := fun p => by
    unfold pairAt
    simp only [Submodule.coe_zero, ZeroMemClass.coe_zero, Pi.zero_apply, hz, integral_zero]
  intro t0 _
  refine ⟨1, one_pos, fun _ => 0, integrable_zero _ _ _, fun t _ c' => ?_⟩
  rw [h0, mul_zero, norm_zero]

theorem slDom_add (hμ : B.IsHaarOn (Glev k r (Fin.last r)) μ) {Φ Ψ : RadSp k r z z' π π'}
    (hΦ : Φ ∈ lcSub k r z z' π π') (hΨ : Ψ ∈ lcSub k r z z' π π') (h1 : SlDom μ l c Φ) (h2 : SlDom μ l c Ψ) :
    SlDom μ l c (Φ + Ψ) := by
  haveI : IsFiniteMeasureOnCompacts μ := ⟨hμ.finite_compact⟩
  haveI : SFinite μ := by
    first
      | infer_instance
      | exact (sigmaFinite_of_locallyFinite (μ := μ)).toSFinite

  have hconj : ∀ (A C : RadSp k r z z' π π') p, pairAt μ A C p = starRingEnd ℂ (pairAt μ C A p) := by
    intro A C p
    unfold pairAt
    rw [← integral_conj]
    congr 1
    funext x
    unfold B.hsInner
    rw [inner_conj_symm]
  have hpos : ∀ (A : RadSp k r z z' π π') p, ∃ s : ℝ, 0 ≤ s ∧ pairAt μ A A p = s := by
    intro A p
    refine ⟨∫ x, ‖B.hsVec ((A : Fn k r (Wq →L[ℂ] Wp)) p (Matrix.of x))‖ ^ 2 ∂μ,
      integral_nonneg fun _ => by positivity, ?_⟩
    unfold pairAt B.hsInner
    first
      | rw [← integral_complex_ofReal]
      | rw [← integral_ofReal]
      | rw [← integral_coe]
    congr 1
    funext x
    rw [inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  have hadd : ∀ (A1 A2 C : RadSp k r z z' π π') p, A1 ∈ lcSub k r z z' π π' → A2 ∈ lcSub k r z z' π π' →
      C ∈ lcSub k r z z' π π' → pairAt μ (A1 + A2) C p = pairAt μ A1 C p + pairAt μ A2 C p :=
    fun A1 A2 C p h1 h2 h3 => pairAt_add_left_lc (μ := μ) hμ h1 h2 h3 p
  have hsub : ∀ (A1 A2 C : RadSp k r z z' π π') p, A1 ∈ lcSub k r z z' π π' → A2 ∈ lcSub k r z z' π π' →
      C ∈ lcSub k r z z' π π' → pairAt μ (A1 - A2) C p = pairAt μ A1 C p - pairAt μ A2 C p := by
    intro A1 A2 C p h1 h2 h3
    have h := hadd (A1 - A2) A2 C p (sub_mem h1 h2) h2 h3
    rw [sub_add_cancel] at h
    rw [h]
    ring
  have hkey : ∀ p, ‖pairAt μ (Φ + Ψ) (Φ + Ψ) p‖ ≤ 2 * ‖pairAt μ Φ Φ p‖ + 2 * ‖pairAt μ Ψ Ψ p‖ := by
    intro p
    have hs := hadd Φ Ψ (Φ + Ψ) p hΦ hΨ (add_mem hΦ hΨ)
    have hd := hsub Φ Ψ (Φ - Ψ) p hΦ hΨ (sub_mem hΦ hΨ)
    have e1 : pairAt μ Φ (Φ + Ψ) p = pairAt μ Φ Φ p + pairAt μ Φ Ψ p := by
      rw [hconj, hadd Φ Ψ Φ p hΦ hΨ hΦ, map_add, ← hconj, ← hconj]
    have e2 : pairAt μ Ψ (Φ + Ψ) p = pairAt μ Ψ Φ p + pairAt μ Ψ Ψ p := by
      rw [hconj, hadd Φ Ψ Ψ p hΦ hΨ hΨ, map_add, ← hconj, ← hconj]
    have e3 : pairAt μ Φ (Φ - Ψ) p = pairAt μ Φ Φ p - pairAt μ Φ Ψ p := by
      rw [hconj, hsub Φ Ψ Φ p hΦ hΨ hΦ, map_sub, ← hconj, ← hconj]
    have e4 : pairAt μ Ψ (Φ - Ψ) p = pairAt μ Ψ Φ p - pairAt μ Ψ Ψ p := by
      rw [hconj, hsub Φ Ψ Ψ p hΦ hΨ hΨ, map_sub, ← hconj, ← hconj]
    obtain ⟨s1, hs1, q1⟩ := hpos (Φ + Ψ) p
    obtain ⟨s2, hs2, q2⟩ := hpos (Φ - Ψ) p
    obtain ⟨a, ha, qa⟩ := hpos Φ p
    obtain ⟨b, hb, qb⟩ := hpos Ψ p
    have hpar : (s1 : ℂ) = 2 * a + 2 * b - s2 := by
      rw [← q1, ← q2, ← qa, ← qb, hs, hd, e1, e2, e3, e4]
      ring
    have hpar' : s1 = 2 * a + 2 * b - s2 := by exact_mod_cast hpar
    rw [q1, qa, qb, Complex.norm_real, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hs1,
      Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
    linarith
  intro t0 ht0
  obtain ⟨ε1, hε1, F1, hF1, hb1⟩ := h1 t0 ht0
  obtain ⟨ε2, hε2, F2, hF2, hb2⟩ := h2 t0 ht0
  refine ⟨min ε1 ε2, lt_min hε1 hε2, fun c' => 2 * F1 c' + 2 * F2 c', (hF1.const_mul 2).add (hF2.const_mul 2),
    fun t ht c' => ?_⟩
  have ht1 : t ∈ Metric.ball t0 ε1 := Metric.ball_subset_ball (min_le_left _ _) ht
  have ht2 : t ∈ Metric.ball t0 ε2 := Metric.ball_subset_ball (min_le_right _ _) ht
  have k1 := hb1 t ht1 c'
  have k2 := hb2 t ht2 c'
  rw [norm_mul] at k1 k2 ⊢
  have hk := hkey (glue l.succ (Function.update c l t) c')
  have hw := norm_nonneg (wtI l.succ c')
  nlinarith [mul_le_mul_of_nonneg_left hk hw]

theorem slDom_smul (a : ℂ) {Φ : RadSp k r z z' π π'} (h : SlDom μ l c Φ) : SlDom μ l c (a • Φ) := by
  have hp : ∀ p, pairAt μ (a • Φ) (a • Φ) p = (starRingEnd ℂ a * a) * pairAt μ Φ Φ p := fun p => by
    simp only [pairAt, B.hsInner, Submodule.coe_smul, Pi.smul_apply, hsVec_smul', inner_smul_left,
      inner_smul_right]
    first
      | (rw [← integral_const_mul]; congr 1; funext x; ring)
      | (rw [← integral_mul_left]; congr 1; funext x; ring)
  intro t0 ht0
  obtain ⟨ε, hε, F, hF, hb⟩ := h t0 ht0
  refine ⟨ε, hε, fun c' => ‖a‖ ^ 2 * F c', hF.const_mul _, fun t ht c' => ?_⟩
  have e : ‖starRingEnd ℂ a * a‖ = ‖a‖ ^ 2 := by rw [norm_mul, RCLike.norm_conj, sq]
  rw [hp, show ∀ w q : ℂ, w * (starRingEnd ℂ a * a * q) = (starRingEnd ℂ a * a) * (w * q) from
    fun w q => by ring, norm_mul, e]
  exact mul_le_mul_of_nonneg_left (hb t ht c') (by positivity)

def sgSub (hμ : B.IsHaarOn (Glev k r (Fin.last r)) μ) : Submodule ℂ (RadSp k r z z' π π') where
  carrier := {Φ | SliceGood X μ l c Φ}
  zero_mem' := ⟨(lcSub k r z z' π π').zero_mem, fun js => by rw [map_zero]; exact slDom_zero μ l c⟩
  add_mem' := by
    rintro Φ Ψ ⟨h1, h1'⟩ ⟨h2, h2'⟩
    refine ⟨(lcSub k r z z' π π').add_mem h1 h2, fun js => ?_⟩
    rw [map_add]
    exact slDom_add μ l c hμ (wOp_lc X l js Φ h1) (wOp_lc X l js Ψ h2) (h1' js) (h2' js)
  smul_mem' := by
    rintro a Φ ⟨h1, h1'⟩
    refine ⟨(lcSub k r z z' π π').smul_mem a h1, fun js => ?_⟩
    rw [map_smul]
    exact slDom_smul μ l c a (h1' js)

theorem sliceGood_op {Φ : RadSp k r z z' π π'} (h : SliceGood X μ l c Φ) (j : Fin 6) :
    SliceGood X μ l c (X.op l j Φ) :=
  ⟨Formalism.FourierDecayAlt.P5.HerC.op_lc X l j Φ h.1, fun js => by rw [wOp_op]; exact h.2 _⟩

theorem sliceGood_dT {Φ : RadSp k r z z' π π'} (h : SliceGood X μ l c Φ) : SliceGood X μ l c (dT X l Φ) :=
  sliceGood_op X μ l c (sliceGood_op X μ l c h 0) 2

theorem sliceGood_dTb {Φ : RadSp k r z z' π π'} (h : SliceGood X μ l c Φ) : SliceGood X μ l c (dTb X l Φ) :=
  sliceGood_op X μ l c (sliceGood_op X μ l c h 3) 5

end Clos

theorem clsE_sliceGood_of (hJ : JSliceGen) {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (S : Type) [Fintype S] [DecidableEq S]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq) (hD : IsData P z z' π π' X μ L st l0) (h1 : 1 ≤ l0) (h2 : l0 ≤ P.k)
    (hz : D.z = z) (hz' : D.z' = z') (hπ : D.π = π) (hπ' : D.π' = π') (l : Fin P.r) (hl : l.val = 0)
    (c : Fin P.r → ℂ) (hc : c ∈ OmX P.r) (Φ : RadSp P.k P.r z z' π π')
    (hΦ : Φ ∈ ClsE S P z z' π π' X L st l0 D l) : SliceGood X μ l c Φ := by
  have hμ : B.IsHaarOn (Glev P.k P.r (Fin.last P.r)) μ := hD.2.1
  have hle : ClsE S P z z' π π' X L st l0 D l ≤ sgSub X μ l c hμ := by
    apply opClos_le X l
    · refine (base_le_wave_operator P z z' π π' X μ L st l0 D hD hz hz' hπ hπ' l hl).trans
        (Submodule.span_le.mpr ?_)
      intro Ψ hΨ
      exact hJ Wp Wq S P z z' π π' X μ L st l0 D hD h1 h2 hz hz' hπ hπ' l hl c hc Ψ hΨ
    · intro j Ψ hΨ
      exact sliceGood_op X μ l c hΨ j
  exact hle hΦ

theorem wirt_of_hasFDerivAt {F : ℂ → ℂ} {A B t : ℂ} (h : HasFDerivAt F (wl A B) t) :
    wirt true F t = A ∧ wirt false F t = B := by
  have hf := h.fderiv
  refine ⟨?_, ?_⟩ <;> simp [wirt, hf, wl]
  · first
      | linear_combination ((B - A) / 2) * Complex.I_sq
      | linear_combination ((A - B) / 2) * Complex.I_sq
  · first
      | linear_combination ((A - B) / 2) * Complex.I_sq
      | linear_combination ((B - A) / 2) * Complex.I_sq

theorem leibnizCls_of (hO : OuterLeib) (hJ : JSliceGen) : LeibnizCls := by
  intro Wp Wq _ _ _ _ _ _ S _ _ P z z' π π' X μ L st l0 D hD h1 h2 hz hz' hπ hπ' l hl u v hu hv c hc t ht
  have hμ : B.IsHaarOn (Glev P.k P.r (Fin.last P.r)) μ := hD.2.1
  have hsu : ∀ b, SliceGood X μ l c (u b) := fun b =>
    clsE_sliceGood_of hJ S P z z' π π' X μ L st l0 D hD h1 h2 hz hz' hπ hπ' l hl c hc (u b) (hu b)
  have hsv : ∀ b, SliceGood X μ l c (v b) := fun b =>
    clsE_sliceGood_of hJ S P z z' π π' X μ L st l0 D hD h1 h2 hz hz' hπ hπ' l hl c hc (v b) (hv b)
  exact wirt_of_hasFDerivAt (hO P.k P.r z z' Wp Wq π π' X μ hμ l S u v c hc hsu hsv t ht)

theorem levelSquareIntegrable_succ_update_of_sliceGood {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
    [FiniteDimensional ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}
    (X : ActualOps k r z z' π π') (μ : Measure (Mt k r)) [SFinite μ] (l : Fin r) (c : Fin r → ℂ)
    {Φ : RadSp k r z z' π π'} (h : SliceGood X μ l c Φ) {t : ℂ} (ht : t ≠ 0) :
    LevelSquareIntegrable μ l.succ Φ (Function.update c l t) := by
  have h0 := h.2 []
  rw [wOp_nil_sg] at h0
  exact level_l2_of_slice_domination μ l c h0 ht

theorem contDiffOn_inverse_norm_sq (n : ℕ) :
    ContDiffOn ℝ n (fun t : ℂ => (((‖t‖ ^ (-2 : ℤ) : ℝ)) : ℂ)) {t : ℂ | t ≠ 0} := by
  have hN : (fun t : ℂ => Complex.normSq t) = fun t => t.re * t.re + t.im * t.im :=
    funext Complex.normSq_apply
  have hq : ContDiff ℝ n (fun t : ℂ => Complex.normSq t) := by
    rw [hN]
    exact (Complex.reCLM.contDiff.mul Complex.reCLM.contDiff).add
      (Complex.imCLM.contDiff.mul Complex.imCLM.contDiff)
  have hi : ContDiffOn ℝ n (fun t : ℂ => (Complex.normSq t)⁻¹) {t : ℂ | t ≠ 0} :=
    hq.contDiffOn.inv fun t ht => by simpa [Complex.normSq_eq_zero] using ht
  refine (Complex.ofRealCLM.contDiff.comp_contDiffOn hi).congr fun t _ => ?_
  simp [zpow_neg, Complex.normSq_eq_norm_sq]

theorem form_contDiffOn (hO : OuterLeib) {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type}
    [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}
    (X : ActualOps k r z z' π π') (μ : Measure (Mt k r)) (hμ : B.IsHaarOn (Glev k r (Fin.last r)) μ) (l : Fin r)
    (S : Type) [Fintype S] [DecidableEq S] (c : Fin r → ℂ) (hc : c ∈ OmX r) (n : ℕ) :
    ∀ (u v : Ix S → RadSp k r z z' π π'), (∀ b, SliceGood X μ l c (u b)) → (∀ b, SliceGood X μ l c (v b)) →
      ContDiffOn ℝ n (fun t => form μ l.succ u v (Function.update c l t)) {t : ℂ | t ≠ 0} := by
  have hs : IsOpen {t : ℂ | t ≠ 0} := isOpen_ne

  let Lw : ℂ × ℂ →L[ℝ] (ℂ →L[ℝ] ℂ) :=
    (ContinuousLinearMap.fst ℝ ℂ ℂ).smulRight (ContinuousLinearMap.id ℝ ℂ) +
      (ContinuousLinearMap.snd ℝ ℂ ℂ).smulRight Complex.conjCLE.toContinuousLinearMap
  induction n with
  | zero =>
    intro u v hu hv
    rw [Nat.cast_zero, contDiffOn_zero]
    exact fun t ht => (hO k r z z' Wp Wq π π' X μ hμ l S u v c hc hu hv t ht).continuousAt.continuousWithinAt
  | succ n ih =>
    intro u v hu hv
    have hd := fun t (ht : t ∈ {t : ℂ | t ≠ 0}) => hO k r z z' Wp Wq π π' X μ hμ l S u v c hc hu hv t ht
    have hA := (ih (fun b => dT X l (u b)) v (fun b => sliceGood_dT X μ l c (hu b)) hv).add
      (ih u (fun b => dTb X l (v b)) hu (fun b => sliceGood_dTb X μ l c (hv b)))
    have hB := (ih (fun b => dTb X l (u b)) v (fun b => sliceGood_dTb X μ l c (hu b)) hv).add
      (ih u (fun b => dT X l (v b)) hu (fun b => sliceGood_dT X μ l c (hv b)))
    have hW : ContDiffOn ℝ n (fun t => wl
        (form μ l.succ (fun b => dT X l (u b)) v (Function.update c l t) +
          form μ l.succ u (fun b => dTb X l (v b)) (Function.update c l t))
        (form μ l.succ (fun b => dTb X l (u b)) v (Function.update c l t) +
          form μ l.succ u (fun b => dT X l (v b)) (Function.update c l t))) {t : ℂ | t ≠ 0} := by
      first
        | exact (Lw.contDiff.comp_contDiffOn (hA.prodMk hB)).congr fun t _ => rfl
        | exact (Lw.contDiff.comp_contDiffOn (hA.prod hB)).congr fun t _ => rfl
    have hF : ContDiffOn ℝ n (fderiv ℝ fun t => form μ l.succ u v (Function.update c l t)) {t : ℂ | t ≠ 0} :=
      hW.congr fun t ht => (hd t ht).fderiv
    rw [Nat.cast_succ]
    first
      | exact (contDiffOn_succ_iff_fderiv_of_isOpen hs).2
          ⟨fun t ht => (hd t ht).differentiableAt.differentiableWithinAt, fun h => by simp at h, hF⟩
      | exact (contDiffOn_succ_iff_fderiv_of_isOpen hs).2
          ⟨fun t ht => (hd t ht).differentiableAt.differentiableWithinAt, hF⟩

theorem densSmoothCls_of (hO : OuterLeib) (hJ : JSliceGen) : DensSmoothCls := by
  intro Wp Wq _ _ _ _ _ _ S _ _ P z z' π π' X μ L st l0 D hD h1 h2 hz hz' hπ hπ' l hl u v hu hv c hc
  have hμ : B.IsHaarOn (Glev P.k P.r (Fin.last P.r)) μ := hD.2.1
  have hsu : ∀ b, SliceGood X μ l c (u b) := fun b =>
    clsE_sliceGood_of hJ S P z z' π π' X μ L st l0 D hD h1 h2 hz hz' hπ hπ' l hl c hc (u b) (hu b)
  have hsv : ∀ b, SliceGood X μ l c (v b) := fun b =>
    clsE_sliceGood_of hJ S P z z' π π' X μ L st l0 D hD h1 h2 hz hz' hπ hπ' l hl c hc (v b) (hv b)
  haveI : IsFiniteMeasureOnCompacts μ := ⟨hμ.finite_compact⟩
  haveI : SFinite μ := by
    first
      | infer_instance
      | exact (sigmaFinite_of_locallyFinite (μ := μ)).toSFinite
  refine ⟨fun n => ?_, fun t ht b => ⟨levelSquareIntegrable_succ_update_of_sliceGood X μ l c (hsu b) ht, levelSquareIntegrable_succ_update_of_sliceGood X μ l c (hsv b) ht⟩⟩
  exact (contDiffOn_inverse_norm_sq n).mul (form_contDiffOn hO X μ hμ l S c hc n u v hsu hsv)

theorem leibnizCls_of_leaves (hP : PairAtDeriv) (hJ : JSliceGen) : LeibnizCls :=
  leibnizCls_of (outerLeib_of hP) hJ

theorem densSmoothCls_of_leaves (hP : PairAtDeriv) (hJ : JSliceGen) : DensSmoothCls :=
  densSmoothCls_of (outerLeib_of hP) hJ

theorem leibnizCls_of_jSlice (hJ : JSliceGen) : LeibnizCls :=
  leibnizCls_of_leaves pairing_derivative_formula hJ

theorem densSmoothCls_of_jSlice (hJ : JSliceGen) : DensSmoothCls :=
  densSmoothCls_of_leaves pairing_derivative_formula hJ

end Formalism.FourierDecayAlt.P.CutSE
