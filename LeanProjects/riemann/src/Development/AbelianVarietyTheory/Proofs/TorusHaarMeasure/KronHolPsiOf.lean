import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OrthoStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfS
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfE
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfH

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.KronAssembly

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem chi_ne_zero {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) :
    X.χ la γ ≠ 0 := by
  obtain ⟨n, hn, h⟩ := X.χ_fin la
  intro h0
  have := h γ hγ
  rw [h0, zero_pow hn.ne'] at this
  exact zero_ne_one this

theorem exists_orth {r : ℕ} (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) {γ : GL (Fin r) E}
    (hγ : γ ∈ X.Γ) : ∃ x1, IsOrth X x1 ∧ ∃ b ∈ Bor X.Ψ r, ∃ b' ∈ Bor X.Ψ r,
      lact γ x = rmul x1 b ∧ x1 = lact γ (rmul x b') := by
  obtain ⟨x1, ho, b, hb, h⟩ := ortho_holds r X (lact γ x) (OntoS.dom_lact X hγ hx)
  refine ⟨x1, ho, b, hb, ExtFPf.invF X b, ExtFPf.invF_mem X hb, h, ?_⟩
  rw [FundSetPf.lact_rmul, h, ExtFPf.rmul_assoc, ExtFPf.rmul_invF X hb, ExtFPf.rmul_oneF]

theorem sec_ne_zero {r : ℕ} (X : Data E r) {L : Wt X.Ψ r} {w : Frame X.Ψ r → ℂ} (hw : X.IsSec L w)
    {x : Frame X.Ψ r} (hx : x ∈ X.dom) (h : w x ≠ 0) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ)
    {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) : w (lact γ (rmul x b)) ≠ 0 := by
  rw [hw.2.2 γ hγ _ (OntoS.dom_rmul X hx hb), hw.2.1 x hx b hb]
  exact mul_ne_zero (chi_ne_zero X L hγ) (mul_ne_zero (OntoE.bchar_ne X L hb) h)

theorem kronHolPsi_of :
    (ExtFStatement (E := E)) → (∀ (r : ℕ) (X : Data E r) (L : Wt X.Ψ r) (w0 : Frame X.Ψ r → ℂ) (s
        : Fin (nd X) → Frame X.Ψ r → ℂ), X.IsSec L w0 → (∀ k, X.IsSec L (s
        k)) → ∀ x ∈ X.dom, w0 x ≠ 0 → (fderiv ℂ (fun z : V (nd X) => (WithLp.toLp 2
        fun k => s k (cpt X (x) z) / w0 (cpt X (x) z) : V (nd X)))
        0).det ≠ 0 → ∀ γ ∈ X.Γ, ∀ b ∈ Bor X.Ψ r, (fderiv ℂ (fun z : V (nd X) => (WithLp.toLp 2
        fun k => s k (cpt X (lact γ (rmul x b)) z) / w0 (cpt X (lact γ (rmul x b)) z) : V (nd X)))
        0).det ≠ 0) → (∀ (r : ℕ) (X : Data E r) (la
        : Wt X.Ψ r), ∀ ψ : Frame X.Ψ r → ℝ, IsInvFn X ψ → (∀ x0, IsOrth X x0 → ContDiffOn ℝ ∞ (fun z => ψ (cpt
        X x0 z)) (OmF X
        x0)) → (∃ C : ℝ, ∀ x ∈ X.dom, ψ x ≤ C) → ContinuousOn ψ X.dom ∧ IsMetricW X la (X.dom.indicator
        fun x => ENNReal.ofReal (Real.exp (-(phla X la x + ψ x)))) ∧ WLower X la (X.dom.indicator
        fun x => ENNReal.ofReal (Real.exp (-(phla X la x + ψ x))))) → (∀ (r : ℕ) (X : Data E r) (la
        L : Wt X.Ψ r) (w0 : Frame X.Ψ r → ℂ) (s : Fin (nd X) → Frame X.Ψ r → ℂ) (ψ
        : Frame X.Ψ r → ℝ) (x0 : Frame X.Ψ r) (bb m η
        : ℝ), 0 < nd X → IsOrth X x0 → X.IsSec L w0 → (∀ k, X.IsSec L (s
        k)) → ContDiffOn ℝ ∞ (fun z => ψ (cpt X x0 z)) (OmF X
        x0) → 0 ≤ bb → bb < m → 0 < η → (∀ z ∈ OmF X x0, ∀ ξ : Fin (nd
        X) → ℂ, m * leviRh X x0 z ξ ≤ leviO X x0 (phla X la) z ξ - leviDens X x0 z ξ - (nd X
        : ℝ) * leviO X x0 (phla X L) z ξ + leviO X x0 ψ z ξ) → (∀ z ∈ OmF X x0, ∀ ξ : Fin (nd
        X) → ℂ, 2 * η * leviO X x0 (phla X L) z ξ ≤ leviO X x0 (phla X
        la) z ξ - leviDens X x0 z ξ - (nd X : ℝ) * leviO X x0 (phla X
        L) z ξ + leviO X x0 ψ z ξ) → (∀ z ∈ OmF X x0, ∀ ξ : Fin (nd
        X) → ℂ, ξ ≠ 0 → 0 < leviO X x0 (phla X L) z ξ) → w0 x0 ≠ 0 → (∀ k, s k x0 = 0) → (fderiv ℂ
        (fun z : V (nd X) => (WithLp.toLp 2 fun k => s k (cpt X (x0) z) / w0 (cpt X (x0) z) : V (nd
        X))) 0).det ≠ 0 → ∃ (ε : ℝ) (χ F : V (nd X) → ℂ), 0 < ε ∧ Metric.closedBall (0 : V (nd
        X)) (2 * ε) ⊆ OmF X x0 ∧ (∀ z ∈ Metric.closedBall (0 : V (nd X)) (2 * ε), (∀ k, s k (cpt X
        x0
        z) = 0) → z = 0) ∧ Continuous χ ∧ (∀ z, ‖z‖ ≤ ε → χ z = 1) ∧ (∀ z, 2 * ε ≤ ‖z‖ → χ z = 0) ∧ DifferentiableOn ℂ F (OmF
        X x0) ∧ ∫⁻ z, ENNReal.ofReal (‖χ z - F z‖ ^ 2 * Real.exp (-(phla X la (cpt X x0 z) + ψ (cpt
        X x0 z))) / kaF X x0 bb z * (∑ k, X.pnorm L (s k) (cpt X x0 z) ^ 2) ^ (-(nd X
        : ℝ))) ∂muF X x0 < ⊤) → (∀ (r : ℕ) (X : Data E r) (la L : Wt X.Ψ r) (w0
        : Frame X.Ψ r → ℂ) (s : Fin (nd X) → Frame X.Ψ r → ℂ) (ψ : Frame X.Ψ r → ℝ) (x0 x1
        : Frame X.Ψ r) (bb δ : ℝ) (χ F : V (nd X) → ℂ) (P
        : Frame X.Ψ r → ℂ), 0 < nd X → IsOrth X x0 → IsOrth X x1 → X.IsSec L w0 → (∀ k, X.IsSec L (s
        k)) → ContinuousOn ψ X.dom → (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, ψ (rmul x
        b) = ψ x) → 0 ≤ bb → Metric.closedBall (0 : V (nd
        X)) δ ⊆ OmF X x0 → (∀ z, δ ≤ ‖z‖ → χ z = 0) → IsBEq X la P → (∀ z ∈ OmF X x0, P (cpt X x0
        z) = F z) → ∫⁻ z, ENNReal.ofReal (‖χ z - F z‖ ^ 2 * Real.exp (-(phla X la (cpt X x0 z) + ψ
        (cpt X x0 z))) / kaF X x0 bb z * (∑ k, X.pnorm L (s k) (cpt X x0 z) ^ 2) ^ (-(nd X
        : ℝ))) ∂muF X x0 < ⊤ → (∀ z ∈ Metric.closedBall (0 : V (nd
        X)) δ, ∀ b ∈ Bor X.Ψ r, x1 ≠ rmul (cpt X x0 z) b) → w0 x1 ≠ 0 → (∀ k, s k x1 = 0) → (fderiv
        ℂ (fun z : V (nd X) => (WithLp.toLp 2 fun k => s k (cpt X (x1) z) / w0 (cpt X (x1)
        z) : V (nd X))) 0).det ≠ 0 → P x1 = 0) → (∀ (r : ℕ) (X : Data E r) (la L : Wt X.Ψ r) (w0
        : Frame X.Ψ r → ℂ) (s : Fin (nd X) → Frame X.Ψ r → ℂ) (ψ : Frame X.Ψ r → ℝ) (x0
        : Frame X.Ψ r) (bb ε δ : ℝ) (χ F : V (nd
        X) → ℂ), 0 < nd X → IsOrth X x0 → X.IsBddSec L w0 → (∀ k, X.IsBddSec L (s
        k)) → ContinuousOn ψ X.dom → (∃ C : ℝ, ∀ x ∈ X.dom, ψ x ≤ C) → 0 ≤ bb → 0 < ε → Metric.closedBall (0
        : V (nd
        X)) δ ⊆ OmF X x0 → Continuous χ → (∀ z, ‖z‖ ≤ ε → χ z = 1) → (∀ z, δ ≤ ‖z‖ → χ z = 0) → DifferentiableOn ℂ F (OmF
        X x0) → ∫⁻ z, ENNReal.ofReal (‖χ z - F z‖ ^ 2 * Real.exp (-(phla X la (cpt X x0 z) + ψ (cpt
        X x0 z))) / kaF X x0 bb z * (∑ k, X.pnorm L (s k) (cpt X x0 z) ^ 2) ^ (-(nd X
        : ℝ))) ∂muF X x0 < ⊤ → w0 x0 ≠ 0 → (∀ k, s k x0 = 0) → (fderiv ℂ (fun z : V (nd
        X) => (WithLp.toLp 2 fun k => s k (cpt X (x0) z) / w0 (cpt X (x0) z) : V (nd X)))
        0).det ≠ 0 → F 0 = 1 ∧ InAt X x0 (X.dom.indicator fun x => ENNReal.ofReal (Real.exp (-(phla
        X la x + ψ x)))) bb F ∧ ∀ C : Set (Frame X.Ψ
        r), IsCompact C → C ⊆ X.dom → ∫⁻ z in sat X x0 C, ENNReal.ofReal (‖F z‖ ^ 2 * Real.exp
        (-phla X la (cpt X x0 z))) ∂muF X x0 < ⊤) → (KronHolPsiStatement (E := E)) := by
  intro hExt hCo hMet hSol hVan hOne r X Xa Fl _ ψ hψ hψs hψb ⟨bb, m, hbb, hbm, hmar⟩ ⟨η, hη, hstr⟩ _ j
  have hn : 0 < nd X := lt_of_lt_of_le (by norm_num) Xa.n_ge
  have hbb0 : 0 ≤ bb := le_trans (by positivity) hbb.le
  have hw0b : X.IsBddSec Xa.L Fl.w0 := Fl.weightForm_vanishes.1.1
  have hsb : ∀ k, X.IsBddSec Xa.L (Fl.s k) := fun k => (Fl.s_van k).1.1
  have hw0 : X.IsSec Xa.L Fl.w0 := hw0b.1
  have hs : ∀ k, X.IsSec Xa.L (Fl.s k) := fun k => (hsb k).1
  have key : ∀ j', ∀ γ ∈ X.Γ, ∀ b ∈ Bor X.Ψ r, ∀ x1, x1 = lact γ (rmul (Fl.xs j') b) →
      Fl.w0 x1 ≠ 0 ∧ (∀ k, Fl.s k x1 = 0) ∧
      (fderiv ℂ (fun z : V (nd X) => (WithLp.toLp 2 fun k =>
        Fl.s k (cpt X x1 z) / Fl.w0 (cpt X x1 z) : V (nd X))) 0).det ≠ 0 := by
    rintro j' γ hγ b hb x1 rfl
    refine ⟨sec_ne_zero X hw0 (Fl.xs_mem j') (Fl.w0_ne j') hγ hb, ?_,
      hCo r X Xa.L Fl.w0 Fl.s hw0 hs _ (Fl.xs_mem j') (Fl.w0_ne j') (Fl.coord j') γ hγ b hb⟩
    exact (Fl.S_eq _ (OntoS.dom_lact X hγ (OntoS.dom_rmul X (Fl.xs_mem j') hb))).2
      ⟨j', γ, hγ, b, hb, rfl⟩
  obtain ⟨x0, ho, b0, hb0, b0', hb0', hx0, hx0'⟩ := exists_orth X (Fl.xs_mem j) X.Γ.one_mem
  have hx0d : x0 ∈ X.dom := IW.orth_mem_dom X x0 ho
  obtain ⟨k1, k2, k3⟩ := key j 1 X.Γ.one_mem b0' hb0' x0 hx0'
  obtain ⟨hψc, hMW, hWL⟩ := hMet r X Xa.Fp ψ hψ hψs hψb
  have hψB : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, ψ (rmul x b) = ψ x := by
    intro x hx b hb
    have := hψ 1 X.Γ.one_mem x hx b hb
    rwa [FundSetPf.lact_one] at this
  obtain ⟨ε, χ, F, hε, hball, hiso, hχc, hχ1, hχ0, hF, hint⟩ :=
    hSol r X Xa.Fp Xa.L Fl.w0 Fl.s ψ x0 bb m η hn ho hw0 hs (hψs x0 ho) hbb0 hbm hη (hmar x0 ho)
      (hstr x0 ho) (fun z hz ξ hξ => Xa.posL x0 hx0d z hz ξ hξ) k1 k2 k3
  obtain ⟨hF0, hInAt, hloc⟩ :=
    hOne r X Xa.Fp Xa.L Fl.w0 Fl.s ψ x0 bb ε (2 * ε) χ F hn ho hw0b hsb hψc hψb hbb0 hε hball hχc hχ1
      hχ0 hF hint k1 k2 k3
  obtain ⟨P, hP, hPF⟩ := hExt r X x0 ho Xa.Fp F hF hloc
  have h0 : (0 : V (nd X)) ∈ OmF X x0 := by
    show cpt X x0 0 ∈ X.dom
    rw [IW.cpt_zero]; exact hx0d
  have hP0 : P x0 = 1 := by
    have := hPF 0 h0
    rwa [IW.cpt_zero, hF0] at this
  refine ⟨x0, _, bb, F, P, 1, ho, hMW, hWL, fun x hx => ?_, hbb, hF, hInAt, hP, hPF, X.Γ.one_mem, ?_, ?_⟩
  · rw [Set.indicator_of_mem hx]
  · rw [hx0, hP.2 x0 hx0d b0 hb0, hP0, mul_one]
    exact OntoE.bchar_ne X _ hb0
  · intro γ hγ j' hne
    obtain ⟨x1, ho1, b1, hb1, b1', hb1', hx1, hx1'⟩ := exists_orth X (Fl.xs_mem j') hγ
    have hx1d : x1 ∈ X.dom := IW.orth_mem_dom X x1 ho1
    obtain ⟨l1, l2, l3⟩ := key j' γ hγ b1' hb1' x1 hx1'
    have hP1 : P x1 = 0 := by
      refine hVan r X Xa.Fp Xa.L Fl.w0 Fl.s ψ x0 x1 bb (2 * ε) χ F P hn ho ho1 hw0 hs hψc hψB hbb0 hball
        hχ0 hP hPF hint ?_ l1 l2 l3
      intro z hz b hb hxz
      have hz0 : z = 0 := by
        refine hiso z hz fun k => ?_
        have h1 := l2 k
        rw [hxz, (hs k).2.1 _ (hball hz) b hb] at h1
        exact (mul_eq_zero.mp h1).resolve_left (OntoE.bchar_ne X _ hb)
      rw [hz0, IW.cpt_zero] at hxz

      rw [FundSetPf.lact_one] at hx0'
      have hc : rmul b0' (rmul b b1) ∈ Bor X.Ψ r := ExtFPf.mul_mem X hb0' (ExtFPf.mul_mem X hb hb1)
      have he : lact γ (Fl.xs j') = rmul (Fl.xs j) (rmul b0' (rmul b b1)) := by
        rw [hx1, hxz, ← ExtFPf.rmul_assoc X (Fl.xs j) b0', ← hx0', ExtFPf.rmul_assoc]
      have hjj : j = j' := by
        refine Fl.xs_inj j j' γ⁻¹ (X.Γ.inv_mem hγ) _ hc ?_
        rw [← he, FundSetPf.lact_inv]
      subst hjj
      have hγ1 : γ = 1 := X.Γ_free γ hγ _ (Fl.xs_mem j) _ hc he
      rcases hne with h | h
      · exact h hγ1
      · exact h rfl
    rw [hx1, hP.2 x1 hx1d b1 hb1, hP1, mul_zero]

end GlobalTheory.KronAssembly
