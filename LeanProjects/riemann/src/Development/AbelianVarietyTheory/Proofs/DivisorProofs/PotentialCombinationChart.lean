import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGradedOfDivisors
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernTopPowLinearSumStatement
open NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.ChernWeilLine
open ReciprocityTheory.L2DbarEstimates (V)
open scoped Classical

namespace GlobalTheory.ChernWeilLine

theorem pn_eq_normSq_mul_exp_pot : ∀ {F : Type} [Field F] [NumberField F] {Y : Var F} {M : Man Y.dim} (I : ManIs M Y) (a : Fin (M.n + 1)) {Δ : Y.Dv} (m : (cxSt F).Met Y (I.ε a) Δ) (Q : LocPot (M.X a)), IsPot (I.pt a) m Q → IsPotential (M.A a) Q → ∀ (j : Fin (M.A a).n) (c : GlobalTheory.AlgChart Y.str (I.ε a) Y.dim), (M.A a).chart j = (I.pt a).transOpenPartialHomeomorph c.finChart → ∀ z ∈ ((M.A a).chart j).target, ∀ g : Y.Fn, Δ.GeneratesAt (under (c.finChart.symm z)) g → ∃ R : V Y.dim → ℂ, ContDiffAt ℂ 2 R (c.e (c.finChart.symm z)) ∧ R (c.e (c.finChart.symm z)) ≠ 0 ∧ ContDiffAt ℝ 2 (fun u => Q.φ (((M.A a).chart j).symm z) ((I.pt a).symm (c.e.symm u))) (c.e (c.finChart.symm z)) ∧ ∀ᶠ u in nhds (c.e (c.finChart.symm z)), 0 < (cxSt F).pn Y (I.ε a) Δ m ((cxSt F).cx Y (I.ε a) g) (c.e.symm u) ∧ (cxSt F).pn Y (I.ε a) Δ m ((cxSt F).cx Y (I.ε a) g) (c.e.symm u) = ‖R u‖ ^ 2 * Real.exp (-2 * Q.φ (((M.A a).chart j).symm z) ((I.pt a).symm (c.e.symm u))) := by
  intro F _ _ Y M I a Δ m Q hP hPot j c hc z hz g hg
  have hsymm : ∀ y', ((M.A a).chart j).symm y' = (I.pt a).symm (c.finChart.symm y') := fun y' => by
    rw [hc, Homeomorph.transOpenPartialHomeomorph_symm_apply]; rfl
  have hzt : z ∈ c.finChart.target := by
    rw [hc] at hz; simpa using hz
  have hy0 : c.finChart.symm z ∈ c.e.source := c.finChart.map_target hzt
  set x := ((M.A a).chart j).symm z with hxdef
  have hx : I.pt a x = c.finChart.symm z := by rw [hxdef, hsymm, Homeomorph.apply_symm_apply]
  obtain ⟨f, hf⟩ := hP x
  have hfx := hf x (Q.mem_U x)
  rw [hx] at hfx
  obtain ⟨e, he⟩ := Δ.exists_isEqn (under (c.finChart.symm z))
  have hr : UnitAt (under (c.finChart.symm z)) (g * f⁻¹) := by
    have h1 := (he.generatesAt_iff.1 hg).mul (he.generatesAt_iff.1 hfx.1).inv
    have hf0 : f ≠ 0 := hfx.1.ne_zero
    have he0 : (e : Y.Fn) ≠ 0 := Units.ne_zero e
    convert h1 using 1
    field_simp
  obtain ⟨U0, hU0, hU0u⟩ := hr.exists_nhds
  obtain ⟨b, hb⟩ := exists_unit_fnOf_eq hU0u
  have hgen0 := gen_mem hU0
  have hb' := hb hgen0
  have hv : c.e (c.finChart.symm z) = GlobalTheory.FinChart.toV Y.dim z := by
    rw [← AlgChart.toV_finChart, c.finChart.right_inv hzt]
  have hxs : (I.pt a).symm (c.finChart.symm z) = x := by rw [← hx, Homeomorph.symm_apply_apply]
  have hS : IsOpen (ptsIn Y.str (I.ε a) U0 ∩ (I.pt a).symm ⁻¹' Q.U x) :=
    (isOpen_ptsIn U0).inter ((Q.isOpen_U x).preimage (I.pt a).symm.continuous)
  have hvO := mem_over c.e hy0 (S := ptsIn Y.str (I.ε a) U0 ∩ (I.pt a).symm ⁻¹' Q.U x)
    ⟨mem_ptsIn.2 hU0, by simpa [hxs] using Q.mem_U x⟩
  have hRa : AnalyticAt ℂ (ev Y.str (I.ε a) U0 b.1 ∘ c.e.symm) (c.e (c.finChart.symm z)) :=
    GlobalTheory.SCV.analyticAt_of_differentiableOn (c.holo U0 b)
      ((isOpen_over c.e (isOpen_ptsIn U0)).mem_nhds (mem_over c.e hy0 (mem_ptsIn.2 hU0)))
  refine ⟨fun u => ev Y.str (I.ε a) U0 b.1 (c.e.symm u), hRa.contDiffAt, ?_, ?_, ?_⟩
  · simp only [c.e.left_inv hy0]
    exact ev_ne_zero (mem_ptsIn.2 hU0) b.isUnit
  · have hsm := hPot.1 x j
    have hzmem : z ∈ ((M.A a).chart j).target ∩ ((M.A a).chart j).symm ⁻¹' Q.U x :=
      ⟨hz, by simpa [← hxdef] using Q.mem_U x⟩
    have hca : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Q.φ x ∘ ((M.A a).chart j).symm) z :=
      hsm.contDiffAt ((((M.A a).chart j).isOpen_inter_preimage_symm (Q.isOpen_U x)).mem_nhds hzmem)
    have key : (fun u => Q.φ x ((I.pt a).symm (c.e.symm u))) =
        fun u => (Q.φ x ∘ ((M.A a).chart j).symm) ((GlobalTheory.FinChart.toV Y.dim).symm u) := by
      funext u; simp [hsymm, AlgChart.finChart_symm_apply]
    rw [key]
    have hca' : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Q.φ x ∘ ((M.A a).chart j).symm)
        ((GlobalTheory.FinChart.toV Y.dim).symm (c.e (c.finChart.symm z))) := by
      rw [hv, ContinuousLinearEquiv.symm_apply_apply]; exact hca
    exact (hca'.comp _ (GlobalTheory.FinChart.toV Y.dim).symm.contDiff.contDiffAt).of_le
      (WithTop.coe_le_coe.2 le_top)
  · filter_upwards [(isOpen_over c.e hS).mem_nhds hvO] with u hu
    obtain ⟨-, h1, h2⟩ := hu
    obtain ⟨hgw, hpos, hφ⟩ := hf _ h2
    rw [Homeomorph.apply_symm_apply] at hgw hpos hφ
    have hUw := hU0u _ (mem_ptsIn.1 h1)
    have hratv : ratVal (g * f⁻¹) (c.e.symm u) = ev Y.str (I.ε a) U0 b.1 (c.e.symm u) := by
      rw [← hb', ratVal_fnOf h1]
    have hpn : (cxSt F).pn Y (I.ε a) Δ m ((cxSt F).cx Y (I.ε a) g) (c.e.symm u) =
        ‖ratVal (g * f⁻¹) (c.e.symm u)‖ ^ 2 * (cxSt F).pn Y (I.ε a) Δ m ((cxSt F).cx Y (I.ε a) f) (c.e.symm u) := by
      have := (cxSt F).pn_mul Y (I.ε a) Δ m (g * f⁻¹) f (c.e.symm u) hUw.regAt hgw.regularAt
      rwa [inv_mul_cancel_right₀ hgw.ne_zero] at this
    have hfpos : 0 < (cxSt F).pn Y (I.ε a) Δ m ((cxSt F).cx Y (I.ε a) f) (c.e.symm u) := by
      obtain ⟨a', ha', e'⟩ := exists_pn_eq (C := cxSt F) hgw
      rw [e' m]; exact mul_pos ha' hpos
    have hexp : Real.exp (-2 * Q.φ x ((I.pt a).symm (c.e.symm u))) =
        (cxSt F).pn Y (I.ε a) Δ m ((cxSt F).cx Y (I.ε a) f) (c.e.symm u) := by
      rw [hφ, lnN, show -2 * -(Real.log ((cxSt F).pn Y (I.ε a) Δ m ((cxSt F).cx Y (I.ε a) f) (c.e.symm u)) / 2) =
        Real.log ((cxSt F).pn Y (I.ε a) Δ m ((cxSt F).cx Y (I.ε a) f) (c.e.symm u)) by ring, Real.exp_log hfpos]
    have hR0 : 0 < ‖ratVal (g * f⁻¹) (c.e.symm u)‖ ^ 2 := pow_pos (norm_pos_iff.2 (ratVal_ne_zero hUw)) 2
    refine ⟨?_, ?_⟩
    · rw [hpn]; exact mul_pos hR0 hfpos
    · rw [hpn, hexp, hratv]

open GlobalTheory.FinChart in

theorem hessC_comp_toV {n : ℕ} (h : V n → ℝ) (z : Fin n → ℂ) (hh : ContDiffAt ℝ 2 h (toV n z)) :
    hessC (h ∘ toV n) z = Matrix.of fun a b => GlobalTheory.leviForm h (toV n z) (coordVec a) (coordVec b) := by
  have h₁ : fderiv ℝ (h ∘ toV n) = fun w => (fderiv ℝ h (toV n w)).comp (toV n).toContinuousLinearMap :=
    funext fun _ => (toV n).comp_right_fderiv
  have hD := ((hh.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).hasFDerivAt
  have h₂ := ((hD.comp z (toV n).hasFDerivAt).clm_comp
    (hasFDerivAt_const (toV n).toContinuousLinearMap z)).fderiv
  have hH (p q : Fin n → ℂ) : fderiv ℝ (fderiv ℝ (h ∘ toV n)) z p q =
      fderiv ℝ (fderiv ℝ h) (toV n z) (toV n p) (toV n q) := by
    rw [h₁]
    erw [h₂]
    simp
  have e₁ (a : Fin n) : toV n (Pi.single a 1) = coordVec a := rfl
  have e₂ (a : Fin n) : toV n (Complex.I • Pi.single a 1) = Complex.I • coordVec a := rfl
  ext a b
  rw [Matrix.of_apply, GlobalTheory.leviForm_apply hh, hessC]
  simp only [hH, e₁, e₂]
  push_cast
  ring

open GlobalTheory.FinChart in

theorem locDens_combPot_eq_chernTop : ∀ {F : Type} [Field F] [NumberField F] {Y : Var F} {M : Man Y.dim} (I : ManIs M Y) {ι : Type} [Fintype ι] {Δ : ι → Y.Dv} (m : ∀ i σ, (cxSt F).Met Y σ (Δ i)) (t : ι → ℝ) (a : Fin (M.n + 1)) (Q : ι → LocPot (M.X a)), (∀ i, IsPot (I.pt a) (m i (I.ε a)) (Q i) ∧ IsPotential (M.A a) (Q i)) → ∀ (j : Fin (M.A a).n) (c : GlobalTheory.AlgChart Y.str (I.ε a) Y.dim), (M.A a).chart j = (I.pt a).transOpenPartialHomeomorph c.finChart → ∀ z ∈ ((M.A a).chart j).target, ∀ A ∈ (ofDivisors Δ).S (under (c.finChart.symm z)), locDens (M.A a) (fun _ => InhabCalc.combPot Q t 0) j z = chernTop ((∑ i, C (t i) * X (i, 1)) ^ Y.dim) (fun v => lineGram (cxSt F) (fun i => m i (I.ε a)) A (c.e.symm v)) (c.e (c.finChart.symm z)) := by
  intro F _ _ Y M I ι _ Δ m t a Q hQ j c hc z hz A hA
  have hsymm : ∀ y', ((M.A a).chart j).symm y' = (I.pt a).symm (c.e.symm (toV Y.dim y')) := fun y' => by
    rw [hc, Homeomorph.transOpenPartialHomeomorph_symm_apply]; rfl
  have hzt : z ∈ c.finChart.target := by
    rw [hc] at hz; simpa using hz
  have hv : c.e (c.finChart.symm z) = toV Y.dim z := by
    rw [← AlgChart.toV_finChart, c.finChart.right_inv hzt]
  have hgen : ∀ i, (Δ i).GeneratesAt (under (c.finChart.symm z)) (A i 0 0) := fun i => hA i
  choose R hR hR0 hq hev using fun i =>
    pn_eq_normSq_mul_exp_pot I a (m i (I.ε a)) (Q i) (hQ i).1 (hQ i).2 j c hc z hz (A i 0 0) (hgen i)

  set v := c.e (c.finChart.symm z) with hvdef
  let q : ι → V Y.dim → ℝ := fun i u => (Q i).φ (((M.A a).chart j).symm z) ((I.pt a).symm (c.e.symm u))
  let g : ι → V Y.dim → ℝ := fun i u =>
    (cxSt F).pn Y (I.ε a) (Δ i) (m i (I.ε a)) ((cxSt F).cx Y (I.ε a) (A i 0 0)) (c.e.symm u)
  have hq : ∀ i, ContDiffAt ℝ 2 (q i) v := hq
  have hev : ∀ i, ∀ᶠ u in nhds v, 0 < g i u ∧ g i u = ‖R i u‖ ^ 2 * Real.exp (-2 * q i u) := hev
  have hR2 : ∀ i, ContDiffAt ℝ 2 (fun u => ‖R i u‖ ^ 2) v := fun i => ((hR i).restrict_scalars ℝ).norm_sq ℂ
  have hg2 : ∀ i, ContDiffAt ℝ 2 (g i) v := fun i =>
    ((hR2 i).mul ((contDiffAt_const.mul (hq i)).exp)).congr_of_eventuallyEq ((hev i).mono fun u hu => hu.2)
  have hgpos : ∀ i, 0 < g i v := fun i => (hev i).self_of_nhds.1
  have hlog : ∀ i, (fun u => Real.log (g i u)) =ᶠ[nhds v] fun u => Real.log (‖R i u‖ ^ 2) + (-2) * q i u :=
    fun i => (hev i).mono fun u hu => by
      obtain ⟨h1, h2⟩ := hu
      have hp : 0 < ‖R i u‖ ^ 2 := by
        rw [h2] at h1; exact (mul_pos_iff_of_pos_right (Real.exp_pos _)).1 h1
      show Real.log (g i u) = Real.log (‖R i u‖ ^ 2) + -2 * q i u
      rw [h2, Real.log_mul hp.ne' (Real.exp_pos _).ne', Real.log_exp]
  have hl1 : ∀ i, ContDiffAt ℝ 2 (fun u => Real.log (‖R i u‖ ^ 2)) v := fun i =>
    (hR2 i).log (pow_ne_zero 2 (norm_ne_zero_iff.2 (hR0 i)))
  have hlev : ∀ i, GlobalTheory.leviForm (fun u => Real.log (g i u)) v = (-2 : ℂ) • GlobalTheory.leviForm (q i) v := fun i => by
    rw [GlobalTheory.leviForm_congr (hlog i), GlobalTheory.leviForm_add (hl1 i) (contDiffAt_const.mul (hq i)),
      GlobalTheory.leviForm_log_normSq_eq_zero (hR i) (hR0 i), zero_add, GlobalTheory.leviForm_const_mul _ (hq i)]
    push_cast; rfl
  have hcurv : ∀ i (a' b' : Fin Y.dim),
      curv (fun u => lineGram (cxSt F) (fun i => m i (I.ε a)) A (c.e.symm u) i) v (coordVec a') (coordVec b') 0 0 =
        2 * GlobalTheory.leviForm (q i) v (coordVec a') (coordVec b') := fun i a' b' => by
    rw [curv_line (f := g i) (hg2 i) (hgpos i).ne' (Filter.Eventually.of_forall fun u => rfl), hlev i]
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  have hψ2 : ContDiffAt ℝ 2 (fun u => ∑ i, t i * q i u) v :=
    ContDiffAt.sum fun i _ => contDiffAt_const.mul (hq i)
  have hsum : (∑ i, (t i : ℂ) • Matrix.of fun a' b' =>
      curv (fun u => lineGram (cxSt F) (fun i => m i (I.ε a)) A (c.e.symm u) i) v (coordVec a') (coordVec b') 0 0) =
      (2 : ℂ) • Matrix.of fun a' b' => GlobalTheory.leviForm (fun u => ∑ i, t i * q i u) v (coordVec a') (coordVec b') := by
    ext a' b'
    simp only [hcurv, Matrix.sum_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    rw [GlobalTheory.leviForm_sum fun i _ => contDiffAt_const.mul (hq i)]
    simp only [ContinuousLinearMap.sum_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [GlobalTheory.leviForm_const_mul _ (hq i)]
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  have hψ : (fun y' => (InhabCalc.combPot Q t 0).φ (((M.A a).chart j).symm z) (((M.A a).chart j).symm y')) =
      (fun u => ∑ i, t i * q i u) ∘ toV Y.dim := by
    funext y'
    simp [InhabCalc.combPot, hsymm, q]
  rw [GlobalTheory.T.chern_top_pow_linear_sum, hsum, locDens, maDens, ReciprocityTheory.AnForm.A.mdisc_const, hψ, hessC_comp_toV _ _ (hv ▸ hψ2), ← hv,
    Matrix.det_smul, Fintype.card_fin]
  rw [show ((2 : ℂ) ^ Y.dim) = ((2 ^ Y.dim : ℝ) : ℂ) by push_cast; rfl, Complex.re_ofReal_mul, div_pow]
  field_simp

end GlobalTheory.ChernWeilLine
