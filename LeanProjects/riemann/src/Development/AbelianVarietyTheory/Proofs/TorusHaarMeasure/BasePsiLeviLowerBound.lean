import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.BasePsiLeviLowerBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExtFStatementPfA
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumInvariantContinuousPosOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajPos
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajorantFamilyNorms
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.CurvatureFamilyNorm
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.NormBcharMulNfacRmul
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.LeviFormWeightMetricOrthonormalDiagonal
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.BorelDiagNeZero
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.PhlaBlockWtCpt
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MeasureStatements

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates Topology
open scoped ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.CurvatureFamilyNorm

namespace GlobalTheory.FrameThetaCompare

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem cpt_contDiff (X : Data E r) (x0 : Frame X.Ψ r) : ContDiff ℂ ∞ (cpt X x0) :=
  contDiff_pi.2 fun τ => contDiff_pi.2 fun a => contDiff_pi.2 fun c => IW.cpt_entry_cd X x0 τ a c

theorem chart_smooth (X : Data E r) {u : Frame X.Ψ r → ℝ} (hu : ContDiffOn ℝ ∞ u X.dom)
    (x0 : Frame X.Ψ r) : ContDiffOn ℝ ∞ (fun z => u (cpt X x0 z)) {z | cpt X x0 z ∈ X.dom} :=
  hu.comp ((cpt_contDiff X x0).restrict_scalars ℝ).contDiffOn fun _ hz => hz

theorem contDiffOn_frame {Ψ : Finset (E →+* ℂ)} {g : Frame Ψ r → ℂ} {U : Set (Frame Ψ r)}
    (hU : IsOpen U) (hg : DifferentiableOn ℂ g U) : ContDiffOn ℂ ∞ g U := by
  let n := Module.finrank ℂ (Frame Ψ r)
  let e : Frame Ψ r ≃L[ℂ] V n := ContinuousLinearEquiv.ofFinrankEq (by simp [n, V])
  have h := contDiffOn_of_differentiableOn n (g ∘ e.symm) (e.symm ⁻¹' U)
    (hU.preimage e.symm.continuous) (hg.comp e.symm.differentiableOn fun _ h => h)
  refine (h.comp e.contDiff.contDiffOn fun x hx => by simpa using hx).congr fun x _ => by simp

theorem smooth_of_chart (X : Data E r) {u : Frame X.Ψ r → ℝ}
    (hinv : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, u (rmul x b) = u x)
    (hu : ∀ x0 ∈ X.dom, ContDiffOn ℝ ∞ (fun z => u (cpt X x0 z)) {z | cpt X x0 z ∈ X.dom}) :
    ContDiffOn ℝ ∞ u X.dom := by
  intro x hx
  obtain ⟨x1, ho, b, hb, hxb⟩ := ortho_holds r X _ hx
  obtain ⟨Δ, zOf, bOf, hΔ, -, hzd, -, hsplit, hin⟩ := lu_holds r X x1 ho
  have h0 := hin 0 (IW.zero_mem_OmF X x1 ho) b hb
  rw [IW.cpt_zero, ← hxb] at h0
  have hU : IsOpen {x | x ∈ X.dom ∧ Δ x ≠ 0} :=
    (FourierCoefficientDomain.isOpen_dom X).inter (isOpen_ne_fun hΔ.continuous continuous_const)
  have hz : ContDiffOn ℂ ∞ zOf {x | x ∈ X.dom ∧ Δ x ≠ 0} := by
    rw [contDiffOn_piLp]
    intro i
    exact contDiffOn_frame hU ((differentiableOn_piLp 2).1 hzd i)
  have h1 : ContDiffOn ℝ ∞ u {x | x ∈ X.dom ∧ Δ x ≠ 0} := by
    refine ((hu x1 (IW.orth_mem_dom X x1 ho)).comp (hz.restrict_scalars ℝ)
      fun y hy => (hsplit y hy.1 hy.2).1).congr fun y hy => ?_
    obtain ⟨k1, k2, k3⟩ := hsplit y hy.1 hy.2
    show u y = u (cpt X x1 (zOf y))
    rw [← hinv _ k1 _ k2, ← k3]
  exact (h1.contDiffAt (hU.mem_nhds ⟨hx, h0.1⟩)).contDiffWithinAt

theorem levi_transfer (X : Data E r) (x0 : Frame X.Ψ r) (z : V (nd X)) (hz : cpt X x0 z ∈ X.dom) :
    ∃ (x1 : Frame X.Ψ r) (D : (Fin (nd X) → ℂ) →ₗ[ℂ] (Fin (nd X) → ℂ)), IsOrth X x1 ∧
      Function.Injective D ∧ ∀ (la : Wt X.Ψ r) (u : Frame X.Ψ r → ℝ),
        (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r,
          u (rmul x b) = u x + Real.log (Complex.normSq (bchar la b))) →
        ContDiffAt ℝ 2 (fun w => u (cpt X x1 w)) 0 →
        ∀ ξ, lev X x0 u z ξ = lev X x1 u 0 (D ξ) := by
  obtain ⟨x1, ho, b, hb, hxb⟩ := ortho_holds r X _ hz
  obtain ⟨Δ, zOf, bOf, hΔ, -, hzd, hbd, hsplit, hinv⟩ := lu_holds r X x1 ho
  have h0 := hinv 0 (IW.zero_mem_OmF X x1 ho) b hb
  rw [IW.cpt_zero, ← hxb] at h0
  have hcd : Differentiable ℂ (cpt X x0) := (cpt_contDiff X x0).differentiable (by simp)
  set U : Set (V (nd X)) := {w | cpt X x0 w ∈ X.dom ∧ Δ (cpt X x0 w) ≠ 0} with hUdef
  have hU : IsOpen U :=
    (ExF.isOpen_OmF X x0).inter
      (isOpen_compl_singleton.preimage (hΔ.comp hcd).continuous)
  have hzU : z ∈ U := ⟨hz, h0.1⟩
  set Φ : V (nd X) → V (nd X) := fun w => zOf (cpt X x0 w) with hΦdef
  set bf : V (nd X) → Frame X.Ψ r := fun w => bOf (cpt X x0 w) with hbfdef
  have hΦ : DifferentiableOn ℂ Φ U := hzd.comp hcd.differentiableOn fun w hw => hw
  have hbf : DifferentiableOn ℂ bf U := hbd.comp hcd.differentiableOn fun w hw => hw
  have hΦz : Φ z = 0 := h0.2.1
  have hdet := GlobalTheory.FrameMeasureClosed.kapGG_holds r X x0 x1 1 U Φ bf hU hΦ (fun w hw =>
    ⟨hw.1, (hsplit _ hw.1 hw.2).2.1, by
      rw [LeviTransfer.left_act_one]; exact (hsplit _ hw.1 hw.2).2.2⟩) z hzU
  have hdet' : (fderiv ℂ Φ z).det ≠ 0 := by
    rw [hdet]; exact LeviTransfer.borel_char_ne_zero (hsplit _ hz h0.1).2.1 _
  have hinj : Function.Injective (fderiv ℂ Φ z) := by
    have hu : IsUnit ((fderiv ℂ Φ z : V (nd X) →L[ℂ] V (nd X)) : V (nd X) →ₗ[ℂ] V (nd X)) :=
      (LinearMap.isUnit_iff_isUnit_det _).2 (Ne.isUnit hdet')
    exact LinearMap.ker_eq_bot.1 ((LinearMap.isUnit_iff_ker_eq_bot _).1 hu)
  have hΦ2 : ContDiffOn ℂ 2 Φ U := by
    rw [contDiffOn_piLp]
    intro i
    exact (contDiffOn_of_differentiableOn _ _ U hU
      ((differentiableOn_piLp 2).1 hΦ i)).of_le HE.two_le_inf
  refine ⟨x1, (WithLp.linearEquiv 2 ℂ (Fin (nd X) → ℂ)).toLinearMap ∘ₗ
    ((fderiv ℂ Φ z : V (nd X) →L[ℂ] V (nd X)) : V (nd X) →ₗ[ℂ] V (nd X)) ∘ₗ
    (WithLp.linearEquiv 2 ℂ (Fin (nd X) → ℂ)).symm.toLinearMap, ho, ?_, ?_⟩
  · exact (WithLp.linearEquiv 2 ℂ (Fin (nd X) → ℂ)).injective.comp
      (hinj.comp (WithLp.linearEquiv 2 ℂ (Fin (nd X) → ℂ)).symm.injective)
  intro la u hu hg0 ξ
  have hch : DifferentiableOn ℂ (fun w => bchar la (bf w)) U := by
    classical
    intro w hw
    unfold bchar
    refine DifferentiableAt.differentiableWithinAt ?_
    refine (HasFDerivAt.finsetProd (g' := fun τ => fderiv ℂ (fun w => ∏ i, bf w τ i i ^ la τ i) w)
      fun τ _ => DifferentiableAt.hasFDerivAt ?_).differentiableAt
    refine (HasFDerivAt.finsetProd (g' := fun i => fderiv ℂ (fun w => bf w τ i i ^ la τ i) w)
      fun i _ => DifferentiableAt.hasFDerivAt ?_).differentiableAt
    have hw' : DifferentiableAt ℂ bf w := hbf.differentiableAt (hU.mem_nhds hw)
    have hi : DifferentiableAt ℂ (fun w => bf w τ i i) w :=
      differentiableAt_pi.1 (differentiableAt_pi.1 (differentiableAt_pi.1 hw' τ) i) i
    have hzp : DifferentiableAt ℂ (fun t : ℂ => t ^ la τ i) (bf w τ i i) :=
      differentiableAt_zpow.2 (Or.inl (LeviTransfer.borel_diag_ne_zero (hsplit _ hw.1 hw.2).2.1 τ i))
    exact DifferentiableAt.comp (g := fun t : ℂ => t ^ la τ i) w hzp hi
  have hchz : ContDiffAt ℂ 2 (fun w => bchar la (bf w)) z :=
    (HE.contDiffAt_of_punct hU hch hzU).of_le HE.two_le_inf
  have hne : bchar la (bf z) ≠ 0 := LeviTransfer.borel_char_ne_zero (hsplit _ hz h0.1).2.1 _
  have hev : (fun w => ((u (cpt X x0 w) : ℝ) : ℂ)) =ᶠ[𝓝 z]
      fun w => ((u (cpt X x1 (Φ w)) + Real.log (Complex.normSq (bchar la (bf w))) : ℝ) : ℂ) := by
    filter_upwards [hU.mem_nhds hzU] with w hw
    obtain ⟨h1, h2, h3⟩ := hsplit _ hw.1 hw.2
    rw [← hu _ h1 _ h2, ← h3]
  have hg : ContDiffAt ℝ 2 (fun w => u (cpt X x1 w)) (Φ z) := by rwa [hΦz]
  have h1 : ContDiffAt ℝ 2 (fun w => u (cpt X x1 (Φ w))) z :=
    hg.comp z ((hΦ2.contDiffAt (hU.mem_nhds hzU)).restrict_scalars ℝ)
  have h2 : ContDiffAt ℝ 2 (fun w => Real.log (Complex.normSq (bchar la (bf w)))) z :=
    (HE.normSq_contDiffAt hchz).log (Complex.normSq_pos.2 hne).ne'
  have hgC : ContDiffAt ℝ 2 (fun w => ((u (cpt X x1 w) : ℝ) : ℂ)) (Φ z) :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp _ hg
  have hc := RGF.gc_leviV_comp _ _ _ Φ U hU z hzU hΦ2 hgC ξ
  rw [hΦz] at hc
  unfold lev
  rw [leviV_congr hev, Y.LocalMaximumSecondDerivative.leviV_ofReal_add h1 h2,
    HE.levi_logNormSq_zero_at _ z hchz hne ξ, add_zero]
  exact congrArg Complex.re hc

def diagForm (X : Data E r) (la : Wt X.Ψ r) (ξ : Fin (nd X) → ℂ) : ℝ :=
  ∑ e : Ent X, sgn X.p0 e.2.1.1 * sgn X.p0 e.2.1.2 *
    ((la e.1 e.2.1.2 : ℝ) - (la e.1 e.2.1.1 : ℝ)) * ‖ξ (Fintype.equivFin (Ent X) e)‖ ^ 2

theorem transfer (X : Data E r) (x0 : Frame X.Ψ r) (z : V (nd X)) (hz : cpt X x0 z ∈ X.dom) :
    ∃ (x1 : Frame X.Ψ r) (D : (Fin (nd X) → ℂ) →ₗ[ℂ] (Fin (nd X) → ℂ)), IsOrth X x1 ∧
      Function.Injective D ∧
      (∀ la ξ, curv X x0 la z ξ = curv X x1 la 0 (D ξ)) ∧
      (∀ la ξ, curv X x0 la z ξ = diagForm X la (D ξ)) ∧
      ∀ u : Frame X.Ψ r → ℝ, (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, u (rmul x b) = u x) →
        ContDiffOn ℝ ∞ u X.dom → ∀ ξ, lev X x0 u z ξ = lev X x1 u 0 (D ξ) := by
  obtain ⟨x1, D, ho, hD, h⟩ := levi_transfer X x0 z hz
  have h0 := IW.zero_mem_OmF X x1 ho
  have h1 : ∀ la ξ, curv X x0 la z ξ = curv X x1 la 0 (D ξ) := fun la =>
    h la _ (fun x hx b hb => LeviTransfer.metric_rmul GlobalTheory.NormFactor.nfac_transform.1 X la hx hb)
      ((IW.phla_cpt_cdAt X x1 h0 la).of_le HE.two_le_inf)
  refine ⟨x1, D, ho, hD, h1, fun la ξ => (h1 la ξ).trans
    (GlobalTheory.LeviZero.levi_phla_zero r X la x1 ho _), fun u hu hs => h 0 u
      (fun x hx b hb => by simp [hu x hx b hb, bchar]) ?_⟩
  exact ((chart_smooth X hs x1).contDiffAt ((ExF.isOpen_OmF X x1).mem_nhds h0)).of_le HE.two_le_inf

theorem diagForm_lin (X : Data E r) (a b : ℤ) (la la' : Wt X.Ψ r) (ξ : Fin (nd X) → ℂ) :
    diagForm X (a • la + b • la') ξ = a * diagForm X la ξ + b * diagForm X la' ξ := by
  simp only [diagForm, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

theorem curv_lin (X : Data E r) {x0 : Frame X.Ψ r} {z : V (nd X)} (hz : cpt X x0 z ∈ X.dom)
    (a b : ℤ) (la la' : Wt X.Ψ r) (ξ : Fin (nd X) → ℂ) :
    curv X x0 (a • la + b • la') z ξ = a * curv X x0 la z ξ + b * curv X x0 la' z ξ := by
  obtain ⟨x1, D, -, -, -, h, -⟩ := transfer X x0 z hz
  rw [h, h, h, diagForm_lin]

theorem curvDe_eq_omRh (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0) {z : V (nd X)}
    (hz : z ∈ OmF X x0) (ξ : Fin (nd X) → ℂ) : curvDe X x0 z ξ = omRh X x0 z ξ := by
  obtain ⟨x1, D, -, -, -, h, -⟩ := transfer X x0 z hz
  have e : omRh X x0 z ξ = curv X x0 (CurvMargin.blockWt X) z ξ := CurvMargin.leviRh_eq X x0 ho hz ξ
  rw [e, curvDe, h, h, diagForm, diagForm, Finset.sum_div]
  refine Finset.sum_congr rfl fun e _ => ?_
  simp only [de2, CurvMargin.blockWt]
  split_ifs <;> push_cast <;> ring

theorem margin_of_gaps (X : Data E r) (hp : 0 < X.p0) (la : Wt X.Ψ r) (m : ℝ)
    (hgap : ∀ τ a b, IsGap X a b → la τ b ≤ la τ a)
    (hpair : ∀ τ (a b : Fin r), (a : ℕ) = 0 → (b : ℕ) + 1 = r → m ≤ (la τ b : ℝ) - la τ a)
    {x0 : Frame X.Ψ r} (ho : IsOrth X x0) {z : V (nd X)} (hz : z ∈ OmF X x0)
    (ξ : Fin (nd X) → ℂ) : m * omRh X x0 z ξ ≤ curv X x0 la z ξ := by
  have mono : ∀ τ (k : ℕ) (i j : Fin r), (j : ℕ) = i + k → ((j : ℕ) < X.p0 ∨ X.p0 ≤ (i : ℕ)) →
      la τ j ≤ la τ i := by
    intro τ k
    induction k with
    | zero => intro i j h _; rw [show j = i from Fin.ext h]
    | succ k ih =>
      intro i j h h'
      have hl : (i : ℕ) + k < r := by have := j.isLt; omega
      exact (hgap τ ⟨i + k, hl⟩ j ⟨h, by omega⟩).trans (ih i ⟨i + k, hl⟩ rfl (by simp only; omega))
  refine (CurvMargin.curv_and_margin GlobalTheory.LeviZero.levi_phla_zero
    (LeviTransfer.levi_transfer GlobalTheory.FrameMeasureClosed.kapGG_holds
      GlobalTheory.NormFactor.nfac_transform)).2 r X la m
    (fun τ i j hij hj => mono τ (j - i) i j (by have : (i : ℕ) ≤ j := hij; omega) (Or.inl hj))
    (fun τ i j hi hij => mono τ (j - i) i j (by have : (i : ℕ) ≤ j := hij; omega) (Or.inr hi))
    (fun τ i j hi hj => ?_) x0 ho z hz ξ
  have hr : 0 < r := i.pos
  have h1 := mono τ i ⟨0, hr⟩ i (by simp) (Or.inl hi)
  have h2 := mono τ (r - 1 - j) j ⟨r - 1, by omega⟩ (by have := j.isLt; simp only; omega) (Or.inr hj)
  have h3 := hpair τ ⟨0, hr⟩ ⟨r - 1, by omega⟩ rfl (by simp only; omega)
  have h1' : (la τ i : ℝ) ≤ la τ ⟨0, hr⟩ := by exact_mod_cast h1
  have h2' : (la τ ⟨r - 1, by omega⟩ : ℝ) ≤ la τ j := by exact_mod_cast h2
  linarith

theorem curvDe_nonneg (X : Data E r) {x0 : Frame X.Ψ r} {z : V (nd X)} (hz : cpt X x0 z ∈ X.dom)
    (ξ : Fin (nd X) → ℂ) : 0 ≤ curvDe X x0 z ξ := by
  obtain ⟨x1, D, -, -, -, h, -⟩ := transfer X x0 z hz
  rw [curvDe, h, diagForm]
  refine div_nonneg (Finset.sum_nonneg fun e _ => mul_nonneg ?_ (by positivity)) two_pos.le
  have : (e.2.1.2 : ℕ) < e.2.1.1 := e.2.2
  simp only [de2, sgn]
  split_ifs <;> first | omega | norm_num

section Weights

variable {X : Data E r} (w : Weights X)

theorem second_degree_eq_on_gap {a b : Fin r} (h : IsGap X a b) (τ : X.Ψ) : de2 X τ a = de2 X τ b := by
  obtain ⟨h1, h2⟩ := h
  simp only [de2]
  split_ifs <;> first | rfl | omega

theorem gap_rem (τ : X.Ψ) (a b : Fin r) (h : IsGap X a b) : w.rem τ b ≤ w.rem τ a := by
  have h2 := (w.gap_div τ a b h).1
  have e : ((b : ℕ) : ℤ) = (a : ℕ) + 1 := by have := h.1; omega
  simp only [Weights.rem, Weights.Fp, Weights.L, frameWt, kapW, Pi.add_apply, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul, second_degree_eq_on_gap h τ, e]
  linarith

end Weights

theorem isInv_iff (X : Data E r) (u : Frame X.Ψ r → ℝ) : IsInv X u ↔ IsInvFn X u := by
  constructor
  · rintro ⟨h1, h2⟩ γ hγ x hx b hb
    rw [h2 γ hγ _ (OrthogonalFrameDomain.rmul_mem_dom X hx hb), h1 x hx b hb]
  · intro h
    refine ⟨fun x hx b hb => ?_, fun γ hγ x hx => ?_⟩
    · simpa only [LeviTransfer.left_act_one] using h 1 X.Γ.one_mem x hx b hb
    · simpa only [ExtFPf.rmul_oneF] using h γ hγ x hx _ (ExtFPf.oneF_mem X)

theorem mem_SS_iff (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) :
    P ∈ X.SS la ↔ P ∈ X.SSgt la 0 := ⟨ss_sub_ssgt0 X la, fun h => h.1⟩

theorem pnorm_nonneg (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) :
    0 ≤ X.pnorm la P x := by
  unfold Data.pnorm
  positivity

theorem lower_iff (X : Data E r) (la : Wt X.Ψ r) {N : ℕ} (w : Fin N → Frame X.Ψ r → ℂ) (c : ℝ)
    (ph : Frame X.Ψ r → ℝ) :
    (∃ C : ℝ, ∀ x ∈ X.dom, Real.exp (-(C + c * ph x)) ≤ famNorm X la w x) ↔
      ∃ K : ℝ, ∀ x ∈ X.dom, Real.exp (-(2 * c * ph x)) ≤ K * ∑ k, X.pnorm la (w k) x ^ 2 := by
  have hs : ∀ x, 0 ≤ ∑ k, X.pnorm la (w k) x ^ 2 := fun x => by positivity
  have he : ∀ C x, Real.exp (-(2 * c * ph x)) = Real.exp (2 * C) * Real.exp (-(C + c * ph x)) ^ 2 :=
    fun C x => by rw [sq, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
  constructor
  · rintro ⟨C, h⟩
    refine ⟨Real.exp (2 * C), fun x hx => ?_⟩
    rw [he C]
    exact mul_le_mul_of_nonneg_left ((Real.le_sqrt (Real.exp_pos _).le (hs x)).1 (h x hx))
      (Real.exp_pos _).le
  · rintro ⟨K, h⟩
    refine ⟨K / 2, fun x hx => (Real.le_sqrt (Real.exp_pos _).le (hs x)).2 ?_⟩
    have h1 := h x hx
    rw [he (K / 2)] at h1
    have h2 : K ≤ Real.exp (2 * (K / 2)) := by have := Real.add_one_le_exp (2 * (K / 2)); linarith
    exact le_of_mul_le_mul_left (h1.trans (mul_le_mul_of_nonneg_right h2 (hs x))) (Real.exp_pos _)

theorem upper_iff (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) {i : ℕ} (hi : 0 < i)
    (ph : Frame X.Ψ r → ℝ) :
    (∃ C : ℝ, ∀ x ∈ X.dom, X.pnorm la P x ≤ Real.exp (-(i * (ph x - C)))) ↔
      ∃ K : ℝ, ∀ x ∈ X.dom, X.pnorm la P x ^ 2 ≤ K * Real.exp (-(2 * i * ph x)) := by
  have he : ∀ C x, Real.exp (-(i * (ph x - C))) ^ 2 =
      Real.exp (2 * i * C) * Real.exp (-(2 * i * ph x)) :=
    fun C x => by rw [sq, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hi' : (0 : ℝ) < i := by exact_mod_cast hi
  constructor
  · rintro ⟨C, h⟩
    refine ⟨Real.exp (2 * i * C), fun x hx => ?_⟩
    rw [← he C]
    exact pow_le_pow_left₀ (pnorm_nonneg X la P x) (h x hx) 2
  · rintro ⟨K, h⟩
    refine ⟨K / (2 * i), fun x hx => ?_⟩
    refine (pow_le_pow_iff_left₀ (pnorm_nonneg X la P x) (Real.exp_pos _).le two_ne_zero).1 ?_
    rw [he, mul_div_cancel₀ _ (by positivity)]
    have h2 : K ≤ Real.exp K := by have := Real.add_one_le_exp K; linarith
    exact (h x hx).trans (mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le)

theorem bdd_of_upper (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (i : ℕ)
    {ph : Frame X.Ψ r → ℝ} (h0 : ∀ x ∈ X.dom, 0 ≤ ph x)
    (h : ∃ C : ℝ, ∀ x ∈ X.dom, X.pnorm la P x ≤ Real.exp (-(i * (ph x - C)))) :
    ∃ C : ℝ, ∀ x ∈ X.dom, X.pnorm la P x ≤ C := by
  obtain ⟨C, h⟩ := h
  refine ⟨Real.exp (i * C), fun x hx => (h x hx).trans (Real.exp_le_exp.2 ?_)⟩
  have : 0 ≤ (i : ℝ) * ph x := mul_nonneg (Nat.cast_nonneg _) (h0 x hx)
  linarith

theorem depth_iff (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) {ξ : Fin r → E} (hξ : X.IsIso ξ)
    (τ : X.Ψ) : X.c τ * X.maj x τ (Data.emb τ.1 ξ) ≤ 1 ↔ 1 ≤ X.tt ξ x τ := by
  have h := mul_pos (MajorantFamilyNorms.c_pos X τ) (X.maj_pos hx τ (emb_ne_zero τ.1 hξ.2.2))
  rw [Data.tt, le_div_iff₀ h, one_mul]

theorem one_le_rd (X : Data E r) : 1 ≤ rd X := by
  apply Real.one_le_rpow _ (by positivity)
  have : (1 : ℤ) ≤ |discr E| := Int.one_le_abs (discr_ne_zero E)
  exact_mod_cast this

theorem card_pos {X : Data E r} (h : 2 ≤ nd X) : 0 < X.Ψ.card := by
  have : 0 < nd X := by omega
  obtain ⟨e⟩ := Fintype.card_pos_iff.1 this
  exact Finset.card_pos.2 ⟨e.1.1, e.1.2⟩

section Clauses

variable {X : Data E r} (I : ThetaInputs X)

theorem T_pos (w : Weights X) : (0 : ℝ) < w.T := by
  have := w.T_forty
  exact_mod_cast (by omega : 0 < w.T)

theorem dp_pos (w : Weights X) : 0 < dp X := by
  have h1 : (0 : ℝ) < X.Ψ.card := by exact_mod_cast card_pos w.shape.D_ge
  have h2 : (0 : ℝ) < X.p0 := by exact_mod_cast w.shape.p0_pos
  unfold dp; positivity

theorem one_le_RR (X : Data E r) : 1 ≤ RR X := one_le_pow₀ (one_le_rd X)

theorem frame_theta_const_pos (w : Weights X) : 0 < w.c1 := by
  have h1 := T_pos w
  have h2 := dp_pos w
  have h3 : (0 : ℝ) < X.p0 := by exact_mod_cast w.shape.p0_pos
  have h4 := w.c_pos
  have h5 := one_le_RR X
  unfold Weights.c1; positivity

theorem frame_theta_weight_pos (w : Weights X) : 0 < a1 X := by
  have h1 : (0 : ℝ) < X.Ψ.card := by exact_mod_cast card_pos w.shape.D_ge
  have h5 := one_le_rd X
  unfold a1; positivity

theorem w_nz (x : Frame X.Ψ r) (hx : x ∈ X.dom) : ∃ k, I.w k x ≠ 0 := by
  by_contra h
  push Not at h
  obtain ⟨C, hC⟩ := I.w_lower
  have := (Real.exp_pos _).trans_le (hC x hx)
  simp [famNorm, Data.pnorm, h] at this

theorem base_psi_weighted_cf : cfwM X I.ps0 (a1 X) := by
  obtain ⟨C, hC⟩ := I.potential_bounded
  obtain ⟨A, hA⟩ := I.potential_decay
  refine ⟨⟨C, 0, fun x hx => by simpa using hC x hx⟩, fun η hη _ => ?_⟩
  obtain ⟨C', h⟩ := hA η hη
  exact ⟨C', A, fun x hx ξ hξ ht => h x hx ξ hξ fun τ => (depth_iff X hx hξ τ).2 (ht τ)⟩

theorem base_psi_levi_lower_bound (x0 : Frame X.Ψ r) (z : V (nd X)) (hz : cpt X x0 z ∈ X.dom) (ξ : Fin (nd X) → ℂ) :
    -(r * curvDe X x0 z ξ) ≤ lev X x0 I.ps0 z ξ := by
  obtain ⟨x1, D, ho, -, h1, -, h2⟩ := transfer X x0 z hz
  rw [h2 _ I.potential_invariant.1 I.potential_smooth, curvDe, h1]
  exact I.curvature_lower_bound x1 ho 0 (IW.zero_mem_OmF X x1 ho) _

theorem posL (x0 : Frame X.Ψ r) (z : V (nd X)) (hz : cpt X x0 z ∈ X.dom) (ξ : Fin (nd X) → ℂ)
    (hξ : ξ ≠ 0) : 0 < curv X x0 I.toWeights.L z ξ := by
  obtain ⟨x1, D, ho, hD, h1, -, -⟩ := transfer X x0 z hz
  rw [h1]
  exact I.curv_L x1 ho 0 (IW.zero_mem_OmF X x1 ho) _ fun h => hξ (hD (h.trans (map_zero D).symm))

theorem weight_margin (w : Weights X) :
    w.Fp - kapW X - nd X • w.L = (2 : ℤ) • w.L + w.rem := by
  simp only [Weights.rem]; module

theorem posF (u : ℝ) (hu : u ≤ 2 * I.T) (x0 : Frame X.Ψ r) (z : V (nd X))
    (hz : cpt X x0 z ∈ X.dom) (ξ : Fin (nd X) → ℂ) :
    curv X x0 I.toWeights.L z ξ ≤
      curv X x0 (I.toWeights.Fp - kapW X - nd X • I.toWeights.L) z ξ - u * curvDe X x0 z ξ := by
  obtain ⟨x1, D, ho, -, h1, -, -⟩ := transfer X x0 z hz
  have h0 := IW.zero_mem_OmF X x1 ho
  have h2 := I.margin_cut x1 ho 0 h0 (D ξ)
  have h3 := curvDe_nonneg X h0 (D ξ)
  have h4 := mul_le_mul_of_nonneg_right hu h3
  have h5 := mul_nonneg (T_pos I.toWeights).le h3
  rw [← curvDe_eq_omRh X ho h0] at h2
  rw [weight_margin, curvDe, h1, h1, h1]
  unfold curvDe at *
  linarith

end Clauses

end

end GlobalTheory.FrameThetaCompare
