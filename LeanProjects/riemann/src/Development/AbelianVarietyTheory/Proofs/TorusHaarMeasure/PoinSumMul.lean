import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalExponentialDecay
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.BoundedSectionAlgebra
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.KronHolPsiStatementHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfH
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfS
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.RhGradFPf
import Development.AbelianVarietyTheory.Definitions.UpperBounds.SumNormSqWPos
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MulProd
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.OfRealRpowNegLe
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ContDiffAtCompCpt
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MeasurablePhi
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.SmoothWtContDiffOn

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.Up.DivCorePf

open ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

section

variable {r : ℕ} (X : Data E r)

theorem chi_ne_zero (la : Wt X.Ψ r) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) : X.χ la γ ≠ 0 := by
  obtain ⟨n, hn, h⟩ := X.χ_fin la
  intro h0
  have := h γ hγ
  rw [h0, zero_pow hn.ne'] at this
  exact zero_ne_one this

theorem isSec_one : X.IsSec 0 (fun _ => (1 : ℂ)) := by
  refine ⟨differentiableOn_const _, fun x _ b _ => by simp [bchar], fun γ hγ x _ => ?_⟩
  have h := X.χ_add 0 0 γ hγ
  rw [add_zero] at h
  rw [mul_one]
  exact mul_left_cancel₀ (chi_ne_zero X 0 hγ) (by rw [mul_one]; exact h)

variable {X}

theorem isSec_mul {la la' : Wt X.Ψ r} {P Q : Frame X.Ψ r → ℂ} (hP : X.IsSec la P)
    (hQ : X.IsSec la' Q) : X.IsSec (la + la') (fun x => P x * Q x) := by
  refine ⟨hP.1.mul hQ.1, fun x hx b hb => ?_, fun γ hγ x hx => ?_⟩
  · simp only [hP.2.1 x hx b hb, hQ.2.1 x hx b hb, bchar_add X hb]
    ring
  · simp only [hP.2.2 γ hγ x hx, hQ.2.2 γ hγ x hx, X.χ_add la la' γ hγ]
    ring

theorem isSec_pow {L : Wt X.Ψ r} {P : Frame X.Ψ r → ℂ} (hP : X.IsSec L P) (m : ℕ) :
    X.IsSec (m • L) (fun x => P x ^ m) := by
  induction m with
  | zero => simpa using isSec_one X
  | succ m ih => simpa only [succ_nsmul, pow_succ] using isSec_mul ih hP

theorem isSec_monoM {n : ℕ} {L : Wt X.Ψ r} {s : Fin n → Frame X.Ψ r → ℂ}
    (hs : ∀ k, X.IsSec L (s k)) (α : Fin n → ℕ) : X.IsSec ((∑ k, α k) • L) (monoM X s α) := by
  have key : ∀ S : Finset (Fin n),
      X.IsSec ((∑ k ∈ S, α k) • L) (fun x => ∏ k ∈ S, s k x ^ α k) := by
    intro S
    induction S using Finset.induction_on with
    | empty => simpa using isSec_one X
    | insert a S ha ih =>
      simpa only [Finset.sum_insert ha, Finset.prod_insert ha, add_nsmul] using
        isSec_mul (isSec_pow (hs a) (α a)) ih
  exact key Finset.univ

theorem exists_extension (hExt : ExtFStatement (E := E)) {x0 : Frame X.Ψ r} (ho : IsOrth X x0)
    {la : Wt X.Ψ r} {W : Frame X.Ψ r → ℝ≥0∞} (hWL : WLower X la W) {bb : ℝ} (hbb : 0 ≤ bb)
    {F : V (nd X) → ℂ} (hF : DifferentiableOn ℂ F (OmF X x0)) (hI : InAt X x0 W bb F) :
    ∃ P : Frame X.Ψ r → ℂ, IsBEq X la P ∧ ∀ z ∈ OmF X x0, P (cpt X x0 z) = F z := by
  obtain ⟨c, hc, hWL'⟩ := hWL
  have hka1 : ∀ z ∈ OmF X x0, kaF X x0 bb z ≤ 1 := fun z hz => by
    unfold kaF
    rw [Real.exp_le_one_iff]
    have := mul_nonneg hbb (ExF.rhF_nonneg X x0 ho hz)
    linarith
  refine hExt r X x0 ho la F hF fun Cs _ _ => ?_
  have hpt : ∀ᵐ z ∂muF X x0, ENNReal.ofReal (‖F z‖ ^ 2 * Real.exp (-phla X la (cpt X x0 z))) ≤
      ENNReal.ofReal (1 / c) * (ENNReal.ofReal (‖F z‖ ^ 2 / kaF X x0 bb z) * W (cpt X x0 z)) := by
    refine (OntoH.ae_mem_Om X x0).mono fun z hz => ?_
    have hk : 0 < kaF X x0 bb z := Real.exp_pos _
    have e : ‖F z‖ ^ 2 * Real.exp (-phla X la (cpt X x0 z)) =
        1 / c * (‖F z‖ ^ 2 * (c * Real.exp (-phla X la (cpt X x0 z)))) := by field_simp
    rw [e, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
    gcongr
    · exact le_div_self (by positivity) hk (hka1 z hz)
    · exact hWL' _ hz
  refine ((setLIntegral_le_lintegral _ _).trans (lintegral_mono_ae hpt)).trans_lt ?_
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hI

theorem poin_sum_mul {ι : Type*} (S : Finset ι) {la la' : Wt X.Ψ r} {P : Frame X.Ψ r → ℂ}
    {g Q : ι → Frame X.Ψ r → ℂ} (hg : ∀ i ∈ S, X.IsSec la' (g i))
    (hP : ∀ y ∈ X.dom, P y = ∑ i ∈ S, g i y * Q i y) {x : Frame X.Ψ r} (hx : x ∈ X.dom)
    (hQ : ∀ i ∈ S, Summable fun γ : X.Γ => ‖(X.χ la γ.1)⁻¹ * Q i (lact γ.1 x)‖) :
    poin X (la + la') P x = ∑ i ∈ S, g i x * poin X la (Q i) x := by
  unfold poin
  have e : ∀ γ : X.Γ, (X.χ (la + la') γ.1)⁻¹ * P (lact γ.1 x) =
      ∑ i ∈ S, g i x * ((X.χ la γ.1)⁻¹ * Q i (lact γ.1 x)) := by
    intro γ
    rw [hP _ (OntoS.dom_lact X γ.2 hx), Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have h1 := chi_ne_zero X la γ.2
    have h2 := chi_ne_zero X la' γ.2
    rw [(hg i hi).2.2 γ.1 γ.2 x hx, X.χ_add la la' γ.1 γ.2]
    field_simp
  rw [tsum_congr e, Summable.tsum_finsetSum fun i hi => ((hQ i hi).of_norm).mul_left (g i x)]
  exact Finset.sum_congr rfl fun i _ => tsum_mul_left

end

theorem divCore_of :
    (NfacRmulStatement (E := E) ∧ NfacLactStatement (E := E) ∧ PnormInvStatement (E := E)) →
      PoinStatement (E := E) → OntoStatement (E := E) → ExtFStatement (E := E) →
      MeasInvStatement (E := E) → DivCoreStatement (E := E) := by
  intro hN hPo hOn hExt hMI r X Xa Fl hPD hfin ⟨bb, m, hbb, hbm, hmar⟩ _ _ _ hcusp ⟨K, gs, hgs⟩
    δ t ht _ x0 ho FF hFF f hf hfi cc hvan
  have h2 := Xa.n_ge
  have hT := Xa.T_ge
  have hnT : nd X ≤ Xa.T := by nlinarith
  have hbb0 : 0 ≤ bb := le_trans (by positivity) hbb.le
  have hbm' : bb ≤ m := by
    have : 0 ≤ bb ^ 2 * ((X.Ψ.card * min X.p0 (r - X.p0) : ℕ) : ℝ) := by positivity
    linarith
  have hs : ∀ k, X.IsSec Xa.L (Fl.s k) := fun k => (Fl.s_van k).1.1.1
  obtain ⟨hg, hgC⟩ := GlobalTheory.LeadBound.main r X Xa Fl Xa.Fp Xa.T (Xa.T - nd X) δ (by omega) t ht cc
  set g := leadM X Fl.s Fl.w0 t Xa.T (Xa.T - nd X) cc with hgdef
  have hf' : X.IsBddSec (Xa.Fp + Xa.T • Xa.L) (fun x => f x - g x) := by
    have h := bdd_add X hf.1 (bdd_smul X (-1) hg)
    have e : f + (-1 : ℂ) • g = fun x => f x - g x := by
      funext x
      simp [sub_eq_add_neg]
    rwa [e] at h
  have hIn := DivInFFPf.divInFF_of hN hMI r X Xa Fl hfin x0 ho FF hFF f g hf.1.1 hg.1 hfi hgC hvan
  obtain ⟨hMT, hLT, hET⟩ := DivMetricPf.divMetric_of hN r X Xa Fl Xa.T (by omega)
  obtain ⟨hMn, hLn, -⟩ := DivMetricPf.divMetric_of hN r X Xa Fl (nd X) (by omega)
  obtain ⟨⟨k0, z0, hz0, hz0'⟩, hLev⟩ := divLevi_holds r X Xa Fl Xa.T (by omega) x0 ho
  obtain ⟨F, P, hF, hFI, hP, hPF, hpo⟩ := hOn r X x0 ho hPD _ (Wdiv X Xa Fl Xa.T) (Psdiv X Xa Fl Xa.T)
    (fun z => Fl.s k0 (cpt X x0 z)) bb m hMT hLT hbb hbm (OntoB.hol_comp X x0 (hs k0).1)
    ⟨z0, hz0, hz0'⟩ (hLev k0).1 (fun z hz hz' => hET _ hz ⟨k0, hz'⟩)
    (fun z hz hz' ξ => (hmar x0 ho z hz ξ).trans ((hLev k0).2 z hz hz' ξ)) hcusp FF hFF
    ⟨K, gs, fun f hf _ => hgs f hf⟩ _ (hcusp _ hf') hIn
  obtain ⟨H, hH, hFH⟩ := divUp_holds r X Xa Fl x0 ho bb
    (fun z hz ξ => (mul_le_mul_of_nonneg_right hbm'
      (OntoB.levi_rh_nonneg RhGradFStatement_holds ho hz ξ)).trans (hmar x0 ho z hz ξ))
    ⟨k0, z0, hz0, hz0'⟩ F hF hFI
  choose Q hQ hQH using fun α => exists_extension hExt ho hLn hbb0 (hH α).1 (hH α).2
  have hPQ := fun α => hPo r X x0 ho hPD _ _ bb hMn hLn hbb (H α) (Q α) (hH α).1 (hH α).2 (hQ α) (hQH α)
  have hmono : ∀ α ∈ Finset.Nat.antidiagonalTuple (nd X) (Xa.T - nd X),
      X.IsSec ((Xa.T - nd X) • Xa.L) (monoM X Fl.s α) := by
    intro α hα
    have h := isSec_monoM hs α
    rwa [Finset.Nat.mem_antidiagonalTuple.1 hα] at h
  have hwt : Xa.Fp + Xa.T • Xa.L = Xa.Fp + nd X • Xa.L + (Xa.T - nd X) • Xa.L := by
    rw [add_assoc, ← add_nsmul, Nat.add_sub_cancel' hnT]
  have hsum : ∀ y ∈ X.dom, P y = ∑ α ∈ Finset.Nat.antidiagonalTuple (nd X) (Xa.T - nd X),
      monoM X Fl.s α y * Q α y := by
    intro y hy
    refine sub_eq_zero.1 (bigCellStatement_holds r X x0 ho (Xa.Fp + Xa.T • Xa.L)
      (fun y => P y - ∑ α ∈ Finset.Nat.antidiagonalTuple (nd X) (Xa.T - nd X),
        monoM X Fl.s α y * Q α y) ⟨?_, fun x hx b hb => ?_⟩ (fun z hz => ?_) y hy)
    · exact hP.1.sub (DifferentiableOn.fun_sum fun α hα => (hmono α hα).1.mul (hQ α).1)
    · beta_reduce
      rw [mul_sub, hP.2 x hx b hb, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun α hα => ?_
      rw [(hmono α hα).2.1 x hx b hb, (hQ α).2 x hx b hb, hwt,
        bchar_add X hb _ ((Xa.T - nd X) • Xa.L)]
      ring
    · beta_reduce
      rw [hPF z hz, hFH z hz, sub_eq_zero]
      exact Finset.sum_congr rfl fun α _ => by rw [hQH α z hz]
  refine ⟨fun α => poin X (Xa.Fp + nd X • Xa.L) (Q α), fun α _ => (hPQ α).2.1, fun x hx => ?_⟩
  rw [← hpo x hx, hwt]
  exact poin_sum_mul _ hmono hsum hx fun α _ => (hPQ α).1 x hx

end GlobalTheory.Up.DivCorePf
