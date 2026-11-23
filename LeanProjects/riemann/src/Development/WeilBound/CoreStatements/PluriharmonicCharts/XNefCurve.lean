import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
import Development.AutomorphicSpectrum.Proofs.MetricProofs.DegreeGenericOfDegree
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SamePotBlock
import Development.AutomorphicSpectrum.Proofs.MetricProofs.CompChartEventuallyEq
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MongeAmpereIntegralCongrPotentials
import Development.WeilBound.CoreStatements.PluriharmonicCharts.XResLift
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.MultiIsProjVarFOfRatDiv
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridge
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedF
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ExistsLinearIndependentOfGenerates
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.AssemblyBridgeFull
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

namespace PositivityTheory.Xgp.nef_curve

open GlobalTheory.CompanionTheory.Ar.PB.FA.BlockPot

theorem holoMap_comp {e₁ e₂ e₃ : ℕ} {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] {C : FinHolAtlas e₁ Z} {B : FinHolAtlas e₂ Y} {A : FinHolAtlas e₃ X}
    {g : Z → Y} {f : Y → X} (hg : HoloMap C B g) (hf : HoloMap B A f) : HoloMap C A (f ∘ g) := by
  refine ⟨hf.1.comp hg.1, fun j k t ht => ?_⟩
  obtain ⟨ht1, ht2⟩ := ht
  obtain ⟨m, hm⟩ := B.cover (g ((C.chart j).symm t))
  have h1 : AnalyticAt ℂ (B.chart m ∘ g ∘ (C.chart j).symm) t := hg.2 j m t ⟨ht1, hm⟩
  have hu : (B.chart m).symm ((B.chart m ∘ g ∘ (C.chart j).symm) t) = g ((C.chart j).symm t) :=
    (B.chart m).left_inv hm
  have h2 : AnalyticAt ℂ (A.chart k ∘ f ∘ (B.chart m).symm)
      ((B.chart m ∘ g ∘ (C.chart j).symm) t) :=
    hf.2 m k _ ⟨(B.chart m).map_source hm, by
      rw [Set.mem_preimage, hu]; exact ht2⟩
  refine (h2.comp h1).congr ?_
  have hc : ContinuousAt (g ∘ (C.chart j).symm) t :=
    hg.1.continuousAt.comp ((C.chart j).continuousAt_symm ht1)
  filter_upwards [hc ((B.chart m).open_source.mem_nhds hm)] with t' ht'
  have ht'' : g ((C.chart j).symm t') ∈ (B.chart m).source := ht'
  simp only [Function.comp]
  rw [(B.chart m).left_inv ht'']

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem smooth_comb {σ : Type} [Fintype σ] {A : σ → HermLine ι} (hA : ∀ a, IsSmoothHerm (A a))
    (n : σ → ℤ) : IsSmoothHerm (GlobalTheory.CompanionTheory.Ar.PB.combLine A n) := by
  refine contDiffOn_prod fun a _ => ?_
  intro z hz
  have h0 : (A a).h z ≠ 0 := ((A a).pos z hz).ne'
  have hf := hA a z hz
  have key : ∀ m : ℤ, ContDiffWithinAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => (A a).h z ^ m)
      {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} z := by
    intro m
    cases m with
    | ofNat k => simpa only [Int.ofNat_eq_natCast, zpow_natCast] using hf.pow k
    | negSucc k =>
      simp only [zpow_negSucc]
      exact (hf.pow (k + 1)).inv (pow_ne_zero _ h0)
  exact key _

theorem samePot_lift {P J P' J' : Ideal (MRing ι)} {e e' : ℕ} (R : AnLogRes P J e) (R' : AnLogRes P' J' e')
    (h : R.X → R'.X) (hh : HoloMap R.A R'.A h) (L : HermLine ι)
    (hO : ∀ x, SameOrbit (R'.lift (h x) (h x)) (R.lift x x)) :
    SamePot R.A Set.univ (potOf R L) ((potOf R' L).pullback h hh.1) := by
  intro x _
  have hb : IsBlockMap (ι := ι) (ι' := ι) id id := isBlockMap_id
  have hxU : x ∈ R.U x := R.mem_U x
  have hxU' : h x ∈ R'.U (h x) := R'.mem_U _
  obtain ⟨cx, hcx, ex⟩ := orbit_near R R' h hb hO hxU hxU'
  choose m hm using (R.mem x x hxU).1
  let den : K → R.X → ℂ := fun k y => R.lift x y ⟨k, m k⟩
  let num : K → R.X → ℂ := fun k y => R'.lift (h x) (h y) ⟨k, m k⟩
  let rat : K → R.X → ℂ := fun k y => num k y / den k y / cx k
  have hdenH : ∀ k, R.A.HoloOn (R.U x) (den k) := fun k => R.holo x _
  have hnumH : ∀ k, R.A.HoloOn (h ⁻¹' R'.U (h x)) (num k) := fun k =>
    holoOn_comp hh (R'.holo (h x) ⟨k, m k⟩)
  have hdenC : ∀ k, ContinuousAt (den k) x := fun k => continuousAt_of_holoOn (hdenH k) hxU
  have hnumC : ∀ k, ContinuousAt (num k) x := fun k => continuousAt_of_holoOn (hnumH k) hxU'
  have hratC : ∀ k, ContinuousAt (rat k) x := fun k =>
    ((hnumC k).div (hdenC k) (hm k)).div continuousAt_const (hcx k)
  have hrat1 : ∀ k, rat k x = 1 := by
    intro k
    have := ex ⟨k, m k⟩
    have h1 : den k x ≠ 0 := hm k
    have h2 := hcx k
    simp only [rat, num, den, id] at h1 this ⊢
    rw [this]
    field_simp
  have hev : ∀ᶠ y in 𝓝 x, y ∈ R.U x ∧ h y ∈ R'.U (h x) ∧ ∀ k, den k y ≠ 0 ∧ rat k y ∈ Complex.slitPlane := by
    have e1 : ∀ᶠ y in 𝓝 x, y ∈ R.U x := (R.isOpen_U x).mem_nhds hxU
    have e2 : ∀ᶠ y in 𝓝 x, h y ∈ R'.U (h x) := ((R'.isOpen_U (h x)).preimage hh.1).mem_nhds hxU'
    have e3 : ∀ᶠ y in 𝓝 x, ∀ k, den k y ≠ 0 ∧ rat k y ∈ Complex.slitPlane := by
      refine eventually_all.2 fun k => ((hdenC k).eventually_ne (hm k)).and ?_
      exact (hratC k).eventually_mem (Complex.isOpen_slitPlane.mem_nhds (by
        simpa only [hrat1 k] using Complex.one_mem_slitPlane))
    exact e1.and (e2.and e3)
  obtain ⟨V, hVs, hVo, hxV⟩ := mem_nhds_iff.1 hev
  refine ⟨V, hVo, hxV, fun y => -∑ k, (L.a k : ℂ) * (Complex.log (rat k y) + (Real.log ‖cx k‖ : ℂ)), ?_, ?_⟩
  · intro j u hu
    obtain ⟨hy1, hy2, hy3⟩ := hVs hu.2
    have hd : ∀ k, AnalyticAt ℂ (fun u => den k ((R.A.chart j).symm u)) u := fun k =>
      hdenH k j u ⟨hu.1, hy1⟩
    have hn : ∀ k, AnalyticAt ℂ (fun u => num k ((R.A.chart j).symm u)) u := fun k =>
      hnumH k j u ⟨hu.1, hy2⟩
    have hr : ∀ k, AnalyticAt ℂ (fun u => rat k ((R.A.chart j).symm u)) u := fun k =>
      ((hn k).div (hd k) (hy3 k).1).div analyticAt_const (hcx k)
    have hl : ∀ k, AnalyticAt ℂ (fun u => (L.a k : ℂ) * (Complex.log (rat k ((R.A.chart j).symm u)) +
        (Real.log ‖cx k‖ : ℂ))) u := fun k =>
      analyticAt_const.mul (((hr k).clog (hy3 k).2).add analyticAt_const)
    exact (Finset.analyticAt_fun_sum Finset.univ fun k _ => hl k).neg
  · intro y hy
    obtain ⟨hy1, hy2, hy3⟩ := hVs hy
    obtain ⟨c, hc, ec⟩ := orbit_near R R' h hb hO hy1 hy2
    have hw : R'.lift (h x) (h y) = fun p => c p.1 * R.lift x y p := funext fun p => ec p
    have hrat : ∀ k, rat k y = c k / cx k := by
      intro k
      have h1 : den k y ≠ 0 := (hy3 k).1
      have h2 := ec ⟨k, m k⟩
      simp only [rat, num, den, id] at h1 h2 ⊢
      rw [h2]
      field_simp
    have hpos : 0 < L.h (R.lift x y) := L.pos _ (R.mem x y hy1).1
    have hprod : (∏ k, ‖c k‖ ^ L.a k) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.2 (hc k))
    have hL : Real.log (L.h (R'.lift (h x) (h y))) =
        (∑ k, (L.a k : ℝ) * Real.log ‖c k‖) + Real.log (L.h (R.lift x y)) := by
      rw [hw, L.smul c _ hc, Real.log_mul hprod hpos.ne', Real.log_prod]
      · simp only [Real.log_zpow]
      · exact fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.2 (hc k))
    have hG : (-∑ k, (L.a k : ℂ) * (Complex.log (rat k y) + (Real.log ‖cx k‖ : ℂ))).re =
        -∑ k, (L.a k : ℝ) * Real.log ‖c k‖ := by
      rw [Complex.neg_re, Complex.re_sum]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      have hck := norm_ne_zero_iff.2 (hc k)
      have hcxk := norm_ne_zero_iff.2 (hcx k)
      have hcast : ((L.a k : ℤ) : ℂ) = (((L.a k : ℤ) : ℝ) : ℂ) := by push_cast; rfl
      rw [hrat k, hcast, Complex.re_ofReal_mul, Complex.add_re, Complex.log_re, Complex.ofReal_re, norm_div,
        Real.log_div hck hcxk]
      ring
    show Real.log (L.h (R.lift x y)) - Real.log (L.h (R'.lift (h x) (h y))) = _
    rw [hL, hG]
    ring

section Mass

variable {e e' : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

theorem samePot_trans {A : FinHolAtlas e X} {P Q T : LocPot X} (h1 : SamePot A Set.univ P Q)
    (h2 : SamePot A Set.univ Q T) : SamePot A Set.univ P T := by
  intro x hx
  obtain ⟨V, hV, hxV, G, hG, e1⟩ := h1 x hx
  obtain ⟨V', hV', hxV', G', hG', e2⟩ := h2 x hx
  refine ⟨V ∩ V', hV.inter hV', ⟨hxV, hxV'⟩, fun y => G y + G' y, fun j u hu => ?_, fun y hy => ?_⟩
  · exact (hG j u ⟨hu.1, hu.2.1⟩).add (hG' j u ⟨hu.1, hu.2.2⟩)
  · rw [Complex.add_re, ← e1 y hy.1, ← e2 y hy.2]
    ring

theorem samePot_pullback {A : FinHolAtlas e X} {B : FinHolAtlas e' Y} {h : Y → X} (hh : HoloMap B A h)
    {P Q : LocPot X} (h1 : SamePot A Set.univ P Q) :
    SamePot B Set.univ (P.pullback h hh.1) (Q.pullback h hh.1) := by
  intro x _
  obtain ⟨V, hV, hxV, G, hG, e1⟩ := h1 (h x) (Set.mem_univ _)
  exact ⟨h ⁻¹' V, hV.preimage hh.1, hxV, fun y => G (h y), holoOn_comp hh hG, fun y hy => e1 _ hy⟩

theorem isC2At_of_isPotential {A : FinHolAtlas e X} {P : LocPot X} (hP : IsPotential A P) (x : X) :
    IsTwiceDifferentiableAt A P x := by
  intro j hj
  have hm : (A.chart j).target ∩ (A.chart j).symm ⁻¹' P.U x ∈ 𝓝 (A.chart j x) :=
    ((A.chart j).isOpen_inter_preimage_symm (P.isOpen_U x)).mem_nhds ⟨(A.chart j).map_source hj, by
      simpa only [Set.mem_preimage, (A.chart j).left_inv hj] using P.mem_U x⟩
  exact ((hP.1 x j).contDiffAt hm).of_le (by norm_cast)

noncomputable def mass (B : FinHolAtlas 1 Y) (Q : LocPot Y) : ℝ := mInt B (fun _ => Q) fun _ => 1

theorem cons_eq (Q : LocPot Y) : (Fin.cons Q (Fin.elim0 : Fin 0 → LocPot Y) : Fin 1 → LocPot Y) = fun _ => Q := by
  funext j
  exact Fin.cases rfl (fun i => i.elim0) j

variable [CompactSpace Y] [T2Space Y] {B : FinHolAtlas 1 Y}

theorem mass_add {P Q : LocPot Y} (hP : IsPotential B P) (hQ : IsPotential B Q) :
    mass B (P + Q) = mass B P + mass B Q := by
  have := mIntAdd B P Q Fin.elim0 hP hQ (fun i => i.elim0) (fun _ => 1)
    (by rw [cons_eq]; exact mIntegrableCont B _ (fun _ => hP) _ continuous_const)
    (by rw [cons_eq]; exact mIntegrableCont B _ (fun _ => hQ) _ continuous_const)
  simpa only [cons_eq, mass] using this

omit [CompactSpace Y] [T2Space Y] in
theorem mass_rsmul {P : LocPot Y} (hP : IsPotential B P) (c : ℝ) : mass B (P.rsmul c) = c * mass B P := by
  have := mIntRsmul B c P Fin.elim0 hP (fun i => i.elim0) (fun _ => 1)
  simpa only [cons_eq, mass] using this

omit [CompactSpace Y] [T2Space Y] in
theorem mass_nonneg {P : LocPot Y} (hP : IsPotential B P) (h : IsPsh B P) : 0 ≤ mass B P :=
  mIntNonneg B _ (fun _ => hP) (fun _ => h) _ fun _ => zero_le_one

theorem mass_fun {P : LocPot Y} (hP : IsPotential B P) {u : Y → ℝ} (hu : B.Smooth u) :
    mass B (P + LocPot.ofFun u) = mass B P :=
  massIndep B (fun _ => P) (fun _ => u) (fun _ => hP) fun _ => hu

theorem mass_congr {P Q : LocPot Y} (h : SamePot B Set.univ P Q) (hQ : IsPotential B Q) : mass B P = mass B Q :=
  (mInt_congr_samePot 1 Y B Set.univ _ _ _ _ (fun j => by simp) (fun _ => h)
    (fun _ x _ => isC2At_of_isPotential hQ x) (fun _ _ => rfl)).1

theorem mass_sys {D : ℕ} {σ : Type} (S : AnSys D σ) {g : Y → S.X} (hg : HoloMap B S.A g) (a : σ) :
    0 ≤ mass B ((S.th a).pullback g hg.1) ∧
      ((∀ t, IsPsh S.A ((S.potT a t).rsmul (-1))) → mass B ((S.th a).pullback g hg.1) ≤ 0) := by
  obtain ⟨ht0, -, hreg⟩ := S.reg a
  have hth : IsPotential S.A (S.th a) := (S.sing a).1
  have hpb := fun (Q : LocPot S.X) hQ => isPotentialPullback S.A B g hg Q hQ
  have hpp := fun (Q : LocPot S.X) hQ =>
    (GlobalTheory.CompanionTheory.Ar.Giv.pullPsh S.A B g hg Q Set.univ (fun _ => 0) isOpen_univ hQ).2.1
  have hT : ∀ t, 0 < t → t ≤ S.t₀ → IsPotential S.A (S.potT a t) := fun t h1 h2 =>
    isPotentialAdd _ _ _ hth (isPotential_ofFun _ _ (hreg t h1 h2).1)
  have hM : ∀ t, 0 < t → t ≤ S.t₀ → mass B ((S.potT a t).pullback g hg.1) = mass B ((S.th a).pullback g hg.1) := by
    intro t h1 h2
    have hs : B.Smooth (S.phT a t ∘ g) :=
      (GlobalTheory.CompanionTheory.Ar.Giv.pullPsh S.A B g hg _ Set.univ (S.phT a t) isOpen_univ hth).1 (hreg t h1 h2).1
    exact mass_fun (hpb _ hth) hs
  constructor
  · have hlim : Tendsto (fun t : ℝ => mass B ((S.th a).pullback g hg.1) + ReciprocityTheory.AnForm.P.epsT S.C t * mass B (S.Θ.pullback g hg.1))
        (𝓝[>] 0) (𝓝 (mass B ((S.th a).pullback g hg.1) + (S.C * 0) * mass B (S.Θ.pullback g hg.1))) := by
      refine tendsto_const_nhds.add (Tendsto.mul_const _ ?_)
      have h1 : Tendsto (fun t : ℝ => Real.log (1 / t)) (𝓝[>] 0) atTop := by
        simp only [one_div]
        exact Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero
      have h2 := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
      simp only [one_mul, add_zero, pow_one] at h2
      refine ((h2.comp h1).const_mul S.C).congr fun t => ?_
      simp only [ReciprocityTheory.AnForm.P.epsT, Function.comp, mul_div_assoc]
    rw [mul_zero, zero_mul, add_zero] at hlim
    refine ge_of_tendsto hlim ?_
    filter_upwards [Ioc_mem_nhdsGT ht0] with t ht
    have hP : IsPotential S.A (S.potT a t + S.Θ.rsmul (ReciprocityTheory.AnForm.P.epsT S.C t)) :=
      isPotentialAdd _ _ _ (hT t ht.1 ht.2) (isPotentialRsmul _ _ _ S.potΘ)
    have h0 := mass_nonneg (hpb _ hP) (hpp _ hP (hreg t ht.1 ht.2).2.2.2.2.1)
    have e1 : (S.potT a t + S.Θ.rsmul (ReciprocityTheory.AnForm.P.epsT S.C t)).pullback g hg.1 =
        (S.potT a t).pullback g hg.1 + (S.Θ.pullback g hg.1).rsmul (ReciprocityTheory.AnForm.P.epsT S.C t) := rfl
    rwa [e1, mass_add (hpb _ (hT t ht.1 ht.2)) (isPotentialRsmul _ _ _ (hpb _ S.potΘ)),
      mass_rsmul (hpb _ S.potΘ), hM t ht.1 ht.2] at h0
  · intro hfl
    have hP := isPotentialRsmul _ (-1) _ (hT _ ht0 le_rfl)
    have h0 := mass_nonneg (hpb _ hP) (hpp _ hP (hfl _))
    have e1 : ((S.potT a S.t₀).rsmul (-1)).pullback g hg.1 = ((S.potT a S.t₀).pullback g hg.1).rsmul (-1) := rfl
    rw [e1, mass_rsmul (hpb _ (hT _ ht0 le_rfl)), hM _ ht0 le_rfl] at h0
    linarith

end Mass

end PositivityTheory.Xgp.nef_curve

open PositivityTheory.Xgp.nef_curve in
theorem PositivityTheory.Xgp.t_nef_curve : Inputs → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (D : ℕ) (σ : Type) [Fintype σ] (S : AnSys D σ) (P : Ideal (MRing ι)) (Re : Realis S P) (Fl : Set σ), (∀ a ∈ Fl, ∀ t, IsPsh S.A ((S.potT a t).rsmul (-1)) ∧ IsPsh S.A (S.potT a t)) → Re.J = ⊤ → ∀ n : σ → ℤ, (∀ a ∉ Fl, 0 ≤ n a) → ∀ W : Ideal (MRing ι), IsArithVar W 2 → P ≤ W → 0 ≤ geomDeg W (combLine Re.ref n) 1 := by
  intro hI K _ ι _ D σ _ S P Re Fl hFl hJ n hn W hW hPW
  classical
  obtain ⟨J', ⟨R'⟩⟩ := exists_anLogRes hI.resExists (e := 1) hW
  obtain ⟨h, hh, hO⟩ := PositivityTheory.Xgp.t_res_lift K ι P W Re.J J' D 1 Re.R R' hJ hPW
  have hg := holoMap_comp hh Re.holo
  have hdeg : ∀ a, geomDeg W (Re.ref a) 1 = mass R'.A ((S.th a).pullback (Re.π ∘ h) hg.1) := by
    intro a
    have e1 : geomDeg W (Re.ref a) 1 = mass R'.A (potOf R' (Re.ref a)) :=
      ptsIntegral_one_eq_mInt hI.resExists resBridge R' (L := fun _ => Re.ref a) hW fun _ => Re.ref_smooth a
    rw [e1]
    exact mass_congr (samePot_trans (samePot_lift R' Re.R h hh _ hO) (samePot_pullback hh (Re.ref_pot a)))
      (isPotentialPullback _ _ _ hg _ (S.sing a).1)
  let I : IFamily ℚ ι := fun V _ L => GroundTheory.Heights₂.Heights.NumbersDVR.intNum ℚ V L
  have hIf : IsFieldIntersection I := GroundTheory.Heights₂.Heights.NumbersDVR.IntNumIsFieldIntersection.full _ _ _
  have hWq : IsProjVarF (W.map (MvPolynomial.map (Int.castRingHom ℚ))) 1 :=
    GroundTheory.Heights₂.Heights.HilbertSamuel.isProjVarF_map_of_isArithVar hW
  have hup : ∀ a : K → ℤ, Function.update (fun _ : Fin 1 => (0 : K → ℤ)) 0 a = fun _ => a := by
    intro a; funext j; rw [Subsingleton.elim j 0]; simp
  let d : (K → ℤ) →+ ℤ := AddMonoidHom.mk'
    (fun a => I (W.map (MvPolynomial.map (Int.castRingHom ℚ))) 1 fun _ => a) fun a b => by
      have := ReciprocityTheory.ChartRestriction.G.AI.I1.multilin_thm ℚ ι I hIf _ 1 (fun _ => 0) 0 a b hWq
      simpa only [hup] using this
  have hd : ∀ L : HermLine ι, IsSmoothHerm L → geomDeg W L 1 = d L.a := fun L hL =>
    GlobalTheory.CompanionTheory.Ar.Giv.degreeGeneric_of_degree hI.degree K ι W 1 (fun _ => L) hW fun _ => hL
  have ha : (combLine Re.ref n).a = ∑ a, n a • (Re.ref a).a := by
    funext k
    simp [combLine_a, Finset.sum_apply]
  rw [hd _ (smooth_comb Re.ref_smooth n), ha, map_sum, Int.cast_sum]
  refine Finset.sum_nonneg fun a _ => ?_
  rw [map_zsmul, smul_eq_mul, Int.cast_mul, ← hd _ (Re.ref_smooth a), hdeg]
  obtain ⟨h1, h2⟩ := mass_sys S hg a
  by_cases hF : a ∈ Fl
  · rw [le_antisymm (h2 fun t => (hFl a hF t).1) h1, mul_zero]
  · exact mul_nonneg (by exact_mod_cast hn a hF) h1
