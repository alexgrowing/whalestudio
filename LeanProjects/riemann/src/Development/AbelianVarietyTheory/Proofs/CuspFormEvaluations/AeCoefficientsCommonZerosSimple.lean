import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LocalUnfoldBStatementHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalExponentialDecay
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.KappaStatementHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LUStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OrthoStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfE
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfH

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology GlobalTheory.Shares
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.ParamSard

noncomputable def colProj {n N : ℕ} (j0 : Fin N) :
    (Fin (n + 1) × Fin N → ℂ) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun p => WithLp.toLp 2 fun k => p (k.succ, j0)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

noncomputable def colInc {n N : ℕ} (j0 : Fin N) :
    EuclideanSpace ℂ (Fin n) →L[ℂ] (Fin (n + 1) × Fin N → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v q => if q.2 = j0 then (Fin.cons 0 (fun k => v k) : Fin (n + 1) → ℂ) q.1 else 0
      map_add' := fun v w => by
        funext ⟨i, j⟩
        by_cases h : j = j0
        · refine Fin.cases ?_ (fun k => ?_) i <;> simp [h]
        · simp [h]
      map_smul' := fun c v => by
        funext ⟨i, j⟩
        by_cases h : j = j0
        · refine Fin.cases ?_ (fun k => ?_) i <;> simp [h]
        · simp [h] }

theorem colInc_apply {n N : ℕ} (j0 : Fin N) (v : EuclideanSpace ℂ (Fin n)) (k : Fin n) (j : Fin N) :
    colInc j0 v (k.succ, j) = if j = j0 then v k else 0 := by
  simp [colInc]

theorem colProj_colInc {n N : ℕ} (j0 : Fin N) (v : EuclideanSpace ℂ (Fin n)) :
    colProj j0 (colInc j0 v) = v := by
  ext k
  show colInc j0 v (k.succ, j0) = _
  simp [colInc_apply]

theorem ae_simple_col {n N : ℕ} (U : Set (EuclideanSpace ℂ (Fin n))) (hU : IsOpen U)
    (w : Fin N → EuclideanSpace ℂ (Fin n) → ℂ) (hw : ∀ j, DifferentiableOn ℂ (w j) U) (j0 : Fin N) :
    ∀ᵐ t : Fin (n + 1) × Fin N → ℂ, ∀ z ∈ U, w j0 z ≠ 0 → ∑ j, t (0, j) * w j z ≠ 0 →
      (∀ k : Fin n, ∑ j, t (k.succ, j) * w j z = 0) →
      (fderiv ℂ (fun y => (WithLp.toLp 2 fun k : Fin n =>
        (∑ j, t (k.succ, j) * w j y) / ∑ j, t (0, j) * w j y : EuclideanSpace ℂ (Fin n))) z).det ≠ 0 := by
  set S : (Fin (n + 1) × Fin N → ℂ) → EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n) :=
    fun p y => WithLp.toLp 2 fun k => (∑ j, p (k.succ, j) * w j y) / w j0 y with hS
  set G : (Fin (n + 1) × Fin N → ℂ) → (Fin (n + 1) × Fin N → ℂ) :=
    fun p => p - colInc j0 (S p (colProj j0 p)) with hG
  have hnull : volume (G '' {p | DifferentiableAt ℝ G p ∧ (fderiv ℝ G p).det = 0}) = 0 :=
    addHaar_image_eq_zero_of_det_fderivWithin_eq_zero volume (f' := fun p => fderiv ℝ G p)
      (fun p hp => hp.1.hasFDerivAt.hasFDerivWithinAt) (fun p hp => hp.2)
  rw [← compl_mem_ae_iff] at hnull
  filter_upwards [hnull] with t ht z hz hw0 hs0 hsk hdet
  apply ht
  set F : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n) := fun y => WithLp.toLp 2 fun k : Fin n =>
        (∑ j, t (k.succ, j) * w j y) / ∑ j, t (0, j) * w j y with hF
  have hwz : ∀ j, DifferentiableAt ℂ (w j) z := fun j => (hw j).differentiableAt (hU.mem_nhds hz)
  set A : EuclideanSpace ℂ (Fin n) → (Fin (n + 1) × Fin N → ℂ) :=
    fun y => t + colInc j0 (y - colProj j0 t) with hA
  have hπA : ∀ y, colProj j0 (A y) = y := fun y => by simp [hA, colProj_colInc]
  have hGA : ∀ y, w j0 y ≠ 0 → G (A y) = t - colInc j0 (S t y) := by
    intro y hy
    have : S (A y) y = S t y + (y - colProj j0 t) := by
      ext k
      simp only [hS, hA, Pi.add_apply, colInc_apply, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul,
        Finset.sum_ite_eq', Finset.mem_univ, if_true, PiLp.add_apply]
      field_simp
    simp only [hG, hπA, this]
    simp only [hA, map_add]
    abel
  have hSz : S t z = 0 := by
    ext k
    simp [hS, hsk]
  have hFz : F z = 0 := by
    ext k
    simp [hF, hsk]
  have hsum : ∀ i, DifferentiableAt ℂ (fun y => ∑ j, t (i, j) * w j y) z := fun i =>
    DifferentiableAt.fun_sum fun j _ => (hwz j).const_mul _
  have hFd : DifferentiableAt ℂ F z := by
    refine (differentiableAt_piLp 2).2 fun k => ?_
    have := (hsum k.succ).mul ((hsum 0).inv hs0)
    simp only [hF, div_eq_mul_inv]
    exact this
  have hGd : DifferentiableAt ℂ G (A z) := by
    refine differentiableAt_id.sub ((colInc j0).differentiableAt.comp _ ?_)
    have hwp : ∀ j, DifferentiableAt ℂ (fun p => w j (colProj j0 p)) (A z) := fun j =>
      DifferentiableAt.comp _ (by rw [hπA]; exact hwz j) (colProj j0).differentiableAt
    refine (differentiableAt_piLp 2).2 fun k => ?_
    have h1 : DifferentiableAt ℂ (fun p : Fin (n + 1) × Fin N → ℂ =>
        ∑ j, p (k.succ, j) * w j (colProj j0 p)) (A z) :=
      DifferentiableAt.fun_sum fun j _ => (differentiableAt_apply _ _).mul (hwp j)
    have := h1.mul ((hwp j0).inv (by rw [hπA]; exact hw0))
    simp only [hS, div_eq_mul_inv]
    exact this
  refine ⟨A z, ⟨hGd.restrictScalars ℝ, ?_⟩, by rw [hGA z hw0, hSz, map_zero, sub_zero]⟩
  obtain ⟨v, hv, hv0⟩ : ∃ v, fderiv ℂ F z v = 0 ∧ v ≠ 0 := by
    have := LinearMap.det_eq_zero_iff_ker_ne_bot.1 hdet
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 this
    exact ⟨v, hv, hv0⟩
  set c : EuclideanSpace ℂ (Fin n) → ℂ := fun y => (∑ j, t (0, j) * w j y) * (w j0 y)⁻¹ with hc
  have hcd : DifferentiableAt ℂ c z := (hsum 0).mul ((hwz j0).inv hw0)
  have hev : G ∘ A =ᶠ[𝓝 z] fun y => t - colInc j0 (c y • F y) := by
    filter_upwards [(hwz j0).continuousAt.eventually_ne hw0, (hsum 0).continuousAt.eventually_ne hs0]
      with y h1 h2
    have : S t y = c y • F y := by
      ext k
      simp only [hS, hc, hF, PiLp.smul_apply, smul_eq_mul]
      field_simp
    rw [← this]
    exact hGA y h1
  have hAd : HasFDerivAt A (colInc j0) z := by
    have := (((colInc j0).hasFDerivAt (x := z - colProj j0 t)).comp z
      ((hasFDerivAt_id z).sub_const (colProj j0 t))).const_add t
    rw [ContinuousLinearMap.comp_id] at this
    exact this
  have e1 := hGd.hasFDerivAt.comp z hAd
  have e2 := (((colInc j0).hasFDerivAt).comp z (hcd.hasFDerivAt.smul hFd.hasFDerivAt)).const_sub t
  have e3 := e1.unique (e2.congr_of_eventuallyEq hev)
  have e4 : fderiv ℂ G (A z) (colInc j0 v) = 0 := by
    have := congrArg (fun L => L v) e3
    simpa [hv, hFz] using this
  have e5 : fderiv ℝ G (A z) (colInc j0 v) = 0 := by
    rw [(hGd.hasFDerivAt.restrictScalars ℝ).fderiv]
    exact e4
  refine LinearMap.det_eq_zero_iff_ker_ne_bot.2 ((Submodule.ne_bot_iff _).2 ⟨colInc j0 v, e5, fun h => hv0 ?_⟩)
  rw [← colProj_colInc j0 v, h, map_zero]

theorem ae_simple {n N : ℕ} (U : Set (EuclideanSpace ℂ (Fin n))) (hU : IsOpen U)
    (w : Fin N → EuclideanSpace ℂ (Fin n) → ℂ) (hw : ∀ j, DifferentiableOn ℂ (w j) U) :
    ∀ᵐ t : Fin (n + 1) × Fin N → ℂ, ∀ z ∈ U, ∑ j, t (0, j) * w j z ≠ 0 →
      (∀ k : Fin n, ∑ j, t (k.succ, j) * w j z = 0) →
      (fderiv ℂ (fun y => (WithLp.toLp 2 fun k : Fin n =>
        (∑ j, t (k.succ, j) * w j y) / ∑ j, t (0, j) * w j y : EuclideanSpace ℂ (Fin n))) z).det ≠ 0 := by
  filter_upwards [ae_all_iff.2 (ae_simple_col U hU w hw)] with t ht z hz h0 hk
  obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero h0
  exact ht j z hz (right_ne_zero_of_mul hj) h0 hk

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem exists_cell {r : ℕ} (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0) :
    ∃ O : Set (Frame X.Ψ r), IsOpen O ∧ (∀ b ∈ Bor X.Ψ r, rmul x0 b ∈ O) ∧
      ∀ y ∈ O, ∃ z ∈ OmF X x0, ∃ b ∈ Bor X.Ψ r, y = rmul (cpt X x0 z) b ∧
      ∀ (L : Wt X.Ψ r) (w0 : Frame X.Ψ r → ℂ) (s : Fin (nd X) → Frame X.Ψ r → ℂ), IsBEq X L w0 →
        (∀ k, IsBEq X L (s k)) → w0 (cpt X x0 z) ≠ 0 →
        (fderiv ℂ (fun u : V (nd X) => (WithLp.toLp 2 fun k =>
          s k (cpt X x0 u) / w0 (cpt X x0 u) : V (nd X))) z).det ≠ 0 →
        (fderiv ℂ (fun u : V (nd X) => (WithLp.toLp 2 fun k =>
          s k (cpt X y u) / w0 (cpt X y u) : V (nd X))) 0).det ≠ 0 := by
  have hod : x0 ∈ X.dom := IW.orth_mem_dom X _ ho
  obtain ⟨Δ, zOf, bOf, hΔ, -, hz, -, hsplit, huniq⟩ := lu_holds r X x0 ho
  have hO : IsOpen {x | x ∈ X.dom ∧ Δ x ≠ 0} :=
    (FourierCoefficientDomain.isOpen_dom X).inter (isOpen_ne_fun hΔ.continuous continuous_const)
  refine ⟨{x | x ∈ X.dom ∧ Δ x ≠ 0}, hO, fun b hb => ?_, fun y hy => ?_⟩
  · have h0 := huniq 0 (IW.zero_mem_OmF X _ ho) b hb
    rw [IW.cpt_zero] at h0
    exact ⟨OntoS.dom_rmul X hod hb, h0.1⟩
  obtain ⟨h1, h2, h3⟩ := hsplit y hy.1 hy.2
  refine ⟨zOf y, h1, bOf y, h2, h3, fun L w0 s hw0 hs hwx hdet => ?_⟩
  have hcd := OntoB.cd_cpt X y
  set U : Set (V (nd X)) := cpt X y ⁻¹' {x | x ∈ X.dom ∧ Δ x ≠ 0} with hUd
  have hU : IsOpen U := hO.preimage hcd.continuous
  have h0U : (0 : V (nd X)) ∈ U := by
    show cpt X y 0 ∈ {x | x ∈ X.dom ∧ Δ x ≠ 0}
    rwa [IW.cpt_zero]
  set Φ : V (nd X) → V (nd X) := fun u => zOf (cpt X y u) with hΦdef
  have hΦ : DifferentiableOn ℂ Φ U :=
    hz.comp (hcd.differentiable (by simp)).differentiableOn fun _ h => h
  have hΦ0 : Φ 0 = zOf y := by
    show zOf (cpt X y 0) = _
    rw [IW.cpt_zero]
  have hJ : (fderiv ℂ Φ 0).det = bchar (kapW X) (bOf (cpt X y 0)) :=
    KapPf.kappa_statement_holds r X y x0 1 U Φ (fun u => bOf (cpt X y u)) hU hΦ
      (fun u hu => ⟨hu.1, (hsplit _ hu.1 hu.2).2.1, by
        rw [FundSetPf.lact_one]; exact (hsplit _ hu.1 hu.2).2.2⟩) 0 h0U
  have hJ0 : (fderiv ℂ Φ 0).det ≠ 0 := hJ ▸ OntoE.bchar_ne X _ (hsplit _ h0U.1 h0U.2).2.1
  have hΦd : DifferentiableAt ℂ Φ 0 := hΦ.differentiableAt (hU.mem_nhds h0U)
  have hnx : OmF X x0 ∈ 𝓝 (zOf y) := (OntoB.isOpen_OmF X x0).mem_nhds h1
  set F : V (nd X) → V (nd X) := fun u : V (nd X) =>
    (WithLp.toLp 2 fun k => s k (cpt X x0 u) / w0 (cpt X x0 u) : V (nd X)) with hF
  have hFd : DifferentiableAt ℂ F (zOf y) := by
    have hw : DifferentiableAt ℂ (fun u => w0 (cpt X x0 u)) (zOf y) :=
      (OntoB.hol_comp X x0 hw0.1).differentiableAt hnx
    have hsk : ∀ k, DifferentiableAt ℂ (fun u => s k (cpt X x0 u)) (zOf y) := fun k =>
      (OntoB.hol_comp X x0 (hs k).1).differentiableAt hnx
    rw [hF]
    refine (differentiableAt_piLp 2).2 fun k => ?_
    have := (hsk k).mul (hw.inv hwx)
    simp only [div_eq_mul_inv]
    exact this
  have hev : (fun u : V (nd X) => (WithLp.toLp 2 fun k =>
      s k (cpt X y u) / w0 (cpt X y u) : V (nd X))) =ᶠ[𝓝 0] F ∘ Φ := by
    filter_upwards [hU.mem_nhds h0U] with u hu
    obtain ⟨g1, g2, g3⟩ := hsplit _ hu.1 hu.2
    have g1' : cpt X x0 (zOf (cpt X y u)) ∈ X.dom := g1
    show _ = F (Φ u)
    rw [hF]
    show (WithLp.toLp 2 _ : V (nd X)) = WithLp.toLp 2 _
    congr 1
    funext k
    have a1 := (hs k).2 _ g1' _ g2
    have a2 := hw0.2 _ g1' _ g2
    rw [← g3] at a1 a2
    rw [a1, a2, mul_div_mul_left _ _ (OntoE.bchar_ne X L g2)]
  rw [hev.fderiv_eq, fderiv_comp 0 (by rwa [hΦ0]) hΦd, hΦ0]
  have : ((fderiv ℂ F (zOf y)).comp (fderiv ℂ Φ 0)).det =
      (fderiv ℂ F (zOf y)).det * (fderiv ℂ Φ 0).det := by
    unfold ContinuousLinearMap.det
    rw [← LinearMap.det_comp]
    rfl
  rw [this]
  exact mul_ne_zero hdet hJ0

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Xa : ArchInM X) , ∀ᵐ t : Fin (nd X + 1) × Fin Xa.N → ℂ, let sf : Fin (nd X + 1) → Frame X.Ψ r → ℂ := fun i x => ∑ j, t (i, j) * Xa.w j x; ∀ x ∈ X.dom, sf 0 x ≠ 0 → (∀ k : Fin (nd X), sf k.succ x = 0) → (fderiv ℂ (fun z : V (nd X) => (WithLp.toLp 2 fun k => sf k.succ (cpt X x z) / sf 0 (cpt X x z) : V (nd X))) 0).det ≠ 0 := by
  intro E _ _ _ r X Xa
  have hsec : ∀ j, X.IsSec Xa.L (Xa.w j) := fun j => (Xa.w_van j).1.1.1
  choose O hO hOb hOc using fun x0 : {x0 // IsOrth X x0} => exists_cell X x0.2
  obtain ⟨T, hT, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable O hO
  have hae := (ae_ball_iff hT).2 fun (x0 : {x0 // IsOrth X x0}) (_ : x0 ∈ T) =>
    ae_simple (OmF X x0.1) (OntoB.isOpen_OmF X x0.1) (fun j u => Xa.w j (cpt X x0.1 u))
      fun j => OntoB.hol_comp X x0.1 (hsec j).1
  filter_upwards [hae] with t ht sf x hx h0 hk
  have hsf : ∀ i, IsBEq X Xa.L (sf i) := fun i =>
    ⟨DifferentiableOn.fun_sum fun j _ => (hsec j).1.const_mul _, fun y hy b hb => by
      simp only [sf, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [(hsec j).2.1 y hy b hb]; ring⟩
  have hxU : x ∈ ⋃ i ∈ T, O i := by
    rw [hTU]
    obtain ⟨x1, h1, b, hb, rfl⟩ := ortho_holds r X x hx
    exact Set.mem_iUnion.2 ⟨⟨x1, h1⟩, hOb _ b hb⟩
  obtain ⟨x0, hx0, hxO⟩ := Set.mem_iUnion₂.1 hxU
  obtain ⟨z, hz, b, hb, hxe, hmain⟩ := hOc x0 x hxO
  have hz' : cpt X x0.1 z ∈ X.dom := hz
  have hval : ∀ i, sf i x = bchar Xa.L b * sf i (cpt X x0.1 z) := fun i => by
    rw [← (hsf i).2 _ hz' b hb, ← hxe]
  have h0' : sf 0 (cpt X x0.1 z) ≠ 0 := right_ne_zero_of_mul (hval 0 ▸ h0)
  have hk' : ∀ k : Fin (nd X), sf k.succ (cpt X x0.1 z) = 0 := fun k =>
    (mul_eq_zero.1 (hval k.succ ▸ hk k)).resolve_left (OntoE.bchar_ne X _ hb)
  exact hmain Xa.L (sf 0) (fun k => sf k.succ) (hsf 0) (fun k => hsf k.succ) h0'
    (ht x0 hx0 z hz h0' hk')

end GlobalTheory.ParamSard
