import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLast
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BiThetaOfVac
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CentralEigenRealDatumFiniteSumFockProducts
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleLiftFockSumEqSumIteratedLifts
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousIntegralCompactAutomorphicQuotientParaStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilOperatorIntegralCommOfBoundedFiniteMeasureStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SetIntegralFundamentalDomainRightTranslateInvariStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WeilRepresentationContinuous
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemMultTOfEquivariant
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CompactAverageSmoothFamilyClosedUnderDerivatives
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.LevelADef
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AvgMid

open scoped ContDiff

theorem contDiff_mean {K R : Type} [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
    [NormedAddCommGroup R] [NormedSpace ℝ R] [FiniteDimensional ℝ R] (μ : Measure K) [IsFiniteMeasure μ]
    (Q : (K → R → ℂ) → Prop) (hc : ∀ F, Q F → Continuous fun p : K × R => F p.1 p.2)
    (hd : ∀ F, Q F → ∀ k, Differentiable ℝ (F k)) (hq : ∀ F, Q F → ∀ u, Q fun k x => fderiv ℝ (F k) x u) :
    ∀ F, Q F → ContDiff ℝ ∞ fun x => ∫ k, F k x ∂μ := by
  have hF' : ∀ F, Q F → Continuous fun p : K × R => fderiv ℝ (F p.1) p.2 := fun F h =>
    continuous_clm_apply.2 fun u => hc _ (hq F h u)
  have hint : ∀ F, Q F → ∀ x, Integrable (fun k => fderiv ℝ (F k) x) μ := fun F h x => by
    have c : Continuous fun k => fderiv ℝ (F k) x := (hF' F h).comp (continuous_id.prodMk continuous_const)
    obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn c.continuousOn
    exact Integrable.of_bound c.aestronglyMeasurable C (ae_of_all _ fun k => hC k (Set.mem_univ _))
  have hder : ∀ F, Q F → ∀ x₀, HasFDerivAt (fun x => ∫ k, F k x ∂μ) (∫ k, fderiv ℝ (F k) x₀ ∂μ) x₀ := by
    intro F h x₀
    obtain ⟨C, hC⟩ := (isCompact_univ.prod (isCompact_closedBall x₀ 1)).exists_bound_of_continuousOn
      (hF' F h).continuousOn
    have c : ∀ x, Continuous fun k => F k x := fun x => (hc F h).comp (continuous_id.prodMk continuous_const)
    exact hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := μ) (F := fun x k => F k x)
      (F' := fun x k => fderiv ℝ (F k) x) (x₀ := x₀) (bound := fun _ => C)
      (Metric.closedBall_mem_nhds x₀ zero_lt_one)
      (Filter.Eventually.of_forall fun x => (c x).aestronglyMeasurable) (GlobalTheory.AvgFam.integrable_of_continuous μ (c x₀))
      (hint F h x₀).aestronglyMeasurable
      (ae_of_all _ fun k x hx => hC (k, x) ⟨Set.mem_univ _, hx⟩) (integrable_const C)
      (ae_of_all _ fun k x _ => (hd F h k x).hasFDerivAt)
  have key : ∀ n : ℕ, ∀ F, Q F → ContDiff ℝ n fun x => ∫ k, F k x ∂μ := by
    intro n
    induction n with
    | zero => exact fun F h => contDiff_zero.2 (GlobalTheory.AvgFam.continuous_avg μ (hc F h))
    | succ n ih =>
      intro F h
      rw [show ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 by push_cast; rfl, contDiff_succ_iff_fderiv_apply]
      refine ⟨fun x => (hder F h x).differentiableAt, by simp, fun u => ?_⟩
      have e : (fun x => fderiv ℝ (fun x => ∫ k, F k x ∂μ) x u) = fun x => ∫ k, fderiv ℝ (F k) x u ∂μ := by
        funext x
        rw [(hder F h x).fderiv, ContinuousLinearMap.integral_apply (hint F h x)]
      rw [e]
      exact ih _ (hq F h u)
  exact fun F h => contDiff_infty.2 fun n => key n F h

theorem contDiff_mean_span {K R : Type} [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
    [NormedAddCommGroup R] [NormedSpace ℝ R] [FiniteDimensional ℝ R] (μ : Measure K) [IsFiniteMeasure μ]
    (G : Set (K → R → ℂ)) (hG : ∀ F ∈ G, (Continuous fun q : K × R => F q.1 q.2) ∧ (∀ k, Differentiable ℝ (F k)) ∧
      ∀ u, (fun k x => fderiv ℝ (F k) x u) ∈ Submodule.span ℂ G) :
    ∀ F ∈ G, ContDiff ℝ ∞ fun x => ∫ k, F k x ∂μ := by
  have key : ∀ F ∈ Submodule.span ℂ G, (Continuous fun q : K × R => F q.1 q.2) ∧ (∀ k, Differentiable ℝ (F k)) ∧
      ∀ u, (fun k x => fderiv ℝ (F k) x u) ∈ Submodule.span ℂ G := by
    intro F hF
    induction hF using Submodule.span_induction with
    | mem F hF => exact hG F hF
    | zero => exact ⟨continuous_const, fun k => differentiable_const _, fun u => by
        have : (fun (k : K) x => fderiv ℝ ((0 : K → R → ℂ) k) x u) = 0 := by funext k x; simp
        rw [this]; exact zero_mem _⟩
    | add F F' _ _ h h' =>
      refine ⟨h.1.add h'.1, fun k => (h.2.1 k).add (h'.2.1 k), fun u => ?_⟩
      have : (fun k x => fderiv ℝ ((F + F') k) x u) = (fun k x => fderiv ℝ (F k) x u) + fun k x => fderiv ℝ (F' k) x u := by
        funext k x
        rw [Pi.add_apply, fderiv_add (h.2.1 k x) (h'.2.1 k x)]; rfl
      rw [this]; exact add_mem (h.2.2 u) (h'.2.2 u)
    | smul c F _ h =>
      refine ⟨h.1.const_smul c, fun k => (h.2.1 k).const_smul c, fun u => ?_⟩
      have : (fun k x => fderiv ℝ ((c • F) k) x u) = c • fun k x => fderiv ℝ (F k) x u := by
        funext k x
        rw [Pi.smul_apply, fderiv_const_smul (h.2.1 k x)]; rfl
      rw [this]; exact Submodule.smul_mem _ c (h.2.2 u)
  exact fun F hF => contDiff_mean μ (fun F => F ∈ Submodule.span ℂ G) (fun F h => (key F h).1) (fun F h => (key F h).2.1)
    (fun F h => (key F h).2.2) _ (Submodule.subset_span hF)

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

section Smooth

open GlobalTheory.FockCompare GlobalTheory.OrientedHeis GlobalTheory.ThetaGrowth

variable {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {om : Om S T} {θ : InfFam D}
  {σ : (D.what₂.Tau → ℂ) →+ AE D}

theorem fderiv_om (hom : IsWeilDatumO ψ S T χS χT om) (hc : Chart θ σ) {n : ℕ} (e : Module.Basis (Fin n) ℝ (RW T S))
    (p : GA D S × GA D T) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (w : WO S T) (x u : RW T S) :
    fderiv ℝ (fun y : RW T S => om p f (w + iotaW σ T S y)) x u =
      (Real.pi * Complex.I) * (omO S T (piW θ T S w + x) u : ℝ) * om p f (w + iotaW σ T S x) +
        ∑ j, ((e.repr (mov θ p.1⁻¹ p.2⁻¹ u) j : ℝ) : ℂ) * om p (dv θ σ S T (e j) f) (w + iotaW σ T S x) := by
  obtain ⟨g, h⟩ := p
  have hψ := hom.std
  have h1 := dv_apply hc u (hom.om_pres (g, h) f hf) (w + iotaW σ T S x)
  have h2 : fderiv ℝ (fun y : RW T S => om (g, h) f (w + iotaW σ T S x + iotaW σ T S y)) 0 =
      fderiv ℝ (fun y : RW T S => om (g, h) f (w + iotaW σ T S y)) x := by
    have := fderiv_comp_add_left (𝕜 := ℝ) (f := fun y : RW T S => om (g, h) f (w + iotaW σ T S y)) (x := 0) x
    rw [add_zero] at this
    rw [← this]
    congr 1
    funext y
    rw [map_add, add_assoc]
  have h3 : dv θ σ S T (mov θ g⁻¹ h⁻¹ u) f = ∑ j, ((e.repr (mov θ g⁻¹ h⁻¹ u) j : ℝ) : ℂ) • dv θ σ S T (e j) f := by
    have := congrArg (fun z => ((dvL hc hψ S T z ⟨f, hf⟩ : thetaSub ψ S T) : WO S T → ℂ)) (e.sum_repr (mov θ g⁻¹ h⁻¹ u))
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, Submodule.coe_sum, Submodule.coe_smul] at this
    exact this.symm
  rw [h2, dv_om hom hc g h u hf, h3, map_sum, map_add (piW θ T S), hc.pi_iota] at h1
  simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h1
  rw [h1]
  ring

theorem continuous_coord (hθ : IsInfFam θ) {n : ℕ} (e : Module.Basis (Fin n) ℝ (RW T S)) {K : Type} [TopologicalSpace K]
    {p : K → GA D S × GA D T} (hp : Continuous p) (u : RW T S) (j : Fin n) :
    Continuous fun k => ((e.repr (mov θ (p k).1⁻¹ (p k).2⁻¹ u) j : ℝ) : ℂ) := by
  have hr : Continuous fun z : RW T S => ((e.repr z j : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (e.coord j).continuous_of_finiteDimensional
  have hm : Continuous fun k => mov θ (p k).1⁻¹ (p k).2⁻¹ u :=
    Continuous.comp (g := fun z : (GA D S × GA D T) × RW T S => mov θ z.1.1⁻¹ z.1.2⁻¹ z.2) (f := fun k => (p k, u))
      (GlobalTheory.ThetaJointCont.continuous_mov₂ hθ) (hp.prodMk continuous_const)
  exact Continuous.comp (g := fun z : RW T S => ((e.repr z j : ℝ) : ℂ)) hr hm

theorem sm_mean (hom : IsWeilDatumO ψ S T χS χT om) (hc : Chart θ σ) {K : Type} [TopologicalSpace K] [CompactSpace K]
    [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ] {p : K → GA D S × GA D T} (hp : Continuous p)
    {a : K → ℂ} (ha : Continuous a) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    Sm (iotaW σ T S) fun w => ∫ k, a k * om (p k) f w ∂μ := by
  intro w
  have hψ := hom.std
  let e := Module.finBasis ℝ (RW T S)
  let G : Set (K → RW T S → ℂ) := {F | ∃ (a : K → ℂ) (c : RW T S → ℂ) (f : WO S T → ℂ), Continuous a ∧ ContDiff ℝ ∞ c ∧
    IsThetaFunO ψ S T f ∧ F = fun k x => a k * (c x * om (p k) f (w + iotaW σ T S x))}
  have key : ∀ F ∈ G, (Continuous fun q : K × RW T S => F q.1 q.2) ∧ (∀ k, Differentiable ℝ (F k)) ∧
      ∀ u, (fun k x => fderiv ℝ (F k) x u) ∈ Submodule.span ℂ G := by
    · rintro _ ⟨a, c, f, ha, hcc, hf, rfl⟩
      have hs : ∀ k, Differentiable ℝ fun x => om (p k) f (w + iotaW σ T S x) := fun k =>
        (theta_sm hc (hom.om_pres (p k) f hf) w).differentiable (by simp)
      have hcd : Differentiable ℝ c := hcc.differentiable (by simp)
      refine ⟨(ha.comp continuous_fst).mul ((hcc.continuous.comp continuous_snd).mul
        ((GlobalTheory.ThetaJointCont.continuous_om_oriented hom hf).comp ((hp.comp continuous_fst).prodMk
          (continuous_const.add ((hc.continuous_iota T S).comp continuous_snd))))),
        fun k => (hcd.mul (hs k)).const_mul _, fun u => ?_⟩
      have e1 : (fun k x => fderiv ℝ (fun x => a k * (c x * om (p k) f (w + iotaW σ T S x))) x u) =
          (fun k x => a k * ((fderiv ℝ c x u + c x * ((Real.pi * Complex.I) * (omO S T (piW θ T S w + x) u : ℝ))) *
            om (p k) f (w + iotaW σ T S x))) +
          ∑ j, fun k x => (a k * ((e.repr (mov θ (p k).1⁻¹ (p k).2⁻¹ u) j : ℝ) : ℂ)) *
            (c x * om (p k) (dv θ σ S T (e j) f) (w + iotaW σ T S x)) := by
        funext k x
        have := (((hcd x).hasFDerivAt.mul (hs k x).hasFDerivAt).const_mul (a k)).fderiv
        erw [this]
        simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply, smul_eq_mul, Pi.add_apply,
          Finset.sum_apply]
        rw [fderiv_om hom hc e (p k) hf w x u]
        simp only [mul_add, Finset.mul_sum]
        rw [add_right_comm]
        congr 1
        · ring
        · exact Finset.sum_congr rfl fun j _ => by ring
      rw [e1]
      refine add_mem (Submodule.subset_span ⟨a, _, f, ha, ?_, hf, rfl⟩) (Submodule.sum_mem _ fun j _ =>
        Submodule.subset_span ⟨_, c, _, ?_, hcc, theta_dv hc hψ (e j) hf, rfl⟩)
      · have h1 : ContDiff ℝ ∞ fun x : RW T S => ((omO S T).flip u (piW θ T S w + x) : ℝ) :=
          (LinearMap.toContinuousLinearMap ((omO S T).flip u)).contDiff.comp (contDiff_const.add contDiff_id)
        exact ((hcc.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).add
          (hcc.mul (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp h1)))
      · exact ha.mul (continuous_coord hc.inf e hp u j)
  have := contDiff_mean_span μ G key _ ⟨a, fun _ => 1, f, ha, contDiff_const, hf, rfl⟩
  simpa only [one_mul] using this

end Smooth

open scoped ComplexOrder in

theorem exists_haar {S : HSp D} {y : DefSp S} (hy : y.Is) : CompactSpace ↥(GinfC S ⊓ Subgroup.center (GA D S)) ∧
    ∃ ν : Measure ↥(GinfC S ⊓ Subgroup.center (GA D S)), IsProbabilityMeasure ν ∧ ν.IsMulLeftInvariant := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D S
  have hpm : ∀ σ : D.host.E →+* ℂ, (S.gram.map σ).PosDef ∨ (-S.gram.map σ).PosDef := by
    intro σ
    have h0 : ∀ τ, (Formalism.BasicNotions.TH.gramAt D S τ).PosDef ∨ (-Formalism.BasicNotions.TH.gramAt D S τ).PosDef := fun τ => by
      have := (hy.cart τ).2.2
      rcases hy.pm τ with h | h <;> rw [h] at this
      · exact Or.inl (by simpa using this)
      · exact Or.inr (by simpa using this)
    obtain ⟨τ, rfl | rfl⟩ := GlobalTheory.DefLiftMult.exists_tauE D σ
    · exact h0 τ
    · have e : S.gram.map ((starRingEnd ℂ).comp (tauE D τ)) = (Formalism.BasicNotions.TH.gramAt D S τ)ᴴᵀ := by
        ext i j
        rfl
      rw [e]
      refine (h0 τ).imp (fun h => h.conjTranspose.transpose) fun h => ?_
      have := h.conjTranspose.transpose
      rwa [conjTranspose_neg, transpose_neg] at this
  have hd : S.IsDefinite := by
    intro σ
    rcases hpm σ with h | h
    · exact Or.inl (GlobalTheory.DefLiftMult.sig_of_posDef h (hy.sig σ))
    · refine Or.inr ?_
      have hs := hy.sig σ
      generalize S.sig σ = pq at hs ⊢
      obtain ⟨p, q⟩ := pq
      obtain ⟨hn, Q, hQ⟩ := Formalism.UG.P.sig_data _ p q hs
      have hp : p = 0 := by
        by_contra hp
        have j : Fin p := ⟨0, Nat.pos_of_ne_zero hp⟩
        have h1 := (h.posSemidef.conjTranspose_mul_mul_same Q).diag_nonneg (i := Sum.inl j)
        rw [Matrix.mul_neg, Matrix.neg_mul, hQ] at h1
        simp [Formalism.UG.Jpq] at h1
        exact absurd h1 (by norm_num)
      subst hp
      simp at hn
      rw [hn]
  have hcl : IsClosed (Subgroup.center (GA D S) : Set (GA D S)) := by
    have : (Subgroup.center (GA D S) : Set (GA D S)) = ⋂ g, {z | g * z = z * g} := by
      ext z; simp [Subgroup.mem_center_iff]
    rw [this]
    exact isClosed_iInter fun g => isClosed_eq (continuous_const.mul continuous_id) (continuous_id.mul continuous_const)
  haveI hc : CompactSpace ↥(GinfC S ⊓ Subgroup.center (GA D S)) :=
    isCompact_iff_compactSpace.1 ((Formalism.IndefR.Eqv.isCompact_GinfC hy.sig hd).inter_right hcl)
  refine ⟨hc, Measure.haarMeasure ⊤, ⟨?_⟩, inferInstance⟩
  exact Measure.haarMeasure_self

theorem family_bounded {S T : HSp D} (hψ : IsStdChar D ψ (-1)) {K : Type} [TopologicalSpace K] [CompactSpace K]
    {F : K → WO S T → ℂ} (hF : ∀ k, IsThetaFunO ψ S T (F k)) (hc : Continuous fun q : K × WO S T => F q.1 q.2) :
    ∃ C : ℝ, ∀ k w, ‖F k w‖ ≤ C := by
  obtain ⟨-, -, -, -, -, B, hB, hcov⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  obtain ⟨C, hC⟩ := (isCompact_univ.prod hB).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨C, fun k w => ?_⟩
  obtain ⟨γ, hγ, h⟩ := hcov w
  rw [← GlobalTheory.OrientedHeis.theta_norm_periodic hψ (hF k) γ hγ w]
  exact hC (k, _) ⟨Set.mem_univ _, h⟩

theorem integral_mean_translate {S : HSp D} (hS : CoCpt S) (v : Vol S) {K : Type} [TopologicalSpace K]
    [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K] (ν : Measure K) [IsProbabilityMeasure ν]
    {b : K → GA D S} (hb : Continuous b) {Ψ : GA D S → ℂ} (hΨ : IsContAut S Ψ) :
    ∫ h in v.𝓕, (∫ k, Ψ (h * b k) ∂ν) ∂v.μ = ∫ h in v.𝓕, Ψ h ∂v.μ := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D S
  have h1 := (GlobalTheory.T.continuous_integral_compactAutomorphicQuotient_param D S hS v Unit (fun _ _ => 1) continuous_const (fun _ _ _ _ => rfl)).1 ()
  haveI : IsFiniteMeasure (v.μ.restrict v.𝓕) := (integrable_const_iff.1 h1).resolve_left one_ne_zero
  obtain ⟨C, hC⟩ := (GlobalTheory.T.continuous_integral_compactAutomorphicQuotient_param D S hS v Unit (fun g _ => Ψ g) (hΨ.2.comp continuous_fst)
    (fun γ hγ g _ => hΨ.1 γ hγ g)).2.2 ()
  have hC' := hC.self_of_nhds
  rw [integral_integral_swap]
  · simp only [GlobalTheory.T.setIntegral_fundamentalDomain_right_translate_invariant D S v.μ v.𝓕 v.haar v.fund Ψ hΨ.1]
    simp
  · exact Integrable.of_bound (hΨ.2.comp (continuous_fst.mul (hb.comp continuous_snd))).aestronglyMeasurable C
      (ae_of_all _ fun q => hC' _)

def vacSub (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (Λ : AddSubgroup (WO S T)) : Submodule ℂ (WO S T → ℂ) where
  carrier := {f | IsThetaFunO ψ S T f ∧ IsLatVac (heisO ψ S T) Λ f}
  zero_mem' := ⟨GlobalTheory.OrientedHeis.theta_zero, fun u _ => by funext w; simp [heisO], fun _ _ u _ _ => by funext w; simp [heisO]⟩
  add_mem' := fun {f g} hf hg => by
    have e : ∀ u, heisO ψ S T u (f + g) = heisO ψ S T u f + heisO ψ S T u g := fun u => by
      funext w; simp only [heisO, Pi.add_apply, mul_add]
    exact ⟨GlobalTheory.OrientedHeis.theta_add hf.1 hg.1, fun u hu => by rw [e, hf.2.1 u hu, hg.2.1 u hu],
      fun i hi u hu hu' => by rw [e, hf.2.2 i hi u hu hu', hg.2.2 i hi u hu hu']⟩
  smul_mem' := fun c f hf => ⟨GlobalTheory.OrientedHeis.theta_smul c hf.1,
    fun u hu => by rw [GlobalTheory.SplitScalar.heisO_smul, hf.2.1 u hu],
    fun i hi u hu hu' => by rw [GlobalTheory.SplitScalar.heisO_smul, hf.2.2 i hi u hu hu']⟩

theorem theta_comb {S T : HSp D} (hψ : IsStdChar D ψ (-1)) {c : WO S T →₀ ℂ} (hc : IsFinComb c) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) : IsThetaFunO ψ S T (comb ψ S T c f) :=
  Finset.sum_induction _ (IsThetaFunO ψ S T) (fun _ _ => GlobalTheory.OrientedHeis.theta_add) GlobalTheory.OrientedHeis.theta_zero
    fun u hu => GlobalTheory.OrientedHeis.theta_smul _ (GlobalTheory.FinTranslate.isThetaFunO_heisO hψ.1.1 hψ.1.2.1 hf (hc u hu))

theorem comb_smul {S T : HSp D} (c : WO S T →₀ ℂ) (a : ℂ) (f : WO S T → ℂ) :
    comb ψ S T c (a • f) = a • comb ψ S T c f := by
  funext w
  simp only [GlobalTheory.FrComb.comb_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

section Mean

variable {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {om : Om S T}

def mean (om : Om S T) (ν : Measure ↥(GinfC S ⊓ Subgroup.center (GA D S))) (χ : GA D S → ℂ) (f : WO S T → ℂ) :
    WO S T → ℂ := fun w => ∫ b, χ b.1 * om (b.1, 1) f w ∂ν

variable [CompactSpace ↥(GinfC S ⊓ Subgroup.center (GA D S))] {ν : Measure ↥(GinfC S ⊓ Subgroup.center (GA D S))}
  [IsProbabilityMeasure ν] {χ : GA D S → ℂ}

omit [CompactSpace ↥(GinfC S ⊓ Subgroup.center (GA D S))] [IsProbabilityMeasure ν] in
theorem heisO_mean (hom : IsWeilDatumO ψ S T χS χT om) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) {u : WO S T}
    (hu : u.map (infPart D) = 0) : heisO ψ S T u (mean om ν χ f) = mean om ν χ (heisO ψ S T u f) := by
  funext w
  rw [heisO]
  simp only [mean]
  rw [← integral_const_mul]
  congr 1
  funext b
  rw [hom.om_heis b.1 1 u f hf, GlobalTheory.FrComb.actO_real b.2.1 (GinfC T).one_mem hu, heisO]
  ring

theorem theta_mean (hom : IsWeilDatumO ψ S T χS χT om) {θ : InfFam D} (hθ : IsInfFam θ)
    (hχ : Continuous fun b : ↥(GinfC S ⊓ Subgroup.center (GA D S)) => χ b.1) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) : IsThetaFunO ψ S T (mean om ν χ f) := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D S
  obtain ⟨σ, hc⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have hp : Continuous fun b : ↥(GinfC S ⊓ Subgroup.center (GA D S)) => ((b.1, 1) : GA D S × GA D T) :=
    continuous_subtype_val.prodMk continuous_const
  refine ⟨fun γ w => ?_, ?_, ?_, ((GlobalTheory.FockCompare.smooth_iff_sm_and_real_lines D θ σ hc T S).1 _).2
    (sm_mean hom hc ν hp hχ hf)⟩
  · simp only [mean]
    rw [← integral_const_mul]
    congr 1
    funext b
    rw [(hom.om_pres _ f hf).quasi]
    ring
  · obtain ⟨U, hU, h⟩ := hf.level
    exact ⟨U, hU, fun u hu h0 => by rw [heisO_mean hom hf h0, h u hu h0]⟩
  · exact GlobalTheory.AvgFam.continuous_avg ν ((hχ.comp continuous_fst).mul
      ((GlobalTheory.ThetaJointCont.continuous_om_oriented hom hf).comp ((hp.comp continuous_fst).prodMk continuous_snd)))

theorem vac_mean (hom : IsWeilDatumO ψ S T χS χT om) {θ : InfFam D} (hθ : IsInfFam θ)
    (hχ : Continuous fun b : ↥(GinfC S ⊓ Subgroup.center (GA D S)) => χ b.1) {LS : Set (Fin S.rank → D.host.E)}
    {LT : Set (Fin T.rank → D.host.E)} {f : WO S T → ℂ} (hf : f ∈ vacSub ψ S T (latO S T LS LT fun _ => True)) :
    mean om ν χ f ∈ vacSub ψ S T (latO S T LS LT fun _ => True) :=
  ⟨theta_mean hom hθ hχ hf.1,
    fun u hu => by rw [heisO_mean hom hf.1 (GlobalTheory.FrComb.nsmul_fin (GlobalTheory.SplitScalar.latO_fin hu) 2), hf.2.1 u hu],
    fun i hi u hu hu' => by rw [heisO_mean hom hf.1 (GlobalTheory.SplitScalar.latO_fin hu), hf.2.2 i hi u hu hu']⟩

theorem comb_mean (hom : IsWeilDatumO ψ S T χS χT om)
    (hχ : Continuous fun b : ↥(GinfC S ⊓ Subgroup.center (GA D S)) => χ b.1) {c : WO S T →₀ ℂ} (hc : IsFinComb c)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) : comb ψ S T c (mean om ν χ f) = mean om ν χ (comb ψ S T c f) := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D S
  funext w
  have e : ∀ b : ↥(GinfC S ⊓ Subgroup.center (GA D S)), χ b.1 * om (b.1, 1) (comb ψ S T c f) w =
      ∑ x ∈ c.support, c x * (ψ (symplOH S T w x) * (χ b.1 * om (b.1, 1) f (w + x))) := fun b => by
    rw [GlobalTheory.FrComb.om_comb hom b.2.1 (GinfC T).one_mem hc hf, GlobalTheory.FrComb.comb_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [GlobalTheory.FrComb.comb_apply]
  simp only [mean, e]
  rw [integral_finset_sum]
  · simp only [integral_const_mul]
  · exact fun x _ => ((GlobalTheory.AvgFam.integrable_of_continuous ν (hχ.mul ((hom.om_cont f hf _).comp
      (continuous_subtype_val.prodMk continuous_const)))).const_mul _).const_mul _

theorem om_mean (hom : IsWeilDatumO ψ S T χS χT om) {θ : InfFam D} (hθ : IsInfFam θ)
    (hχ : Continuous fun b : ↥(GinfC S ⊓ Subgroup.center (GA D S)) => χ b.1) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (g : GA D S) (h : GA D T) (w : WO S T) :
    om (g, h) (mean om ν χ f) w = ∫ b, χ b.1 * om (g * b.1, h) f w ∂ν := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D S
  have hth : ∀ (g : GA D S) (h : GA D T) (b : ↥(GinfC S ⊓ Subgroup.center (GA D S))),
      IsThetaFunO ψ S T (χ b.1 • om (g * b.1, h) f) := fun g h b =>
    GlobalTheory.OrientedHeis.theta_smul _ (hom.om_pres _ f hf)
  have hco : ∀ (g : GA D S) (h : GA D T), Continuous fun q : ↥(GinfC S ⊓ Subgroup.center (GA D S)) × WO S T =>
      (χ q.1.1 • om (g * q.1.1, h) f) q.2 := fun g h =>
    (hχ.comp continuous_fst).mul ((GlobalTheory.ThetaJointCont.continuous_om_oriented hom hf).comp
      (((continuous_const.mul (continuous_subtype_val.comp continuous_fst)).prodMk continuous_const).prodMk continuous_snd))
  have e : ∀ b : ↥(GinfC S ⊓ Subgroup.center (GA D S)),
      om (g, h) (χ b.1 • om (1 * b.1, 1) f) = χ b.1 • om (g * b.1, h) f := fun b => by
    rw [map_smul, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul, mul_one]
  have e0 : mean om ν χ f = fun y => ∫ b, (χ b.1 • om (1 * b.1, 1) f) y ∂ν := by
    funext y; simp only [mean, one_mul, Pi.smul_apply, smul_eq_mul]
  have := GlobalTheory.T.weilOperator_integral_comm_of_bounded_finiteMeasure D ψ S T χS χT om hom _ ν (fun b => χ b.1 • om (1 * b.1, 1) f) (g, h) (hth 1 1) (hco 1 1)
    (family_bounded hom.std (hth 1 1) (hco 1 1)) (by simp only [e]; exact hco g h)
    (by simp only [e]; exact family_bounded hom.std (hth g h) (hco g h)) (e0 ▸ theta_mean hom hθ hχ hf) w
  rw [e0, this]
  simp only [e, Pi.smul_apply, smul_eq_mul]

theorem eigen_mean [ν.IsMulLeftInvariant] (hom : IsWeilDatumO ψ S T χS χT om) {θ : InfFam D} (hθ : IsInfFam θ)
    (hχ : Continuous fun b : ↥(GinfC S ⊓ Subgroup.center (GA D S)) => χ b.1)
    (hm : ∀ b b' : ↥(GinfC S ⊓ Subgroup.center (GA D S)), χ (b.1 * b'.1) = χ b.1 * χ b'.1) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (b' : ↥(GinfC S ⊓ Subgroup.center (GA D S))) :
    om (b'.1, 1) (mean om ν χ f) = χ b'.1⁻¹ • mean om ν χ f := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D S
  funext w
  rw [om_mean hom hθ hχ hf, Pi.smul_apply, smul_eq_mul, mean,
    ← integral_mul_left_eq_self (fun b : ↥(GinfC S ⊓ Subgroup.center (GA D S)) => χ b.1 * om (b.1, 1) f w) b',
    ← integral_const_mul]
  congr 1
  funext b
  have := hm b'⁻¹ (b' * b)
  simp only [Subgroup.coe_inv, Subgroup.coe_mul, inv_mul_cancel_left] at this
  rw [this, Subgroup.coe_mul, mul_assoc]

theorem lift_mean (hom : IsWeilDatumO ψ S T χS χT om) {θ : InfFam D} (hθ : IsInfFam θ) (hS : CoCpt S) (v : Vol S)
    (hχ : Continuous fun b : ↥(GinfC S ⊓ Subgroup.center (GA D S)) => χ b.1) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) {Φ : GA D S → ℂ} (hΦ : IsContAut S Φ)
    (he : ∀ (b : ↥(GinfC S ⊓ Subgroup.center (GA D S))) h, Φ (h * b.1) = χ b.1 * Φ h) (h₂ : GA D T) :
    ∫ h in v.𝓕, Φ h * om (h, h₂) (mean om ν χ f) 0 ∂v.μ = ∫ h in v.𝓕, Φ h * om (h, h₂) f 0 ∂v.μ := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D S
  have hΨ : IsContAut S fun h => Φ h * om (h, h₂) f 0 := by
    refine ⟨fun γ hγ g => ?_, hΦ.2.mul ((hom.om_cont f hf 0).comp (continuous_id.prodMk continuous_const))⟩
    have e : ((γ * g, h₂) : GA D S × GA D T) = (γ, 1) * (g, h₂) := by simp
    simp only []
    rw [e, map_mul, Module.End.mul_apply, hom.om_aut γ hγ 1 (one_mem _) _ (hom.om_pres _ _ hf), hΦ.1 γ hγ g]
  rw [← integral_mean_translate hS v ν continuous_subtype_val hΨ]
  congr 1
  funext h
  rw [om_mean hom hθ hχ hf, ← integral_const_mul]
  congr 1
  funext b
  rw [he]
  ring

end Mean

section Lift

variable {A S A' : HSp D} {χA χS χS' χA' : (AE D)ˣ →* Circle} {oma : Om A S} {omb : Om S A'}

theorem contAut_lift (hw : IsWeilDatumO ψ A S χA χS oma) (hA : CoCpt A) (v : Vol A) {X : WO A S → ℂ}
    (hX : IsThetaFunO ψ A S X) {φ : GA D A → ℂ} (hφ : IsContAut A φ) :
    IsContAut S fun h => ∫ g in v.𝓕, oma (g, h) X 0 * φ g ∂v.μ := by
  refine ⟨fun γ hγ h => ?_, (GlobalTheory.T.continuous_integral_compactAutomorphicQuotient_param D A hA v (GA D S) (fun g h => oma (g, h) X 0 * φ g)
    ((hw.om_cont X hX 0).mul (hφ.2.comp continuous_fst)) fun γ hγ g h => ?_).2.1⟩
  · simp only []
    congr 1
    funext g
    have e : ((g, γ * h) : GA D A × GA D S) = (1, γ) * (g, h) := by simp
    rw [e, map_mul, Module.End.mul_apply, hw.om_aut 1 (one_mem _) γ hγ _ (hw.om_pres _ _ hX)]
  · have e : ((γ * g, h) : GA D A × GA D S) = (γ, 1) * (g, h) := by simp
    rw [e, map_mul, Module.End.mul_apply, hw.om_aut γ hγ 1 (one_mem _) _ (hw.om_pres _ _ hX), hφ.1 γ hγ g]

theorem biComb_sum (c : WO A S →₀ ℂ) (c' : WO S A' →₀ ℂ) {n : ℕ} (X : Fin n → WO A S → ℂ) (Y : Fin n → WO S A' → ℂ) :
    biComb ψ A S A' c c' (fun u v => ∑ i, X i u * Y i v) =
      fun u v => ∑ i, comb ψ A S c (X i) u * comb ψ S A' c' (Y i) v := by
  funext u v
  simp only [biComb]
  have e1 : (fun u' => comb ψ S A' c' (fun v => ∑ i, X i u' * Y i v) v) =
      fun u' => ∑ i, comb ψ S A' c' (Y i) v * X i u' := by
    funext u'
    rw [comb_sum_mul]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [e1, comb_sum_mul]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem biLift_sum (hwa : IsWeilDatumO ψ A S χA χS oma) (hwb : IsWeilDatumO ψ S A' χS' χA' omb) (hA : CoCpt A)
    (hS : CoCpt S) (vA : Vol A) (vS : Vol S) {n : ℕ} {X : Fin n → WO A S → ℂ} {Y : Fin n → WO S A' → ℂ}
    (hX : ∀ i, IsThetaFunO ψ A S (X i)) (hY : ∀ i, IsThetaFunO ψ S A' (Y i)) {φ : GA D A → ℂ} (hφ : IsContAut A φ)
    (h₂ : GA D A') : biLift oma omb vA vS φ (fun u v => ∑ i, X i u * Y i v) h₂ =
      ∑ i, ∫ h in vS.𝓕, (∫ g in vA.𝓕, oma (g, h) (X i) 0 * φ g ∂vA.μ) * omb (h, h₂) (Y i) 0 ∂vS.μ := by
  have hint : ∀ h₀ h₁, omb (h₁, h₂) (fun v => oma (h₀, h₁) (fun u => ∑ i, X i u * Y i v) 0) 0 =
      ∑ i, oma (h₀, h₁) (X i) 0 * omb (h₁, h₂) (Y i) 0 := by
    intro h₀ h₁
    have e1 : ∀ v, (fun u => ∑ i, X i u * Y i v) = ∑ i, Y i v • X i := by
      intro v; funext u; simp [Finset.sum_apply, mul_comm]
    have e2 : (fun v => oma (h₀, h₁) (fun u => ∑ i, X i u * Y i v) 0) = ∑ i, oma (h₀, h₁) (X i) 0 • Y i := by
      funext v; rw [e1 v, map_sum]; simp [Finset.sum_apply, mul_comm]
    rw [e2, map_sum]; simp [Finset.sum_apply]
  have hin : ∀ h₁, ∫ h₀ in vA.𝓕, φ h₀ * ∑ i, oma (h₀, h₁) (X i) 0 * omb (h₁, h₂) (Y i) 0 ∂vA.μ =
      ∑ i, (∫ g in vA.𝓕, oma (g, h₁) (X i) 0 * φ g ∂vA.μ) * omb (h₁, h₂) (Y i) 0 := by
    intro h₁
    have e : (fun h₀ => φ h₀ * ∑ i, oma (h₀, h₁) (X i) 0 * omb (h₁, h₂) (Y i) 0) =
        fun h₀ => ∑ i, oma (h₀, h₁) (X i) 0 * φ h₀ * omb (h₁, h₂) (Y i) 0 := by
      funext h₀; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [e, integral_finset_sum]
    · exact Finset.sum_congr rfl fun i _ => integral_mul_const _ _
    · exact fun i _ => (integrableOn_kernel hA vA hwa (hX i) hφ h₁).mul_const _
  simp only [biLift, hint, hin]
  rw [integral_finset_sum]
  intro i _
  exact Integrable.congr (integrableOn_kernel hS vS hwb (hY i) (contAut_lift hwa hA vA (hX i) hφ) h₂)
    (Filter.Eventually.of_forall fun h₁ => mul_comm _ _)

end Lift

end GlobalTheory.AvgMid

end
