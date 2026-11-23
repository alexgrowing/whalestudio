import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLast
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfAeFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsBiThetaIffJoin
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BiThetaOfVac
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegralConjInnerMulInnerOfIsEmptyEquiv
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AdelicUnitaryTopCong
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CompactAverageSmoothFamilyClosedUnderDerivatives
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SetIntegralFundamentalDomainRightTranslateInvariStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilOperatorIntegralCommOfBoundedFiniteMeasureStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousIntegralCompactAutomorphicQuotientParaStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompactAverageThetaFamilySmoothStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsJointlySmoothBiThetaHeisenbergDerivStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergOneParamDerivOrthDecJoinedEqSumStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilOperatorFirstCommutesHeisenbergDerivativeSecStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergDerivWeilTranslateContinuousCombinatioStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsCompactRealPointsOfDefiniteHermitianSpaceDataStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CenAvg

section Base

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

open GlobalTheory.WeilVacMove in
theorem dLine_smul {S T : HSp D} (M : ℝ →+ WO S T) (a : ℂ) (f : WO S T → ℂ) : dLine ψ S T M (a • f) = a • dLine ψ S T M f := by
  funext x
  simp only [dLine, heisO, Pi.smul_apply, smul_eq_mul]
  rw [← deriv_const_mul_field]
  congr 1
  funext t
  ring

open GlobalTheory.WeilVacMove in
theorem dLine_add (hψ : IsStdChar D ψ (-1)) {S T : HSp D} {M : ℝ →+ WO S T} (hM : Continuous M)
    (hM0 : ∀ s, (M s).map (finPart D) = 0) {f g : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g) :
    dLine ψ S T M (f + g) = dLine ψ S T M f + dLine ψ S T M g := by
  funext x
  have h := ((hasDerivAt_zero_and_isTheta hψ hM hM0 hf).1 x).add ((hasDerivAt_zero_and_isTheta hψ hM hM0 hg).1 x)
  refine Eq.trans ?_ h.deriv
  unfold dLine
  congr 1
  funext t
  simp only [heisO, Pi.add_apply, mul_add]

variable {A S A' : HSp D} {χA χS χS' χA' : (AE D)ˣ →* Circle} {oma : Om A S} {omb : Om S A'}

theorem continuous_act (ha : IsWeilDatumO ψ A S χA χS oma) (hb : IsWeilDatumO ψ S A' χS' χA' omb) (hB : BiAct D)
    {G : WO A S → WO S A' → ℂ} (hG : IsBiTheta ψ A S A' G) :
    Continuous fun x : (GA D A × GA D S) × WO A S × WO S A' => oma x.1 (fun u => G u x.2.2) x.2.1 := by
  have h := (hB ψ A S A' _ _ _ _ oma omb ha hb G hG).2.2.2.comp
    (show Continuous fun x : (GA D A × GA D S) × WO A S × WO S A' => (x.1, ((1 : GA D S × GA D A'), x.2)) from
      continuous_fst.prodMk (continuous_const.prodMk continuous_snd))
  simpa only [Function.comp_def, map_one, Module.End.one_apply] using h

end Base

section Smooth

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {A S A' : HSp D} {χA χS χS' χA' : (AE D)ˣ →* Circle} {oma : Om A S} {omb : Om S A'}

open GlobalTheory.WeilVacMove GlobalTheory.BiTransfer in

theorem isBiSmooth_avg (ha : IsWeilDatumO ψ A S χA χS oma) (hb : IsWeilDatumO ψ S A' χS' χA' omb) (hB : BiAct D)
    {K : Type} [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ]
    {p : K → GA D A × GA D S} (hp : Continuous p) {c : K → ℂ} (hc : Continuous c) {G : WO A S → WO S A' → ℂ}
    (hG : IsBiTheta ψ A S A' G) : IsBiSmooth fun u v => ∫ k, c k * oma (p k) (fun u' => G u' v) u ∂μ := by
  have hψ := ha.std
  let d := sumDec A (GlobalTheory.ChiGrid.negSp A')
  let gen : Set (K → WO (GlobalTheory.Doubling.hsum A (GlobalTheory.ChiGrid.negSp A')) S → ℂ) :=
    {F | ∃ (c : K → ℂ) (G : WO A S → WO S A' → ℂ), Continuous c ∧ IsBiTheta ψ A S A' G ∧
      F = fun k => c k • join d S fun u v => oma (p k) (fun u' => G u' v) u}
  have h1 : ∀ F ∈ Submodule.span ℂ gen, Continuous fun q : K × WO (GlobalTheory.Doubling.hsum A (GlobalTheory.ChiGrid.negSp A')) S => F q.1 q.2 := by
    intro F hF
    induction hF using Submodule.span_induction with
    | mem F h =>
      obtain ⟨c, G, hc, hG, rfl⟩ := h
      exact (hc.comp continuous_fst).mul ((continuous_act ha hb hB hG).comp ((hp.comp continuous_fst).prodMk
        (((continuous_fstH d S).comp continuous_snd).prodMk ((continuous_sndH d S).comp continuous_snd))))
    | zero => exact continuous_const
    | add F F' _ _ h h' => exact h.add h'
    | smul a F _ h => exact h.const_smul a
  have h2 : ∀ F ∈ Submodule.span ℂ gen, ∀ k, IsThetaFunO ψ _ S (F k) := by
    intro F hF
    induction hF using Submodule.span_induction with
    | mem F h =>
      obtain ⟨c, G, hc, hG, rfl⟩ := h
      exact fun k => isTheta_smul _ (isThetaFunO_join d ((hB ψ A S A' _ _ _ _ oma omb ha hb G hG).1 (p k)))
    | zero => exact fun _ => isTheta_zero
    | add F F' _ _ h h' => exact fun k => isTheta_add (h k) (h' k)
    | smul a F _ h => exact fun k => isTheta_smul a (h k)
  have h3 : ∀ F ∈ Submodule.span ℂ gen, ∀ M : ℝ →+ WO _ S, Continuous M → (∀ s, (M s).map (finPart D) = 0) →
      (fun k => dLine ψ _ S M (F k)) ∈ Submodule.span ℂ gen := by
    intro F hF M hM hM0
    induction hF using Submodule.span_induction with
    | mem F h =>
      obtain ⟨c, G, hc, hG, rfl⟩ := h
      have hT := (hB ψ A S A' _ _ _ _ oma omb ha hb G hG).1
      obtain ⟨f1, f2, -⟩ := GlobalTheory.T.heisenbergOneParamDeriv_orthDecJoined_eq_sum D ψ hψ _ A S A' d G hG M hM hM0
      have c1 : Continuous ((fstH d S).comp M) := (continuous_fstH d S).comp hM
      have c2 : Continuous ((sndH d S).comp M) := (continuous_sndH d S).comp hM
      obtain ⟨m, N, e, hN, hN0, he, hexp⟩ := GlobalTheory.T.heisenbergDeriv_weilTranslate_continuous_combination D ψ A S χA χS oma ha _ c1 f1
      have key : (fun k => dLine ψ _ S M (c k • join d S fun u v => oma (p k) (fun u' => G u' v) u)) =
          (∑ i, fun k => (c k * e i (p k)) • join d S fun u v =>
            oma (p k) (fun u' => dLine ψ A S (N i) (fun u'' => G u'' v) u') u) +
          fun k => c k • join d S fun u v => oma (p k) (fun u' => dLine ψ S A' ((sndH d S).comp M) (G u') v) u := by
        funext k
        rw [dLine_smul, (GlobalTheory.T.heisenbergOneParamDeriv_orthDecJoined_eq_sum D ψ hψ _ A S A' d _ (hT (p k)) M hM hM0).2.2]
        funext x
        simp only [Pi.smul_apply, Pi.add_apply, Finset.sum_apply, join_apply, smul_eq_mul]
        rw [GlobalTheory.T.weilOperator_first_commutes_heisenbergDerivative_second D ψ A S A' _ _ _ _ oma omb ha hb hB G hG _ c2 f2, mul_add]
        congr 1
        have := congrFun (hexp (p k) _ (GlobalTheory.FrComb.slice_left hG (sndH d S x))) (fstH d S x)
        simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul] at this
        rw [show (fun u' => oma (p k) (fun u'' => G u'' (sndH d S x)) u') = oma (p k) (fun u'' => G u'' (sndH d S x)) from rfl,
          this, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => (mul_assoc _ _ _).symm
      rw [key]
      refine Submodule.add_mem _ (Submodule.sum_mem _ fun i _ => Submodule.subset_span ?_) (Submodule.subset_span ?_)
      · exact ⟨_, _, hc.mul ((he i).comp hp), (GlobalTheory.T.isJointlySmoothBiTheta_heisenbergDeriv D ψ hψ A S A' G hG).1 _ (hN i) (hN0 i), rfl⟩
      · exact ⟨_, _, hc, (GlobalTheory.T.isJointlySmoothBiTheta_heisenbergDeriv D ψ hψ A S A' G hG).2 _ c2 f2, rfl⟩
    | zero =>
      have : (fun k : K => dLine ψ _ S M ((0 : K → WO (GlobalTheory.Doubling.hsum A (GlobalTheory.ChiGrid.negSp A')) S → ℂ) k)) = 0 := by
        funext k x
        simp [dLine, heisO]
      rw [this]
      exact Submodule.zero_mem _
    | add F F' hF hF' h h' =>
      have : (fun k => dLine ψ _ S M ((F + F') k)) = (fun k => dLine ψ _ S M (F k)) + fun k => dLine ψ _ S M (F' k) :=
        funext fun k => dLine_add hψ hM hM0 (h2 F hF k) (h2 F' hF' k)
      rw [this]
      exact Submodule.add_mem _ h h'
    | smul a F _ h =>
      have : (fun k => dLine ψ _ S M ((a • F) k)) = a • fun k => dLine ψ _ S M (F k) :=
        funext fun k => dLine_smul M a (F k)
      rw [this]
      exact Submodule.smul_mem _ a h
  intro n L L' hL hL' h0 h0' u v
  have := GlobalTheory.T.compactAverage_thetaFamily_smooth D ψ hψ _ S K μ (Submodule.span ℂ gen : Set _) h1 h2 h3 _ (Submodule.subset_span (show _ ∈ gen from ⟨c, G, hc, hG, rfl⟩)) n
    ((inlH d S).comp L + (inrH d S).comp L') (((continuous_inlH d S).comp hL).add ((continuous_inrH d S).comp hL'))
    (fun t => by
      show (inlH d S (L t) + inrH d S (L' t)).map (finPart D) = 0
      rw [Matrix.map_add _ (RingHom.map_add _), map_inlH d S _ (h0 t), fin_inrH d S (h0' t), add_zero]) (inlH d S u + inrH d S v)
  convert this using 4 with t k
  simp only [Pi.smul_apply, join_apply, smul_eq_mul, AddMonoidHom.add_apply, AddMonoidHom.comp_apply, map_add, fst_inl, fst_inr,
    snd_inl, snd_inr, add_zero, zero_add]

end Smooth

section Compact

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {K : Type} [TopologicalSpace K] [CompactSpace K]

theorem exists_bound_fam (hψ : IsStdChar D ψ (-1)) {S T : HSp D} {F : K → WO S T → ℂ} (hF : ∀ k, IsThetaFunO ψ S T (F k))
    (hc : Continuous fun q : K × WO S T => F q.1 q.2) : ∃ C : ℝ, ∀ k x, ‖F k x‖ ≤ C := by
  obtain ⟨-, -, -, -, -, Q, hQ, hQc⟩ := GlobalTheory.MixModel.lattice_Mx D T.rank S.rank
  obtain ⟨C, hC⟩ := (isCompact_univ.prod hQ).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨C, fun k x => ?_⟩
  obtain ⟨γ, ⟨γ', rfl⟩, hx⟩ := hQc x
  have hq := (hF k).quasi γ' x
  have e : (((incA D).toAddMonoidHom.mapMatrix (m := Fin T.rank) (n := Fin S.rank)) γ') = ratW T S γ' := rfl
  rw [e] at hx
  have h1 := hψ.1.2.1 (-(symplOH S T (ratW T S γ') x))
  have := hC (k, _) ⟨Set.mem_univ _, hx⟩
  simp only at this
  rw [hq, norm_mul, h1, one_mul] at this
  exact this

variable [MeasurableSpace K] [BorelSpace K] [SecondCountableTopology K] (μ : Measure K)

theorem om_integral [IsFiniteMeasure μ] {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {om : Om S T}
    (hom : IsWeilDatumO ψ S T χS χT om) {c : K → ℂ} (hc : Continuous c) {F : K → WO S T → ℂ} (p : GA D S × GA D T)
    (hF : ∀ k, IsThetaFunO ψ S T (F k)) (h1 : Continuous fun q : K × WO S T => F q.1 q.2)
    (h2 : Continuous fun q : K × WO S T => om p (F q.1) q.2) (hI : IsThetaFunO ψ S T fun x => ∫ k, c k * F k x ∂μ) (x : WO S T) :
    om p (fun y => ∫ k, c k * F k y ∂μ) x = ∫ k, c k * om p (F k) x ∂μ := by
  have hF' : ∀ k, IsThetaFunO ψ S T (c k • F k) := fun k => GlobalTheory.WeilVacMove.isTheta_smul _ (hF k)
  have h1' : Continuous fun q : K × WO S T => (c q.1 • F q.1) q.2 := (hc.comp continuous_fst).mul h1
  have h2' : Continuous fun q : K × WO S T => om p (c q.1 • F q.1) q.2 := by
    simp only [map_smul]
    exact (hc.comp continuous_fst).mul h2
  have := GlobalTheory.T.weilOperator_integral_comm_of_bounded_finiteMeasure D ψ S T χS χT om hom K μ (fun k => c k • F k) p hF' h1' (exists_bound_fam hom.std hF' h1') h2'
    (exists_bound_fam hom.std (fun k => hom.om_pres p _ (hF' k)) h2') hI x
  simpa only [map_smul, Pi.smul_apply, smul_eq_mul] using this

omit [CompactSpace K] in

theorem integral_mean [IsProbabilityMeasure μ] {A : HSp D} (hA : CoCpt A) (vA : Vol A) {j : K → GA D A} (hj : Continuous j)
    {F : GA D A → ℂ} (hF : IsContAut A F) : ∫ h in vA.𝓕, ∫ k, F (h * j k) ∂μ ∂vA.μ = ∫ h in vA.𝓕, F h ∂vA.μ := by
  obtain ⟨i1, -, i3, -, i5, -⟩ := GlobalTheory.Ker.CongTop.adelicUnitary_top_cong D A
  have hfin := (GlobalTheory.T.continuous_integral_compactAutomorphicQuotient_param D A hA vA Unit (fun _ _ => 1) continuous_const (fun _ _ _ _ => rfl)).1 ()
  haveI : IsFiniteMeasure (vA.μ.restrict vA.𝓕) := by
    rcases (integrable_const_iff (c := (1 : ℂ))).1 hfin with h | h
    · exact absurd h one_ne_zero
    · exact h
  obtain ⟨C, hC⟩ := (GlobalTheory.T.continuous_integral_compactAutomorphicQuotient_param D A hA vA Unit (fun g _ => F g) (hF.2.comp continuous_fst)
    (fun γ hγ g _ => hF.1 γ hγ g)).2.2 ()
  have hC' := hC.self_of_nhds
  rw [integral_integral_swap]
  · simp_rw [GlobalTheory.T.setIntegral_fundamentalDomain_right_translate_invariant D A vA.μ vA.𝓕 vA.haar vA.fund F hF.1]
    simp
  · refine Integrable.mono' (integrable_const C) ?_ (ae_of_all _ fun q => hC' _)
    exact (hF.2.comp (continuous_fst.mul (hj.comp continuous_snd))).aestronglyMeasurable

end Compact

section Avg

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {A S A' : HSp D} {χA χS χS' χA' : (AE D)ˣ →* Circle} {oma : Om A S} {omb : Om S A'}
  {K : Type} [MeasurableSpace K]

def avg (oma : Om A S) (μ : Measure K) (j : K → GA D A) (c : K → ℂ) (G : WO A S → WO S A' → ℂ) : WO A S → WO S A' → ℂ :=
  fun u v => ∫ k, c k * oma (j k, 1) (fun u' => G u' v) u ∂μ

variable (μ : Measure K) {j : K → GA D A} (c : K → ℂ) {G : WO A S → WO S A' → ℂ}

theorem avg_fix_left (ha : IsWeilDatumO ψ A S χA χS oma) (hj : ∀ k, j k ∈ GinfC A) {v : WO S A'}
    (hG : IsThetaFunO ψ A S fun u => G u v) {w : WO A S} (hw : w.map (infPart D) = 0)
    (h : heisO ψ A S w (fun u => G u v) = fun u => G u v) :
    heisO ψ A S w (fun u => avg oma μ j c G u v) = fun u => avg oma μ j c G u v := by
  funext u
  simp only [heisO, avg]
  rw [← integral_const_mul]
  congr 1
  funext k
  have := congrFun (ha.om_heis (j k) 1 w _ hG) u
  rw [h, GlobalTheory.FrComb.actO_real (hj k) (GinfC S).one_mem hw] at this
  rw [this, heisO]
  ring

theorem avg_fix_right {w : WO S A'} (h : ∀ u, heisO ψ S A' w (G u) = G u) (u : WO A S) :
    heisO ψ S A' w (avg oma μ j c G u) = avg oma μ j c G u := by
  funext v
  simp only [heisO, avg]
  rw [← integral_const_mul]
  congr 1
  funext k
  have e : (fun u' => G u' v) = ψ (symplOH S A' v w) • fun u' => G u' (v + w) := funext fun u' => (congrFun (h u') v).symm
  rw [e, map_smul, Pi.smul_apply, smul_eq_mul]
  ring

variable [TopologicalSpace K] [CompactSpace K] [BorelSpace K] [IsFiniteMeasure μ] {c}

omit [MeasurableSpace K] [CompactSpace K] [BorelSpace K] in
theorem continuous_fam (ha : IsWeilDatumO ψ A S χA χS oma) (hb : IsWeilDatumO ψ S A' χS' χA' omb) (hB : BiAct D)
    (hG : IsBiTheta ψ A S A' G) {p : K → GA D A × GA D S} (hp : Continuous p) :
    Continuous fun q : K × WO A S × WO S A' => oma (p q.1) (fun u => G u q.2.2) q.2.1 :=
  (continuous_act ha hb hB hG).comp ((hp.comp continuous_fst).prodMk continuous_snd)

theorem isBiTheta_avg (ha : IsWeilDatumO ψ A S χA χS oma) (hb : IsWeilDatumO ψ S A' χS' χA' omb) (hB : BiAct D)
    (hjc : Continuous j) (hj : ∀ k, j k ∈ GinfC A) (hc : Continuous c) (hG : IsBiTheta ψ A S A' G) :
    IsBiTheta ψ A S A' (avg oma μ j c G) := by
  have hp : Continuous fun k => (j k, (1 : GA D S)) := hjc.prodMk continuous_const
  have hT := (hB ψ A S A' _ _ _ _ oma omb ha hb G hG).1
  refine ⟨?_, isBiSmooth_avg ha hb hB μ hp hc hG, fun γ u v => ?_, fun γ u v => ?_, ?_, ?_⟩
  · exact GlobalTheory.AvgFam.continuous_avg μ (F := fun k (q : WO A S × WO S A') => c k * oma (j k, 1) (fun u' => G u' q.2) q.1)
      ((hc.comp continuous_fst).mul (continuous_fam ha hb hB hG hp))
  · simp only [avg]
    rw [← integral_const_mul]
    congr 1
    funext k
    rw [(hT (j k, 1)).quasiL]
    ring
  · simp only [avg]
    rw [← integral_const_mul]
    congr 1
    funext k
    rw [(hT (j k, 1)).quasiR]
    ring
  · obtain ⟨U, hU, h⟩ := hG.levL
    exact ⟨U, hU, fun a haU ha0 v => avg_fix_left μ c ha hj (GlobalTheory.FrComb.slice_left hG v) ha0 (h a haU ha0 v)⟩
  · obtain ⟨U, hU, h⟩ := hG.levR
    exact ⟨U, hU, fun a haU ha0 u => avg_fix_right μ c (h a haU ha0) u⟩

theorem isBiVac_avg (ha : IsWeilDatumO ψ A S χA χS oma) (hb : IsWeilDatumO ψ S A' χS' χA' omb) (hB : BiAct D)
    (hjc : Continuous j) (hj : ∀ k, j k ∈ GinfC A) (hc : Continuous c) (hG : IsBiTheta ψ A S A' G) {LA LS LA'}
    (hv : IsBiVac ψ A S A' LA LS LA' G) : IsBiVac ψ A S A' LA LS LA' (avg oma μ j c G) := by
  have h := isBiTheta_avg μ ha hb hB hjc hj hc hG
  refine ⟨h.cont, fun v => ⟨GlobalTheory.FrComb.slice_left h v, fun w hw => ?_, fun e he w hw hw' => ?_⟩,
    fun u => ⟨GlobalTheory.FrComb.slice_right h u, fun w hw => ?_, fun e he w hw hw' => ?_⟩⟩
  · exact avg_fix_left μ c ha hj (hv.left v).1 (GlobalTheory.FrComb.nsmul_fin (GlobalTheory.SplitScalar.latO_fin hw) 2) ((hv.left v).2.1 w hw)
  · exact avg_fix_left μ c ha hj (hv.left v).1 (GlobalTheory.SplitScalar.latO_fin hw) ((hv.left v).2.2 e he w hw hw')
  · exact avg_fix_right μ c (fun u' => (hv.right u').2.1 w hw) u
  · exact avg_fix_right μ c (fun u' => (hv.right u').2.2 e he w hw hw') u

theorem biComb_avg (ha : IsWeilDatumO ψ A S χA χS oma) (hb : IsWeilDatumO ψ S A' χS' χA' omb) (hB : BiAct D)
    (hjc : Continuous j) (hj : ∀ k, j k ∈ GinfC A) (hc : Continuous c) (hG : IsBiTheta ψ A S A' G)
    {e : WO A S →₀ ℂ} {e' : WO S A' →₀ ℂ} (he : IsFinComb e) (he' : IsFinComb e') :
    biComb ψ A S A' e e' (avg oma μ j c G) = avg oma μ j c (biComb ψ A S A' e e' G) := by
  have hp : Continuous fun k => (j k, (1 : GA D S)) := hjc.prodMk continuous_const
  have hK1 := GlobalTheory.FrComb.biTheta_combR ha.std hG he'
  have s1 : ∀ k u v, oma (j k, 1) (fun u' => biComb ψ A S A' e e' G u' v) u =
      biComb ψ A S A' e e' (fun u v => oma (j k, 1) (fun u' => G u' v) u) u v := by
    intro k u v
    show oma (j k, 1) (comb ψ A S e fun u'' => comb ψ S A' e' (G u'') v) u = _
    rw [GlobalTheory.FrComb.om_comb ha (hj k) (GinfC S).one_mem he (GlobalTheory.FrComb.slice_left hK1 v), GlobalTheory.FrComb.op_combR]
    rfl
  have hi : ∀ (a : ℂ) u v, Integrable (fun k => a * (c k * oma (j k, 1) (fun u' => G u' v) u)) μ := fun a u v =>
    GlobalTheory.AvgFam.integrable_of_continuous μ (continuous_const.mul (hc.mul ((continuous_fam ha hb hB hG hp).comp
      (continuous_id.prodMk (continuous_const (y := (u, v)))))))
  funext u v
  have e1 : biComb ψ A S A' e e' (avg oma μ j c G) u v = ∑ x ∈ e.support, ∑ y ∈ e'.support,
      ∫ k, (e x * ψ (symplOH A S u x) * (e' y * ψ (symplOH S A' v y))) *
        (c k * oma (j k, 1) (fun u' => G u' (v + y)) (u + x)) ∂μ := by
    simp only [biComb, GlobalTheory.FrComb.comb_apply, Finset.mul_sum, avg, integral_const_mul, mul_assoc]
  rw [e1]
  simp only [avg, s1]
  rw [← Finset.sum_congr rfl fun x _ => integral_finset_sum _ fun y _ => hi _ _ _,
    ← integral_finset_sum _ fun x _ => integrable_finset_sum _ fun y _ => hi _ _ _]
  congr 1
  funext k
  simp only [biComb, GlobalTheory.FrComb.comb_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  ring

variable [SecondCountableTopology K]

theorem om_avg (ha : IsWeilDatumO ψ A S χA χS oma) (hb : IsWeilDatumO ψ S A' χS' χA' omb) (hB : BiAct D)
    (hjc : Continuous j) (hj : ∀ k, j k ∈ GinfC A) (hc : Continuous c) (hG : IsBiTheta ψ A S A' G) (g : GA D A) (h : GA D S)
    (u : WO A S) (v : WO S A') :
    oma (g, h) (fun u' => avg oma μ j c G u' v) u = ∫ k, c k * oma (g * j k, h) (fun u' => G u' v) u ∂μ := by
  haveI := (GlobalTheory.Ker.CongTop.adelicUnitary_top_cong D A).1
  have hm : ∀ k f, oma (g, h) (oma (j k, 1) f) = oma (g * j k, h) f := fun k f => by
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
  have hv : Continuous fun q : K × WO A S => (q.1, q.2, v) := continuous_fst.prodMk (continuous_snd.prodMk continuous_const)
  have := om_integral μ ha hc (F := fun k => oma (j k, 1) fun u' => G u' v) (g, h)
    (fun k => ha.om_pres _ _ (GlobalTheory.FrComb.slice_left hG v))
    ((continuous_fam ha hb hB hG (hjc.prodMk continuous_const)).comp hv)
    (by
      simp only [hm]
      exact (continuous_fam ha hb hB hG (p := fun k => (g * j k, h)) ((continuous_const.mul hjc).prodMk continuous_const)).comp hv)
    (GlobalTheory.FrComb.slice_left (isBiTheta_avg μ ha hb hB hjc hj hc hG) v) u
  simp only [hm] at this
  exact this

theorem ker_avg (ha : IsWeilDatumO ψ A S χA χS oma) (hb : IsWeilDatumO ψ S A' χS' χA' omb) (hB : BiAct D)
    (hjc : Continuous j) (hj : ∀ k, j k ∈ GinfC A) (hc : Continuous c) (hG : IsBiTheta ψ A S A' G) (g : GA D A) (h : GA D S)
    (q : GA D S × GA D A') (u : WO A S) (v : WO S A') :
    omb q (fun v' => oma (g, h) (fun u' => avg oma μ j c G u' v') u) v =
      ∫ k, c k * omb q (fun v' => oma (g * j k, h) (fun u' => G u' v') u) v ∂μ := by
  haveI := (GlobalTheory.Ker.CongTop.adelicUnitary_top_cong D A).1
  have hBG := hB ψ A S A' _ _ _ _ oma omb ha hb G hG
  have hp : Continuous fun k => (g * j k, h) := (continuous_const.mul hjc).prodMk continuous_const
  have hI := GlobalTheory.FrComb.slice_right ((hB ψ A S A' _ _ _ _ oma omb ha hb _ (isBiTheta_avg μ ha hb hB hjc hj hc hG)).1 (g, h)) u
  simp only [om_avg μ ha hb hB hjc hj hc hG] at hI ⊢
  refine om_integral μ hb hc (F := fun k v' => oma (g * j k, h) (fun u' => G u' v') u) q
    (fun k => GlobalTheory.FrComb.slice_right (hBG.1 (g * j k, h)) u) ?_ ?_ hI v
  · exact (continuous_fam ha hb hB hG hp).comp (continuous_fst.prodMk (continuous_const.prodMk continuous_snd))
  · exact hBG.2.2.2.comp (show Continuous fun z : K × WO S A' => ((g * j z.1, h), q, u, z.2) from
      (hp.comp continuous_fst).prodMk (continuous_const.prodMk (continuous_const.prodMk continuous_snd)))

end Avg

end GlobalTheory.CenAvg

end
