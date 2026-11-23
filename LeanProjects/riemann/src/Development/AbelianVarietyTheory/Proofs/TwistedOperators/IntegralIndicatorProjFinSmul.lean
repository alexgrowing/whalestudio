import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ExponentSeparation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfinitePartActDiscreteSeriesHomFactorwiseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdmissibleRepHasTraceFiniteAdelicPureTensorFunct
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HaarEqRestrictedProductMeasureUnitaryFiniteAdeliStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralFiniteIndicatorSmulArchFunctionStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralContinuousMultilinearMapPiMeasureStatement
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.S

noncomputable section
namespace GlobalTheory.TrOpTensor

theorem exists_sum_indicator {X W : Type} [TopologicalSpace X] [T2Space X] [AddCommGroup W] [Module ℂ W]
    (F : X → W) (hF : IsLocallyConstant F) (hc : HasCompactSupport F) :
    ∃ s : Finset W, (∀ r ∈ s, IsOpen (F ⁻¹' {r}) ∧ IsCompact (closure (F ⁻¹' {r}))) ∧
      ∀ x, F x = ∑ r ∈ s, (F ⁻¹' {r}).indicator (fun _ => (1 : ℂ)) x • r := by
  classical
  have hfin : (Set.range F).Finite := by
    haveI : CompactSpace ↥(tsupport F) := isCompact_iff_compactSpace.1 hc
    have h1 : (Set.range (fun x : tsupport F => F x)).Finite :=
      (hF.comp_continuous continuous_subtype_val).range_finite
    refine (h1.union (Set.finite_singleton 0)).subset ?_
    rintro _ ⟨x, rfl⟩
    by_cases hx : x ∈ tsupport F
    · exact Or.inl ⟨⟨x, hx⟩, rfl⟩
    · exact Or.inr (image_eq_zero_of_notMem_tsupport hx)
  refine ⟨hfin.toFinset.filter (· ≠ 0), fun r hr => ?_, fun x => ?_⟩
  · have hr0 : r ≠ 0 := (Finset.mem_filter.1 hr).2
    refine ⟨hF.isOpen_fiber r, hc.of_isClosed_subset isClosed_closure
      (closure_minimal (fun x hx => subset_tsupport F ?_) (isClosed_tsupport F))⟩
    rw [Function.mem_support, show F x = r from hx]
    exact hr0
  · by_cases h0 : F x = 0
    · rw [h0]
      symm
      refine Finset.sum_eq_zero fun r hr => ?_
      have hx : x ∉ F ⁻¹' {r} := fun hx => (Finset.mem_filter.1 hr).2 ((show F x = r from hx).symm.trans h0)
      rw [Set.indicator_of_notMem hx, zero_smul]
    · rw [Finset.sum_eq_single (F x)]
      · rw [Set.indicator_of_mem (show x ∈ F ⁻¹' {F x} from rfl), one_smul]
      · intro r _ hne
        rw [Set.indicator_of_notMem (s := F ⁻¹' {r}) (fun hx => hne (show F x = r from hx).symm), zero_smul]
      · intro hn
        exact absurd (Finset.mem_filter.2 ⟨hfin.mem_toFinset.2 ⟨x, rfl⟩, h0⟩) hn

theorem integralOp_eq_sum {G W : Type} [Group G] [MeasurableSpace G] [AddCommGroup W] [Module ℂ W]
    (ν : Measure G) (σ : Representation ℂ G W) (b : G → ℂ) (A : W →ₗ[ℂ] W)
    (hA : GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp ν σ b A) (w : W) (s : Finset W)
    (hs : ∀ r ∈ s, MeasurableSet ((fun h => b h • σ h w) ⁻¹' {r}) ∧ ν ((fun h => b h • σ h w) ⁻¹' {r}) ≠ ⊤)
    (hsum : ∀ h, b h • σ h w = ∑ r ∈ s, ((fun h => b h • σ h w) ⁻¹' {r}).indicator (fun _ => (1 : ℂ)) h • r) :
    A w = ∑ r ∈ s, ((ν ((fun h => b h • σ h w) ⁻¹' {r})).toReal : ℂ) • r := by
  set F := fun h => b h • σ h w with hF
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro l
  have hpt : ∀ h, b h * l (σ h w) = ∑ r ∈ s, (F ⁻¹' {r}).indicator (fun _ => l r) h := by
    intro h
    rw [← smul_eq_mul, ← map_smul]
    change l (b h • σ h w) = _
    rw [hsum h, map_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [map_smul, smul_eq_mul]
    by_cases hh : h ∈ F ⁻¹' {r}
    · rw [Set.indicator_of_mem hh, Set.indicator_of_mem hh, one_mul]
    · rw [Set.indicator_of_notMem hh, Set.indicator_of_notMem hh, zero_mul]
  rw [map_sub, (hA w l).2, map_sum, integral_congr_ae (.of_forall hpt),
    integral_finsetSum _ fun r hr => (integrableOn_const (hs r hr).2).integrable_indicator (hs r hr).1,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun r hr => ?_
  rw [integral_indicator_const _ (hs r hr).1, map_smul, Measure.real, Complex.real_smul, smul_eq_mul, sub_self]

theorem measure_eq_of_isFinMeas {D : D7} (V : HSp D) {μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)}
    {νF : Measure (GFin D.sp.cm.sig V.gram)} (hF : IsRestrictedProdFin D.sp.cm.sig V.gram (frameLat V) μf νF)
    {ν : Measure (GfC V)} (hν : IsFinMeas V μf ν) (s : Set (GfC V)) (hs : IsCompact (closure s)) :
    ν s = νF ((finPtsEquiv D.sp.cm.sig V.gram) ⁻¹' s) := GlobalTheory.T.haar_eq_restrictedProductMeasure_unitaryFiniteAdelic D V μf νF hF ν hν s hs

theorem integral_indicator_projFin_smul {D : D7} (V : HSp D) {μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w)}
    {μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)} {μ : Measure (GA D V)}
    (hμ : IsRestrictedProd D.sp.cm.sig V.gram (frameLat V) μa μf μ)
    {νF : Measure (GFin D.sp.cm.sig V.gram)} (hF : IsRestrictedProdFin D.sp.cm.sig V.gram (frameLat V) μf νF)
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (B : Set (GFin D.sp.cm.sig V.gram)) (hB : MeasurableSet B) (hB' : νF B ≠ ⊤)
    (a : (∀ w, GArch D.sp.cm.sig V.gram w) → E) (ha : Integrable a (Measure.pi μa)) :
    Integrable (fun g : GA D V => B.indicator (fun _ => (1 : ℂ)) (projFin D.sp.cm.sig V.gram g) •
        a fun w => projArch D.sp.cm.sig V.gram w g) μ ∧
    ∫ g, B.indicator (fun _ => (1 : ℂ)) (projFin D.sp.cm.sig V.gram g) •
        a (fun w => projArch D.sp.cm.sig V.gram w g) ∂μ = (νF B).toReal • ∫ x, a x ∂Measure.pi μa :=
  GlobalTheory.T.integral_finiteIndicator_smul_archFunction D V μa μf μ hμ νF hF E B hB hB' a ha

open scoped Classical in

theorem integral_pi_dsRep {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S)
    (μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w)) [∀ w, SigmaFinite (μa w)]
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (Φ : ContinuousMultilinearMap ℂ M.H H) (fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ) (y : ∀ τ, M.H τ)
    (hfa : ∀ τ, Integrable (fun z => fa (placeOf D τ) z • dsRep M τ z (y τ)) (μa (placeOf D τ))) :
    Integrable (fun x : ∀ w, GArch D.sp.cm.sig V.gram w =>
        (∏ w, fa w (x w)) • Φ (fun τ => dsRep M τ (x (placeOf D τ)) (y τ))) (Measure.pi μa) ∧
    ∫ x, (∏ w, fa w (x w)) • Φ (fun τ => dsRep M τ (x (placeOf D τ)) (y τ)) ∂Measure.pi μa =
      Φ fun τ => ∫ z, fa (placeOf D τ) z • dsRep M τ z (y τ) ∂μa (placeOf D τ) := by
  haveI : ∀ τ, CompleteSpace (M.H τ) := fun τ => (isIrrUnitary_dsRep M τ).complete
  have hgen := GlobalTheory.T.integral_continuousMultilinearMap_pi_measure D.what₂.Tau (fun τ => GArch D.sp.cm.sig V.gram (placeOf D τ))
    (fun τ => μa (placeOf D τ)) M.H H Φ (fun τ z => fa (placeOf D τ) z • dsRep M τ z (y τ)) hfa
  obtain ⟨e, he⟩ : ∃ e : D.what₂.Tau ≃ InfinitePlace D.host.F, e = Equiv.ofBijective _ (placeOf_bijective D) := ⟨_, rfl⟩
  subst he
  have hP := measurePreserving_piCongrLeft μa (Equiv.ofBijective _ (placeOf_bijective D))
  set P := MeasurableEquiv.piCongrLeft (fun w => GArch D.sp.cm.sig V.gram w)
    (Equiv.ofBijective _ (placeOf_bijective D)) with hPdef
  have hcomp : ∀ x' : ∀ τ, GArch D.sp.cm.sig V.gram (placeOf D τ),
      (∏ w, fa w (P x' w)) • Φ (fun τ => dsRep M τ (P x' (placeOf D τ)) (y τ)) =
        Φ fun τ => fa (placeOf D τ) (x' τ) • dsRep M τ (x' τ) (y τ) := by
    intro x'
    have hx : ∀ τ, P x' (placeOf D τ) = x' τ := fun τ =>
      Equiv.piCongrLeft_apply_apply (fun w => GArch D.sp.cm.sig V.gram w)
        (Equiv.ofBijective _ (placeOf_bijective D)) x' τ
    rw [ContinuousMultilinearMap.map_smul_univ,
      ← Equiv.prod_comp (Equiv.ofBijective _ (placeOf_bijective D)) (fun w => fa w (P x' w))]
    refine congrArg₂ (· • ·) (Finset.prod_congr rfl fun τ _ => ?_) (congrArg Φ (funext fun τ => ?_))
    · exact congrArg (fa (placeOf D τ)) (hx τ)
    · exact congrArg (fun z => dsRep M τ z (y τ)) (hx τ)
  have hfun : ((fun x : ∀ w, GArch D.sp.cm.sig V.gram w =>
      (∏ w, fa w (x w)) • Φ (fun τ => dsRep M τ (x (placeOf D τ)) (y τ))) ∘ P) =
      fun x' => Φ fun τ => fa (placeOf D τ) (x' τ) • dsRep M τ (x' τ) (y τ) := funext hcomp
  refine ⟨?_, ?_⟩
  · rw [← hP.integrable_comp_emb P.measurableEmbedding, hfun]
    exact hgen.1
  · rw [← hP.integral_comp' (fun x : ∀ w, GArch D.sp.cm.sig V.gram w =>
      (∏ w, fa w (x w)) • Φ (fun τ => dsRep M τ (x (placeOf D τ)) (y τ))), ← hgen.2]
    exact integral_congr_ae (.of_forall hcomp)

open scoped Classical in

theorem apply_homFinDS {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} {W : Type} [AddCommGroup W]
    [Module ℂ W] {σ : Representation ℂ (GfC V) W} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {π : GA D V →* (H →L[ℂ] H)} {T : W →ₗ[ℂ] ContinuousMultilinearMap ℂ M.H H}
    (hT : T ∈ homFinDS σ M π ⊤) (g : GA D V) (w : W) (y : ∀ τ, M.H τ) :
    π g (T w y) = T (σ (toFin V g) w) fun τ => dsRep M τ (projArch D.sp.cm.sig V.gram (placeOf D τ) g) (y τ) := by
  have h := mem_homTensorPi.1 hT
  have e := GlobalTheory.T.infinitePart_act_discreteSeriesHom_factorwise D V S M H π ⊤ (T (σ (toFin V g) w)) (hT.1 _) g y
  calc π g (T w y) = π (toInf V g : GA D V) (π (toFin V g : GA D V) (T w y)) := by
        conv_lhs => rw [← toInf_mul_toFin g]
        rw [map_mul]; rfl
    _ = π (toInf V g : GA D V) (T (σ (toFin V g) w) y) := by rw [h.2.1]; rfl
    _ = _ := e

end GlobalTheory.TrOpTensor

namespace GlobalTheory.TrOpTensor

theorem locallyConstant_smul {D : D7} (V : HSp D) {ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ}
    (hff : IsFinFamily D.sp.cm.sig V.gram (frameLat V) ff) {W : Type} [AddCommGroup W] [Module ℂ W]
    {σ : Representation ℂ (GfC V) W} (hσ : GlobalTheory.PRep.IsSmooth σ) (w : W) :
    IsLocallyConstant (fun h => finFn V ff h • σ h w) ∧ HasCompactSupport (fun h => finFn V ff h • σ h w) := by
  obtain ⟨hlc, hcs⟩ := GlobalTheory.FinTrace.finFn_mem_SB V hff
  have h2 : IsLocallyConstant fun h : GfC V => σ h w := by
    refine (IsLocallyConstant.iff_exists_open _).2 fun x => ⟨(fun h => x⁻¹ * h) ⁻¹' {g | σ g w = w},
      (hσ w).preimage (continuous_const.mul continuous_id), by simp, fun x' hx' => ?_⟩
    have e : x' = x * (x⁻¹ * x') := by group
    rw [e, map_mul, Module.End.mul_apply, show σ (x⁻¹ * x') w = w from hx']
  exact ⟨hlc.comp₂ h2 (fun a b => a • b), hcs.smul_right⟩

theorem finFn_toFin {D : D7} (V : HSp D) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ) (g : GA D V) :
    finFn V ff (toFin V g) = ∏ᶠ v, ff v (proj D.sp.cm.sig V.gram v g) := by
  unfold finFn
  refine finprod_congr fun v => congrArg (ff v) ?_
  change proj D.sp.cm.sig V.gram v (ofFin D.sp.cm.sig V.gram (projFin D.sp.cm.sig V.gram g)) = _
  rw [proj_ofFin, projFinLoc_projFin]

theorem opTensor : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w)) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) (μ : Measure (GA D V)), IsRestrictedProd D.sp.cm.sig V.gram (frameLat V) μa μf μ → ∀ ν, IsFinMeas V μf ν → ∀ fa ff, (∀ w, fa w ∈ CcArch D.sp.cm.sig V.gram w) → IsFinFamily D.sp.cm.sig V.gram (frameLat V) ff → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W), GlobalTheory.PRep.IsSmooth σ → ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : GA D V →* (H →L[ℂ] H)), IsUnitaryRep π → ∀ T ∈ homFinDS σ M π ⊤, ∀ A, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp ν σ (finFn V ff) A → ∀ w y, repOp π μ (tensor D.sp.cm.sig V.gram fa ff) (T w y) = T (A w) fun τ => repOp (dsRep M τ) (μa (placeOf D τ)) (fa (placeOf D τ)) (y τ) := by
  intro D V S M μa μf μ hμ ν hν fa ff hfa hff W _ _ σ hσ H _ _ _ π hπ T hT A hA w y
  have := hμ.haar
  have := hμ.haar_arch
  have := hμ.haar_loc
  have hfc : ∀ w', Continuous (fa w') := fun w' =>
    continuous_of_mem_ccSmooth (continuous_archCoord _ _ w') (hfa w')
  have hfs : ∀ w', HasCompactSupport (fa w') := fun w' => (hfa w').1
  have hD := fun τ => (isUnitaryRep_dsRep M τ).isRepOp (μ := μa (placeOf D τ)) (hfc (placeOf D τ)) (hfs (placeOf D τ))
  obtain ⟨hcf, hcs⟩ := continuous_of_mem_ccAd (tensor_mem_ccAd hfa hff)
  have hR := hπ.isRepOp (μ := μ) hcf hcs
  obtain ⟨hlc, hcF⟩ := locallyConstant_smul V hff hσ w
  obtain ⟨s, hs, hsum⟩ := exists_sum_indicator _ hlc hcF
  obtain ⟨νF, hνF⟩ := (existsUnique_isRestrictedProdFin D.sp.cm.sig V.gram (frameLat V) μf
    hμ.eventually_eq_one).exists
  have := hν.1
  set F : GfC V → W := fun h => finFn V ff h • σ h w with hF
  have hfin : ∀ r ∈ s, ν (F ⁻¹' {r}) ≠ ⊤ := fun r hr =>
    ((measure_mono subset_closure).trans_lt (hs r hr).2.measure_lt_top).ne
  have hAw := integralOp_eq_sum ν σ (finFn V ff) A hA w s
    (fun r hr => ⟨(hs r hr).1.measurableSet, hfin r hr⟩) hsum
  set a : W → (∀ w', GArch D.sp.cm.sig V.gram w') → H := fun r x =>
    (∏ w', fa w' (x w')) • T r (fun τ => dsRep M τ (x (placeOf D τ)) (y τ)) with ha
  have hsf : ∀ w', SigmaFinite (μa w') := fun w' => inferInstance
  have hpi := fun r => integral_pi_dsRep M μa (T r) fa y fun τ => (hD τ (y τ)).1
  set B : W → Set (GFin D.sp.cm.sig V.gram) := fun r => (finPtsEquiv D.sp.cm.sig V.gram) ⁻¹' (F ⁻¹' {r}) with hB
  have hBm : ∀ r ∈ s, MeasurableSet (B r) := fun r hr =>
    ((hs r hr).1.preimage (finPtsEquiv D.sp.cm.sig V.gram).continuous).measurableSet
  have hνB : ∀ r ∈ s, νF (B r) = ν (F ⁻¹' {r}) := fun r hr =>
    (measure_eq_of_isFinMeas V hνF hν _ (hs r hr).2).symm
  have hBf : ∀ r ∈ s, νF (B r) ≠ ⊤ := fun r hr => by rw [hνB r hr]; exact hfin r hr
  have hL := fun r (hr : r ∈ s) => integral_indicator_projFin_smul V hμ hνF (B r) (hBm r hr) (hBf r hr) (a r) (hpi r).1
  have hpt : ∀ g : GA D V, tensor D.sp.cm.sig V.gram fa ff g • π g (T w y) =
      ∑ r ∈ s, (B r).indicator (fun _ => (1 : ℂ)) (projFin D.sp.cm.sig V.gram g) •
        a r (fun w' => projArch D.sp.cm.sig V.gram w' g) := by
    intro g
    rw [apply_homFinDS hT, tensor, ← finFn_toFin, mul_smul, ← ContinuousMultilinearMap.smul_apply,
      ← LinearMap.map_smul, hsum, map_sum, ContinuousMultilinearMap.sum_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [map_smul, ContinuousMultilinearMap.smul_apply, smul_comm]
    rfl
  rw [(hR (T w y)).2, integral_congr_ae (.of_forall hpt), integral_finset_sum _ fun r hr => (hL r hr).1,
    hAw, map_sum, ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl fun r hr => ?_
  rw [(hL r hr).2, (hpi r).2, map_smul, ContinuousMultilinearMap.smul_apply, hνB r hr, Complex.coe_smul]
  congr 2
  funext τ
  exact ((hD τ (y τ)).2).symm

end GlobalTheory.TrOpTensor
