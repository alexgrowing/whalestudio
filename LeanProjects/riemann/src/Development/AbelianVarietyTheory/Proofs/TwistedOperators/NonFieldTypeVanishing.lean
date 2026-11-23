import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.NonFieldTypeVanishing
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasOrbIntTensorOfHasOrbInt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCyclicOfFiniteQuotient
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfAdjointFactorIdempotentOrthogonalSplittingRaStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeightedOrbitalIntegralTypeTestVanishStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AnisotropicTorusFundamentalDomainFiniteMeasureStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ClassTermEqVolumeMulOrbitalIntegralStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RegularSemisimpleUnitaryGroupConcreteStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TypeIdempotentConstantTermVanishStatement

open MeasureTheory Set Filter GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms (plusAlg genAlg)
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors (HypH NoFixed radical)
open GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt
open scoped TensorProduct ENNReal

noncomputable section

namespace GlobalTheory.NonFieldType

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {V : HSp D}

theorem localClause {T : TypeDataG V} {U : AuxiliaryPlaceHermitianSpace V} {μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)}
    {ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ} (hμf : ∀ v, (μf v).IsHaarMeasure) (hf : IsTestFin T U μf ff)
    {γ : GRat D.sp.cm.sig V.gram} (hγ : IsNonFieldAniso D.sp.cm.sig V.gram γ.1.1) : LocalClause T μf ff γ := by
  intro k K _ _ e i
  obtain ⟨h1, h2⟩ := GlobalTheory.T.selfAdjointFactorIdempotent_orthogonal_splitting_rank GlobalTheory.T.regularSemisimple_unitaryGroup_concrete D V γ hγ.1 k K e i hγ
  refine ⟨h1, h2, fun v hv dt hdt => ?_⟩
  obtain ⟨hee, -, -, hcomm, hpos, hlt⟩ := h1
  have hγε : γ.1.1 * factorIdem e i = factorIdem e i * γ.1.1 :=
    hcomm _ (Algebra.self_mem_adjoin_singleton _ _)
  have h := GlobalTheory.T.weightedOrbitalIntegral_typeTest_vanish GlobalTheory.T.typeIdempotent_constantTerm_vanish D V T U μf ff hf v (hμf v) γ (factorIdem e i) hγ.1 hee hγε hpos hlt hv 1
    continuous_const (fun _ _ _ => rfl) (fun _ _ _ => rfl) dt
  have e1 : (fun x => (1 : GLoc D.sp.cm.sig V.gram v → ℂ) x *
      ff v (x⁻¹ * proj D.sp.cm.sig V.gram v (ratEmb D.sp.cm.sig V.gram γ) * x)) = conjFn (proj D.sp.cm.sig V.gram v (ratEmb D.sp.cm.sig V.gram γ)) (ff v) := by
    funext x; exact one_mul _
  rw [e1] at h
  exact h

theorem isMulCommutative_cent_ratEmb {γ : GRat D.sp.cm.sig V.gram} (hγ : IsRegSS γ.1.1) :
    IsMulCommutative (cent (ratEmb D.sp.cm.sig V.gram γ)) := by
  refine ⟨⟨fun x y => Subtype.ext (GAd_ext _ _ (fun w => ?_) fun v => ?_)⟩⟩
  · have h := (isMulCommutative_cent_HA (isRegSS_projArch_ratEmb hγ w)).is_comm.comm
      (centMap (projArch D.sp.cm.sig V.gram w) _ x) (centMap (projArch D.sp.cm.sig V.gram w) _ y)
    have h' := congrArg Subtype.val h
    simpa [centMap] using h'
  · have h := (isMulCommutative_cent_HA (isRegSS_proj_ratEmb hγ v)).is_comm.comm
      (centMap (proj D.sp.cm.sig V.gram v) _ x) (centMap (proj D.sp.cm.sig V.gram v) _ y)
    have h' := congrArg Subtype.val h
    simpa [centMap] using h'

theorem ratEmb_mem_GQ (γ : GRat D.sp.cm.sig V.gram) : ratEmb D.sp.cm.sig V.gram γ ∈ GQ V := by
  rw [GlobalTheory.AdelicU.GQ_eq, ← GlobalTheory.AdelicU.range_ratEmb]; exact ⟨γ, rfl⟩

theorem covol_lt_top {γ : GRat D.sp.cm.sig V.gram} (hγ : IsNonFieldAniso D.sp.cm.sig V.gram γ.1.1)
    (dt : Measure (cent (ratEmb D.sp.cm.sig V.gram γ))) [dt.IsHaarMeasure] (𝓣 : Set (cent (ratEmb D.sp.cm.sig V.gram γ)))
    (h𝓣 : IsFundamentalDomain ((GQ V).subgroupOf (cent (ratEmb D.sp.cm.sig V.gram γ))) 𝓣 dt) : dt 𝓣 < ⊤ := by
  obtain ⟨hreg, k, K, iF, iA, he, -, hK⟩ := hγ
  exact GlobalTheory.T.anisotropic_torus_fundamentalDomain_finite_measure GlobalTheory.T.regularSemisimple_unitaryGroup_concrete D V γ hreg k K he hK dt 𝓣 h𝓣

set_option maxHeartbeats 4000000 in
theorem productClause {S : D.what₂.Tau → SPar} {M : DSModel V S} {T : TypeDataG V} {U : AuxiliaryPlaceHermitianSpace V}
    {μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w)} {μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)}
    {μ : Measure (GA D V)} (hμ : IsRestrictedProd D.sp.cm.sig V.gram (frameLat V) μa μf μ)
    {fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ} {ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ}
    (ha : IsTestArchG M μa fa) (hf : IsTestFin T U μf ff)
    {γ : GRat D.sp.cm.sig V.gram} (hγ : IsNonFieldAniso D.sp.cm.sig V.gram γ.1.1) :
    ProductClause μa μf μ fa ff (ratEmb D.sp.cm.sig V.gram γ) := by
  intro dta dtf dt hdt 𝓣 h𝓣
  have hreg := hγ.1
  have hcm := isCMExt_host D
  have hJ := isHermND_gram V
  obtain ⟨hta, htf, htt, -⟩ := id hdt
  have i1 : ∀ w, (dta w).IsMulRightInvariant := fun w =>
    haveI := hta w; isMulRightInvariant_cent (isMulCommutative_cent_HA (isRegSS_projArch_ratEmb hreg w)) _
  have i2 : ∀ v, (dtf v).IsMulRightInvariant := fun v =>
    haveI := htf v; isMulRightInvariant_cent (isMulCommutative_cent_HA (isRegSS_proj_ratEmb hreg v)) _
  have hvol : dt 𝓣 < ⊤ := @covol_lt_top D V γ hγ dt htt 𝓣 h𝓣
  have hfa : ∀ w, Continuous (fa w) ∧ HasCompactSupport (fa w) := fun w =>
    ⟨continuous_of_mem_ccSmooth (continuous_archCoord _ _ w) (ha.mem w), (ha.mem w).1⟩
  have hff : IsFinFamily D.sp.cm.sig V.gram (frameLat V) ff := hf.isFinFamily
  have hKv := (regular_semisimple_adelic hcm hJ (frameLat V) γ hreg).1
  have hpa : ∀ w, IsProperOrbit (cent (projArch D.sp.cm.sig V.gram w (ratEmb D.sp.cm.sig V.gram γ)))
      (projArch D.sp.cm.sig V.gram w (ratEmb D.sp.cm.sig V.gram γ)) := fun w =>
    isProperOrbit_GArch hcm hJ (isRegSS_projArch_ratEmb hreg w)
  have hpf : ∀ v, IsProperOrbit (cent (proj D.sp.cm.sig V.gram v (ratEmb D.sp.cm.sig V.gram γ)))
      (proj D.sp.cm.sig V.gram v (ratEmb D.sp.cm.sig V.gram γ)) := fun v =>
    isProperOrbit_GLoc hcm hJ (isRegSS_proj_ratEmb hreg v)
  obtain ⟨-, hoa, hob, h1, hO⟩ := @hasOrbInt_tensor _ _ _ _ _ _ _ _ _ _ (frameLat V) _ μa μf μ _ dta dtf dt fa ff
    hμ hdt i1 i2 hfa hff hKv (fun w => Or.inl (hpa w)) (fun v => Or.inl (hpf v))
  refine ⟨hvol, _, _, hoa, hob, h1, hO, fun 𝓕 h𝓕 => ?_⟩
  have hc := continuous_of_mem_ccAd (tensor_mem_ccAd ha.mem hf.isFinFamily)
  exact @GlobalTheory.T.classTerm_eq_volume_mul_orbitalIntegral (GA D V) _ _ _ _ _ _ _ _ (GQ V) _ (ratEmb D.sp.cm.sig V.gram γ) (ratEmb_mem_GQ γ)
    (isMulCommutative_cent_ratEmb hreg) μ hμ.2.2.1 dt htt 𝓣 h𝓣 hvol _ _ hc.1 hc.2 hO 𝓕 h𝓕

instance discreteTopology_subgroupOf_cent (γ : GA D V) : DiscreteTopology ((GQ V).subgroupOf (cent γ)) :=
  DiscreteTopology.of_continuous_injective (f := fun t : (GQ V).subgroupOf (cent γ) => (⟨t.1.1, t.2⟩ : GQ V))
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)
    (fun s t h => Subtype.ext (Subtype.ext (by have h' := congrArg Subtype.val h; exact h')))

set_option maxHeartbeats 4000000 in
theorem zeroClause {T : TypeDataG V} (hH : HypH (k := fun v : T.S => ResF v.1) T.τ)
    {μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w)} {μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)}
    {μ : Measure (GA D V)} {fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ} {ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ}
    {γ : GRat D.sp.cm.sig V.gram} (hγ : IsNonFieldAniso D.sp.cm.sig V.gram γ.1.1)
    (hL : LocalClause T μf ff γ) (hP : ProductClause μa μf μ fa ff (ratEmb D.sp.cm.sig V.gram γ)) :
    ZeroClause μ (tensor D.sp.cm.sig V.gram fa ff) (ratEmb D.sp.cm.sig V.gram γ) := by
  intro 𝓕 h𝓕
  haveI hla : ∀ w, LocallyCompactSpace (cent (projArch D.sp.cm.sig V.gram w (ratEmb D.sp.cm.sig V.gram γ))) :=
    fun _ => (isClosed_cent _).locallyCompactSpace
  haveI hlf : ∀ v, LocallyCompactSpace (cent (proj D.sp.cm.sig V.gram v (ratEmb D.sp.cm.sig V.gram γ))) :=
    fun _ => (isClosed_cent _).locallyCompactSpace
  have hR := restrGroup_cent (frameLat V) (ratEmb D.sp.cm.sig V.gram γ)
  let K0 : ∀ v, TopologicalSpace.PositiveCompacts (cent (proj D.sp.cm.sig V.gram v (ratEmb D.sp.cm.sig V.gram γ))) :=
    fun v => ⟨⟨_, hR.isCompact_K v⟩, by
      simp only [(hR.isOpen_K v).interior_eq]; exact ⟨1, one_mem _⟩⟩
  let dta : ∀ w, Measure (cent (projArch D.sp.cm.sig V.gram w (ratEmb D.sp.cm.sig V.gram γ))) := fun _ => Measure.haar
  let dtf : ∀ v, Measure (cent (proj D.sp.cm.sig V.gram v (ratEmb D.sp.cm.sig V.gram γ))) :=
    fun v => Measure.haarMeasure (K0 v)
  haveI : ∀ w, (dta w).IsHaarMeasure := fun _ => inferInstance
  haveI : ∀ v, (dtf v).IsHaarMeasure := fun _ => inferInstance
  have h1 : ∀ᶠ v in cofinite, dtf v ((stabLoc D.sp.cm.sig V.gram (frameLat V) v).subgroupOf
      (cent (proj D.sp.cm.sig V.gram v (ratEmb D.sp.cm.sig V.gram γ)))) = 1 :=
    .of_forall fun v => Measure.haarMeasure_self (K₀ := K0 v)
  obtain ⟨dt, hdt, -⟩ := existsUnique_isCentProd (L := frameLat V) (ratEmb D.sp.cm.sig V.gram γ) dta dtf h1
  have h𝓣 := isFundamentalDomain_stdDom ((GQ V).subgroupOf (cent (ratEmb D.sp.cm.sig V.gram γ))) dt
  obtain ⟨-, oa, ob, -, hob, hone, -, hcls⟩ := hP dta dtf dt hdt _ h𝓣
  obtain ⟨-, k, K, iF, iA, ⟨e⟩, hk, -⟩ := hγ
  obtain ⟨hsplit, -, hloc⟩ := hL k K e ⟨0, by omega⟩
  obtain ⟨v, hv⟩ := hH _ hsplit.2.2.2.2.1 hsplit.2.2.2.2.2
  have h0 := hloc v hv (dtf v.1) inferInstance
  have hob0 : ob v.1 = 0 := (hob v.1).2.symm.trans h0.2
  have hfp : ∏ᶠ v, ob v = 0 := finprod_eq_zero ob v.1 hob0 (Filter.eventually_cofinite.1 hone)
  have h := hcls 𝓕 h𝓕
  rwa [hfp, mul_zero, mul_zero] at h

set_option maxHeartbeats 4000000 in

theorem nonFieldTypeVanishing : NonFieldTypeVanishing := by
  intro D V _ S M T U hH μa μf μ hμ fa ff ha hf γ hγ
  have hL := localClause (fun v => hμ.2.1 v) hf hγ
  have hP := productClause hμ ha hf hγ
  exact ⟨hL, hP, zeroClause hH hγ hL hP⟩

end GlobalTheory.NonFieldType
