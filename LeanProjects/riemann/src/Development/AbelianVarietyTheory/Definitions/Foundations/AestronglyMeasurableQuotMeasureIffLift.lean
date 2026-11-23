import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.EquivariantFiniteGroup
import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHilbertSchmidtOfFiniteDimensional
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SchurOrthogonalitySquareIntegrable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DiscreteTopologyRationalPointsHermitianSpace

open MeasureTheory Filter Set GlobalTheory.OpTrace
open scoped InnerProductSpace ENNReal Topology Pointwise symmDiff ComplexConjugate

noncomputable section

namespace GlobalTheory.AutomorphicL2Unitary

section Subrep

variable {G H : Type*} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def IsSubrep (π : G →* (H →L[ℂ] H)) (W : Submodule ℂ H) : Prop :=
  IsClosed (W : Set H) ∧ ∀ g, ∀ v ∈ W, π g v ∈ W

def IsTopIrreducible (π : G →* (H →L[ℂ] H)) : Prop :=
  Nontrivial H ∧ ∀ W, IsSubrep π W → W = ⊥ ∨ W = ⊤

def IsIrredSubrep (π : G →* (H →L[ℂ] H)) (W : Submodule ℂ H) : Prop :=
  IsSubrep π W ∧ W ≠ ⊥ ∧ ∀ U ≤ W, IsSubrep π U → U = ⊥ ∨ U = W

def disc (π : G →* (H →L[ℂ] H)) : Submodule ℂ H := (sSup {W | IsIrredSubrep π W}).topologicalClosure

variable {π : G →* (H →L[ℂ] H)} {W U : Submodule ℂ H}

def IsSubrep.rep (hW : IsSubrep π W) : G →* (W →L[ℂ] W) where
  toFun g := ((π g).comp W.subtypeL).codRestrict W fun v => hW.2 g v v.2
  map_one' := by ext v; simp
  map_mul' g h := by ext v; exact DFunLike.congr_fun (map_mul π g h) (v : H)

@[simp] theorem IsSubrep.coe_rep_apply (hW : IsSubrep π W) (g : G) (v : W) : (hW.rep g v : H) = π g v := rfl

theorem IsSubrep.completeSpace [CompleteSpace H] (hW : IsSubrep π W) : CompleteSpace W :=
  hW.1.completeSpace_coe

theorem isSubrep_top : IsSubrep π ⊤ := ⟨isClosed_univ, fun _ _ _ => trivial⟩

theorem IsSubrep.inf (hW : IsSubrep π W) (hU : IsSubrep π U) : IsSubrep π (W ⊓ U) :=
  ⟨hW.1.inter hU.1, fun g v hv => ⟨hW.2 g v hv.1, hU.2 g v hv.2⟩⟩

theorem isSubrep_topologicalClosure (h : ∀ g, ∀ v ∈ W, π g v ∈ W) : IsSubrep π W.topologicalClosure :=
  ⟨W.isClosed_topologicalClosure, fun g _ hv => map_mem_closure (π g).continuous hv (h g)⟩

theorem isSubrep_closure_sSup {S : Set (Submodule ℂ H)} (h : ∀ W ∈ S, IsSubrep π W) :
    IsSubrep π (sSup S).topologicalClosure :=
  isSubrep_topologicalClosure fun g _ hv =>
    (sSup_le fun W hW v hv => (le_sSup hW : W ≤ sSup S) ((h W hW).2 g v hv) :
      sSup S ≤ (sSup S).comap (π g : H →ₗ[ℂ] H)) hv

theorem isSubrep_disc : IsSubrep π (disc π) := isSubrep_closure_sSup fun _ h => h.1

theorem IsIrredSubrep.le_disc (hW : IsIrredSubrep π W) : W ≤ disc π :=
  (le_sSup (s := {W | IsIrredSubrep π W}) hW).trans (Submodule.le_topologicalClosure _)

theorem disc_le (hU : IsClosed (U : Set H)) (h : ∀ W, IsIrredSubrep π W → W ≤ U) : disc π ≤ U :=
  Submodule.topologicalClosure_minimal _ (sSup_le h) hU

theorem IsSubrep.isSubrep_rep_iff (hW : IsSubrep π W) {T : Submodule ℂ W} :
    IsSubrep hW.rep T ↔ IsSubrep π (T.map W.subtype) := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨hW.1.isClosedEmbedding_subtypeVal.isClosedMap _ h1, ?_⟩
    rintro g _ ⟨v, hv, rfl⟩
    exact ⟨_, h2 g v hv, rfl⟩
  · rintro ⟨h1, h2⟩
    refine ⟨?_, fun g v hv => ?_⟩
    · rw [← Submodule.comap_map_eq_of_injective W.injective_subtype T]
      exact h1.preimage continuous_subtype_val
    · obtain ⟨w, hw, e⟩ := h2 g v ⟨v, hv, rfl⟩
      rwa [← show w = hW.rep g v from Subtype.ext e]

theorem IsSubrep.isIrredSubrep_iff (hW : IsSubrep π W) : IsIrredSubrep π W ↔ IsTopIrreducible hW.rep := by
  have hinj := Submodule.map_injective_of_injective W.injective_subtype
  constructor
  · rintro ⟨-, h1, h2⟩
    refine ⟨Submodule.nontrivial_iff_ne_bot.2 h1, fun T hT => ?_⟩
    exact (h2 _ (W.map_subtype_le T) (hW.isSubrep_rep_iff.1 hT)).imp
      (fun e => hinj (by simpa using e)) fun e => hinj (by simpa using e)
  · rintro ⟨h1, h2⟩
    refine ⟨hW, Submodule.nontrivial_iff_ne_bot.1 h1, fun U hU hU' => ?_⟩
    have e : (U.comap W.subtype).map W.subtype = U := by
      rw [Submodule.map_comap_subtype, inf_eq_right.2 hU]
    exact (h2 _ (hW.isSubrep_rep_iff.2 (e.symm ▸ hU'))).imp
      (fun h => by rw [← e, h, Submodule.map_bot]) fun h => by rw [← e, h, Submodule.map_subtype_top]

theorem isTopIrreducible_iff_top : IsTopIrreducible π ↔ IsIrredSubrep π ⊤ :=
  ⟨fun h => ⟨isSubrep_top, by have := h.1; exact top_ne_bot, fun U _ hU => h.2 U hU⟩,
    fun h => ⟨(Submodule.nontrivial_iff ℂ).1 ⟨_, _, h.2.1⟩, fun U hU => h.2.2 U le_top hU⟩⟩

theorem IsTopIrreducible.disc_eq_top (h : IsTopIrreducible π) : disc π = ⊤ :=
  top_le_iff.1 (isTopIrreducible_iff_top.1 h).le_disc

theorem isIrredSubrep_span_singleton {v : H} (hv : v ≠ 0) (h : ∀ g, ∃ c : ℂ, π g v = c • v) :
    IsIrredSubrep π (ℂ ∙ v) := by
  refine ⟨⟨Submodule.closed_of_finiteDimensional _, fun g w hw => ?_⟩, by simpa using hv, fun U hU _ => ?_⟩
  · obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hw
    obtain ⟨c, hc⟩ := h g
    rw [map_smul, hc]
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v))
  · exact ((nonzero_span_atom v hv).le_iff).1 hU

variable [CompleteSpace H] [TopologicalSpace G]

omit [CompleteSpace H] in

theorem IsSubrep.isUnitaryRep (hW : IsSubrep π W) (hπ : IsUnitaryRep π) : IsUnitaryRep hW.rep :=
  ⟨fun g v => hπ.norm_apply g v, fun v => (hπ.continuous_apply v).subtype_mk _⟩

theorem IsSubrep.orthogonal (hW : IsSubrep π W) (hπ : IsUnitaryRep π) : IsSubrep π Wᗮ :=
  ⟨W.isClosed_orthogonal, fun g v hv => (W.mem_orthogonal' _).2 fun u hu => by
    rw [hπ.inner_apply_left]; exact (W.mem_orthogonal' _).1 hv _ (hW.2 _ u hu)⟩

theorem IsSubrep.starProjection_apply (hW : IsSubrep π W) (hπ : IsUnitaryRep π) [W.HasOrthogonalProjection]
    (g : G) (v : H) : W.starProjection (π g v) = π g (W.starProjection v) :=
  Submodule.eq_starProjection_of_mem_orthogonal (hW.2 g _ (W.starProjection_apply_mem v)) (by
    rw [← map_sub]; exact (hW.orthogonal hπ).2 g _ (W.sub_starProjection_mem_orthogonal v))

variable [MeasurableSpace G] {μ : Measure G} {f : G → ℂ}

omit [TopologicalSpace G] in

theorem IsSubrep.map_mem_of_isRepOp (hW : IsSubrep π W) {T : H →L[ℂ] H} (hT : IsRepOp π μ f T) {v : H}
    (hv : v ∈ W) : T v ∈ W := by
  have := hW.completeSpace
  rw [(hT v).2, show (fun g => f g • π g v) = fun g => W.subtypeₗᵢ (f g • hW.rep g ⟨v, hv⟩) from rfl,
    W.subtypeₗᵢ.integral_comp_comm]
  exact Subtype.property _

omit [TopologicalSpace G] in

theorem IsSubrep.coe_repOp_rep (hW : IsSubrep π W) {T : H →L[ℂ] H} (hT : IsRepOp π μ f T) :
    IsRepOp hW.rep μ f (repOp hW.rep μ f) ∧ ∀ v : W, (repOp hW.rep μ f v : H) = T v := by
  have := hW.completeSpace
  have h : IsRepOp hW.rep μ f ((T.comp W.subtypeL).codRestrict W fun v => hW.map_mem_of_isRepOp hT v.2) := by
    intro v
    have hi : Integrable (fun g => f g • hW.rep g v) μ :=
      (W.subtypeₗᵢ.lipschitz.integrable_comp_iff_of_antilipschitz W.subtypeₗᵢ.antilipschitz (map_zero _)).1 (hT v).1
    exact ⟨hi, Subtype.ext ((hT v).2.trans (W.subtypeₗᵢ.integral_comp_comm fun g => f g • hW.rep g v))⟩
  rw [h.repOp_eq]
  exact ⟨h, fun _ => rfl⟩

omit [CompleteSpace H] in

theorem isRepOp_of_integrable [SecondCountableTopology G] [OpensMeasurableSpace G] (hπ : IsUnitaryRep π)
    (hf : Integrable f μ) : IsRepOp π μ f (repOp π μ f) :=
  hπ.isRepOp_of_integrable hf fun v => hf.1.smul (hπ.continuous_apply v).aestronglyMeasurable

end Subrep

section Quotient

variable {G : Type*} [Group G] (Γ : Subgroup G)

abbrev Quot : Type _ := Quotient (QuotientGroup.rightRel Γ)

abbrev mk (g : G) : Quot Γ := Quotient.mk _ g

def rmul (g : G) : Quot Γ → Quot Γ :=
  Quotient.map' (· * g) fun x y h => by simpa [QuotientGroup.rightRel_apply, mul_assoc] using h

def LeftInv {X : Type*} (φ : G → X) : Prop := ∀ γ ∈ Γ, ∀ g, φ (γ * g) = φ g

def descend {X : Type*} (φ : G → X) : Quot Γ → X := fun q => φ q.out

def lift {X : Type*} (F : Quot Γ → X) : G → X := fun g => F (mk Γ g)

def orbitSum (f : G → ℂ) (x : G) : ℂ := ∑' γ : Γ, f (γ * x)

def kernel (f : G → ℂ) (x y : G) : ℂ := ∑' γ : Γ, f (x⁻¹ * γ * y)

def kernelQ (f : G → ℂ) (p q : Quot Γ) : ℂ := kernel Γ f p.out q.out

def starFn (f : G → ℂ) : G → ℂ := fun g => conj (f g⁻¹)

variable {Γ}

theorem mk_eq_iff {x y : G} : mk Γ x = mk Γ y ↔ ∃ γ : Γ, γ * x = y :=
  Quotient.eq.trans <| QuotientGroup.rightRel_apply.trans
    ⟨fun h => ⟨⟨_, h⟩, by simp⟩, by rintro ⟨γ, rfl⟩; simp⟩

@[simp] theorem mk_mul (γ : Γ) (g : G) : mk Γ (γ * g) = mk Γ g := (mk_eq_iff.2 ⟨γ, rfl⟩).symm

@[simp] theorem rmul_mk (g x : G) : rmul Γ g (mk Γ x) = mk Γ (x * g) := rfl

@[simp] theorem rmul_one (q : Quot Γ) : rmul Γ 1 q = q := Quotient.inductionOn q fun x => by simp

theorem rmul_mul (g h : G) (q : Quot Γ) : rmul Γ (g * h) q = rmul Γ h (rmul Γ g q) :=
  Quotient.inductionOn q fun x => by simp [mul_assoc]

theorem leftInv_lift {X : Type*} (F : Quot Γ → X) : LeftInv Γ (lift Γ F) :=
  fun γ h g => congrArg F (mk_mul ⟨γ, h⟩ g)

theorem LeftInv.eq_of_mk_eq {X : Type*} {φ : G → X} (h : LeftInv Γ φ) {x y : G} (e : mk Γ x = mk Γ y) : φ x = φ y := by
  obtain ⟨γ, rfl⟩ := mk_eq_iff.1 e
  exact (h γ γ.2 x).symm

theorem LeftInv.descend_mk {X : Type*} {φ : G → X} (h : LeftInv Γ φ) (g : G) : descend Γ φ (mk Γ g) = φ g :=
  h.eq_of_mk_eq (Quotient.out_eq _)

theorem LeftInv.lift_descend {X : Type*} {φ : G → X} (h : LeftInv Γ φ) : lift Γ (descend Γ φ) = φ :=
  funext h.descend_mk

@[simp] theorem descend_lift {X : Type*} (F : Quot Γ → X) : descend Γ (lift Γ F) = F :=
  funext fun q => congrArg F (Quotient.out_eq q)

theorem LeftInv.mul_right {X : Type*} {φ : G → X} (h : LeftInv Γ φ) (g : G) : LeftInv Γ fun x => φ (x * g) :=
  fun γ hγ x => by simp only [mul_assoc, h γ hγ]

theorem leftInv_orbitSum (f : G → ℂ) : LeftInv Γ (orbitSum Γ f) := fun δ hδ x => by
  rw [orbitSum, orbitSum, ← (Equiv.mulRight (⟨δ, hδ⟩ : Γ)).tsum_eq fun γ : Γ => f (γ * x)]
  simp [mul_assoc]

theorem kernel_eq_orbitSum (f : G → ℂ) (x : G) : kernel Γ f x = orbitSum Γ fun y => f (x⁻¹ * y) := by
  funext y; simp only [kernel, orbitSum, mul_assoc]

@[simp] theorem starFn_starFn (f : G → ℂ) : starFn (starFn f) = f := by funext g; simp [starFn]

theorem kernel_starFn (f : G → ℂ) (x y : G) : kernel Γ (starFn f) x y = conj (kernel Γ f y x) := by
  rw [kernel, kernel, Complex.conj_tsum, ← (Equiv.inv Γ).tsum_eq]
  simp [starFn, mul_assoc]

theorem leftInv_kernel_right (f : G → ℂ) (x : G) : LeftInv Γ (kernel Γ f x) :=
  kernel_eq_orbitSum (Γ := Γ) f x ▸ leftInv_orbitSum _

theorem leftInv_kernel_left (f : G → ℂ) (y : G) : LeftInv Γ fun x => kernel Γ f x y := fun γ hγ x => by
  have h := kernel_starFn (Γ := Γ) (starFn f)
  rw [starFn_starFn] at h
  simp only [h, leftInv_kernel_right _ y γ hγ x]

@[simp] theorem kernelQ_mk (f : G → ℂ) (x y : G) : kernelQ Γ f (mk Γ x) (mk Γ y) = kernel Γ f x y :=
  ((leftInv_kernel_left f _).descend_mk x).trans ((leftInv_kernel_right f x).descend_mk y)

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem hasCompactSupport_starFn {f : G → ℂ} (hf : HasCompactSupport f) : HasCompactSupport (starFn f) :=
  (hf.comp_homeomorph (Homeomorph.inv G)).comp_left (g := starRingEnd ℂ) (map_zero _)

theorem finite_mem_compact [T2Space G] [DiscreteTopology Γ] {C : Set G} (hC : IsCompact C) :
    {γ : Γ | (γ : G) ∈ C}.Finite :=
  ((Subgroup.isClosed_of_discrete (H := Γ)).isClosedEmbedding_subtypeVal.isCompact_preimage hC).finite_of_discrete

theorem finite_support_kernel [T2Space G] [DiscreteTopology Γ] {f : G → ℂ} (hf : HasCompactSupport f) (x y : G) :
    (Function.support fun γ : Γ => f (x⁻¹ * γ * y)).Finite :=
  (finite_mem_compact (hf.isCompact.image (f := fun z => x * z * y⁻¹) (by fun_prop))).subset fun γ h =>
    ⟨_, subset_tsupport f h, by simp [mul_assoc]⟩

theorem hasSum_kernel [T2Space G] [DiscreteTopology Γ] {f : G → ℂ} (hf : HasCompactSupport f) (x y : G) :
    HasSum (fun γ : Γ => f (x⁻¹ * γ * y)) (kernel Γ f x y) :=
  (summable_of_hasFiniteSupport (finite_support_kernel hf x y)).hasSum

omit [IsTopologicalGroup G] in

instance (priority := 50) countable_of_discrete [SecondCountableTopology G] [DiscreteTopology Γ] : Countable Γ :=
  TopologicalSpace.separableSpace_iff_countable.1 inferInstance

end Quotient

section Measure

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [DiscreteTopology Γ]

def stdDom : Set G := (GlobalTheory.FundDomDiscrete.exists_measurable_section Γ).choose

theorem measurableSet_stdDom : MeasurableSet (stdDom Γ) :=
  (GlobalTheory.FundDomDiscrete.exists_measurable_section Γ).choose_spec.1

theorem existsUnique_stdDom (x : G) : ∃! γ : Γ, (γ : G) * x ∈ stdDom Γ :=
  (GlobalTheory.FundDomDiscrete.exists_measurable_section Γ).choose_spec.2 x

theorem isFundamentalDomain_stdDom (μ : Measure G) : IsFundamentalDomain Γ (stdDom Γ) μ :=
  .mk' (measurableSet_stdDom Γ).nullMeasurableSet (existsUnique_stdDom Γ)

def sec (q : Quot Γ) : G := (existsUnique_stdDom Γ q.out).choose * q.out

def quotMeasure (μ : Measure G) : Measure (Quot Γ) := (μ.restrict (stdDom Γ)).map (mk Γ)

variable {Γ} {μ : Measure G} {𝓕 : Set G}

@[simp] theorem mk_sec (q : Quot Γ) : mk Γ (sec Γ q) = q := (mk_mul _ _).trans (Quotient.out_eq q)

theorem sec_mem (q : Quot Γ) : sec Γ q ∈ stdDom Γ := (existsUnique_stdDom Γ q.out).choose_spec.1

theorem sec_eq {q : Quot Γ} {x : G} (hx : x ∈ stdDom Γ) (e : mk Γ x = q) : sec Γ q = x := by
  obtain ⟨γ, h⟩ := mk_eq_iff.1 (e.trans (mk_sec q).symm)
  have h1 : γ = 1 := (existsUnique_stdDom Γ x).unique (h ▸ sec_mem q) (by simpa using hx)
  rw [← h, h1]
  simp

omit [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [BorelSpace G] [DiscreteTopology Γ] in

theorem measurable_mk : Measurable (mk Γ) := measurable_quotient_mk''

theorem measurableEmbedding_sec : MeasurableEmbedding (sec Γ) where
  injective := Function.LeftInverse.injective mk_sec
  measurable := fun s hs => by
    have : mk Γ ⁻¹' (sec Γ ⁻¹' s) = ⋃ γ : Γ, (fun x => (γ : G) * x) ⁻¹' (s ∩ stdDom Γ) := by
      ext x
      simp only [mem_preimage, mem_iUnion, mem_inter_iff]
      refine ⟨fun h => ?_, fun ⟨γ, h1, h2⟩ => by rwa [sec_eq h2 (mk_mul γ x)]⟩
      obtain ⟨γ, e⟩ := mk_eq_iff.1 (mk_sec (mk Γ x)).symm
      exact ⟨γ, e ▸ h, e ▸ sec_mem _⟩
    change MeasurableSet (mk Γ ⁻¹' (sec Γ ⁻¹' s))
    rw [this]
    exact .iUnion fun γ => measurable_const_mul _ (hs.inter (measurableSet_stdDom Γ))
  measurableSet_image' := fun s hs => by
    have : sec Γ '' s = mk Γ ⁻¹' s ∩ stdDom Γ := by
      ext x
      exact ⟨by rintro ⟨q, h, rfl⟩; exact ⟨by simpa using h, sec_mem q⟩, fun h => ⟨_, h.1, sec_eq h.2 rfl⟩⟩
    rw [this]
    exact (measurable_mk hs).inter (measurableSet_stdDom Γ)

theorem measurable_rmul_uncurry : Measurable fun p : Quot Γ × G => rmul Γ p.2 p.1 := by
  have : (fun p : Quot Γ × G => rmul Γ p.2 p.1) = fun p => mk Γ (sec Γ p.1 * p.2) := by
    funext p; rw [← rmul_mk, mk_sec]
  rw [this]
  exact measurable_mk.comp ((measurableEmbedding_sec.measurable.comp measurable_fst).mul measurable_snd)

theorem measurable_rmul (g : G) : Measurable (rmul Γ g) :=
  measurable_rmul_uncurry.comp (measurable_id.prodMk measurable_const)

theorem measurePreserving_sec : MeasurePreserving (sec Γ) (quotMeasure Γ μ) (μ.restrict (stdDom Γ)) :=
  ⟨measurableEmbedding_sec.measurable, by
    rw [quotMeasure, Measure.map_map measurableEmbedding_sec.measurable measurable_mk]
    exact (Measure.map_congr ((ae_restrict_mem (measurableSet_stdDom Γ)).mono fun x hx => sec_eq hx rfl)).trans
      Measure.map_id⟩

instance [SigmaFinite μ] : SigmaFinite (quotMeasure Γ μ) :=
  SigmaFinite.of_map _ measurableEmbedding_sec.measurable.aemeasurable
    (by rw [measurePreserving_sec.map_eq]; infer_instance)

theorem quotMeasure_smul (c : ℝ≥0∞) : quotMeasure Γ (c • μ) = c • quotMeasure Γ μ := by
  rw [quotMeasure, Measure.restrict_smul, Measure.map_smul, quotMeasure]

variable [μ.IsMulLeftInvariant]

theorem quotMeasure_eq (h : IsFundamentalDomain Γ 𝓕 μ) : quotMeasure Γ μ = (μ.restrict 𝓕).map (mk Γ) := by
  ext s hs
  rw [quotMeasure, Measure.map_apply measurable_mk hs, Measure.map_apply measurable_mk hs,
    Measure.restrict_apply (measurable_mk hs), Measure.restrict_apply (measurable_mk hs)]
  refine (isFundamentalDomain_stdDom Γ μ).measure_set_eq h (measurable_mk hs) fun γ => ?_
  ext x
  exact iff_of_eq (congrArg (· ∈ s) (mk_mul γ x))

theorem measurePreserving_mk (h : IsFundamentalDomain Γ 𝓕 μ) :
    MeasurePreserving (mk Γ) (μ.restrict 𝓕) (quotMeasure Γ μ) := ⟨measurable_mk, (quotMeasure_eq h).symm⟩

theorem quotMeasure_univ (h : IsFundamentalDomain Γ 𝓕 μ) : quotMeasure Γ μ univ = μ 𝓕 := by
  rw [quotMeasure_eq h, Measure.map_apply measurable_mk .univ, preimage_univ, Measure.restrict_apply_univ]

instance [NeZero μ] : NeZero (quotMeasure Γ μ) :=
  ⟨Measure.measure_univ_ne_zero.1 <| by
    rw [quotMeasure_univ (isFundamentalDomain_stdDom Γ μ)]
    exact (isFundamentalDomain_stdDom Γ μ).measure_ne_zero (NeZero.ne μ)⟩

theorem ae_quotMeasure_iff {p : Quot Γ → Prop} : (∀ᵐ q ∂quotMeasure Γ μ, p q) ↔ ∀ᵐ g ∂μ, p (mk Γ g) := by
  have h : (∀ᵐ g ∂μ.restrict (stdDom Γ), p (mk Γ g)) ↔ ∀ᵐ q ∂quotMeasure Γ μ, p q := by
    rw [← measurePreserving_sec.map_eq, measurableEmbedding_sec.ae_map_iff]; simp
  refine h.symm.trans ⟨fun h' => ?_, ae_restrict_of_ae⟩
  refine (isFundamentalDomain_stdDom Γ μ).measure_zero_of_invariant _ (fun γ => ?_) ?_
  · ext x
    rw [mem_smul_set_iff_inv_smul_mem]
    exact iff_of_eq (congrArg (¬ p ·) (mk_mul γ⁻¹ x))
  · rwa [← Measure.restrict_apply' (measurableSet_stdDom Γ)]

theorem quasiMeasurePreserving_mk : Measure.QuasiMeasurePreserving (mk Γ) μ (quotMeasure Γ μ) :=
  ⟨measurable_mk, .mk fun s hs h => by
    rw [Measure.map_apply measurable_mk hs]
    exact measure_eq_zero_iff_ae_notMem.2 (ae_quotMeasure_iff.1 (measure_eq_zero_iff_ae_notMem.1 h))⟩

theorem lintegral_quotMeasure (h : IsFundamentalDomain Γ 𝓕 μ) (F : Quot Γ → ℝ≥0∞) :
    ∫⁻ q, F q ∂quotMeasure Γ μ = ∫⁻ g in 𝓕, F (mk Γ g) ∂μ := by
  rw [h.setLIntegral_eq (isFundamentalDomain_stdDom Γ μ) _ fun γ x => congrArg F (mk_mul γ x),
    ← measurePreserving_sec.lintegral_comp_emb measurableEmbedding_sec]
  simp

theorem integral_quotMeasure {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (h : IsFundamentalDomain Γ 𝓕 μ)
    (F : Quot Γ → X) : ∫ q, F q ∂quotMeasure Γ μ = ∫ g in 𝓕, F (mk Γ g) ∂μ := by
  rw [h.setIntegral_eq (isFundamentalDomain_stdDom Γ μ) fun γ x => congrArg F (mk_mul γ x),
    ← measurePreserving_sec.integral_comp measurableEmbedding_sec]
  simp

theorem aestronglyMeasurable_quotMeasure_iff (h : IsFundamentalDomain Γ 𝓕 μ) {F : Quot Γ → ℂ} :
    AEStronglyMeasurable F (quotMeasure Γ μ) ↔ AEStronglyMeasurable (lift Γ F) (μ.restrict 𝓕) := by
  rw [h.aestronglyMeasurable_on_iff (isFundamentalDomain_stdDom Γ μ) fun γ x => congrArg F (mk_mul γ x),
    ← measurePreserving_sec.aestronglyMeasurable_comp_iff measurableEmbedding_sec]
  simp [Function.comp_def, lift]

theorem aestronglyMeasurable_quotMeasure_iff_lift {F : Quot Γ → ℂ} :
    AEStronglyMeasurable F (quotMeasure Γ μ) ↔ AEStronglyMeasurable (lift Γ F) μ :=
  ⟨fun h => h.comp_quasiMeasurePreserving quasiMeasurePreserving_mk,
    fun h => (aestronglyMeasurable_quotMeasure_iff (isFundamentalDomain_stdDom Γ μ)).2 h.restrict⟩

theorem memLp_quotMeasure_iff (h : IsFundamentalDomain Γ 𝓕 μ) {F : Quot Γ → ℂ} {p : ℝ≥0∞} :
    MemLp F p (quotMeasure Γ μ) ↔ MemLp (lift Γ F) p (μ.restrict 𝓕) :=
  ⟨fun h' => h'.comp_measurePreserving (measurePreserving_mk h), fun h' => by
    have hm := (aestronglyMeasurable_quotMeasure_iff h).2 h'.1
    exact ⟨hm, (eLpNorm_comp_measurePreserving hm (measurePreserving_mk h)).symm.trans_lt h'.2⟩⟩

theorem lintegral_eq_lintegral_tsum {f : G → ℝ≥0∞} (hf : AEMeasurable f μ) :
    ∫⁻ g, f g ∂μ = ∫⁻ q, ∑' γ : Γ, f (γ * q.out) ∂quotMeasure Γ μ := by
  have h := isFundamentalDomain_stdDom Γ μ
  have hi : LeftInv Γ fun x => ∑' γ : Γ, f (γ * x) := fun δ hδ x => by
    beta_reduce
    rw [← (Equiv.mulRight (⟨δ, hδ⟩ : Γ)).tsum_eq fun γ : Γ => f (γ * x)]
    simp [mul_assoc]
  refine (h.lintegral_eq_tsum'' f).trans ((lintegral_tsum fun γ : Γ => (hf.comp_quasiMeasurePreserving
    (measurePreserving_mul_left μ (γ : G)).quasiMeasurePreserving).restrict).symm.trans ?_)
  exact ((lintegral_quotMeasure h (descend Γ _)).trans (lintegral_congr hi.descend_mk)).symm

theorem integral_eq_integral_orbitSum {f : G → ℂ} (hf : Integrable f μ) :
    ∫ g, f g ∂μ = ∫ q, descend Γ (orbitSum Γ f) q ∂quotMeasure Γ μ := by
  have h := isFundamentalDomain_stdDom Γ μ
  rw [integral_quotMeasure h, h.integral_eq_tsum'' f hf]
  simp only [(leftInv_orbitSum f).descend_mk, orbitSum]
  refine (integral_tsum (fun γ : Γ => (hf.1.comp_quasiMeasurePreserving
    (measurePreserving_mul_left μ (γ : G)).quasiMeasurePreserving).restrict) ?_).symm
  exact ((h.lintegral_eq_tsum'' fun x => ‖f x‖ₑ).symm.trans_lt hf.2).ne

theorem quotMeasure_le {A : Set (Quot Γ)} (hA : MeasurableSet A) {T : Set G} (h : A ⊆ mk Γ '' T) :
    quotMeasure Γ μ A ≤ μ T := by
  rw [quotMeasure, Measure.map_apply measurable_mk hA, (isFundamentalDomain_stdDom Γ μ).measure_eq_tsum T]
  refine (measure_mono fun x hx => ?_ : _ ≤ μ.restrict _ (⋃ γ : Γ, γ • T)).trans
    ((measure_iUnion_le _).trans (le_of_eq (tsum_congr fun γ => Measure.restrict_apply' (measurableSet_stdDom Γ))))
  obtain ⟨y, hy, e⟩ := h hx
  obtain ⟨γ, rfl⟩ := mk_eq_iff.1 e
  exact mem_iUnion.2 ⟨γ, y, hy, rfl⟩

theorem measurePreserving_rmul [μ.IsMulRightInvariant] (g : G) :
    MeasurePreserving (rmul Γ g) (quotMeasure Γ μ) (quotMeasure Γ μ) := by
  have h := isFundamentalDomain_stdDom Γ μ
  have h' : IsFundamentalDomain Γ ((· * g) ⁻¹' stdDom Γ) μ :=
    h.preimage_of_equiv (measurePreserving_mul_right μ g).quasiMeasurePreserving Function.bijective_id
      fun γ x => mul_assoc _ _ _
  refine ⟨measurable_rmul g, ?_⟩
  conv_lhs => rw [quotMeasure_eq h', Measure.map_map (measurable_rmul g) measurable_mk]
  exact ((measurePreserving_mk h).comp ((measurePreserving_mul_right μ g).restrict_preimage
    (measurableSet_stdDom Γ))).map_eq

end Measure

section L2

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [DiscreteTopology Γ] (μ : Measure G)

abbrev L2 : Type _ := Lp ℂ 2 (quotMeasure Γ μ)

def MemL2Quotient (φ : G → ℂ) : Prop := LeftInv Γ φ ∧ MemLp (descend Γ φ) 2 (quotMeasure Γ μ)

def pet (φ ψ : G → ℂ) : ℂ := ∫ q, descend Γ φ q * conj (descend Γ ψ q) ∂quotMeasure Γ μ

def convR (f φ : G → ℂ) : G → ℂ := fun x => ∫ y, f y * φ (x * y) ∂μ

def conv (f f' : G → ℂ) : G → ℂ := fun y => ∫ x, f x * f' (x⁻¹ * y) ∂μ

variable {Γ μ} {𝓕 : Set G} {φ ψ : G → ℂ}

def MemL2Quotient.toL2 (h : MemL2Quotient Γ μ φ) : L2 Γ μ := h.2.toLp _

theorem memL2_lift (F : L2 Γ μ) : MemL2Quotient Γ μ (lift Γ F) :=
  ⟨leftInv_lift _, by rw [descend_lift]; exact Lp.memLp F⟩

@[simp] theorem toL2_lift (F : L2 Γ μ) : (memL2_lift F).toL2 = F :=
  Lp.ext ((memL2_lift F).2.coeFn_toLp.trans (by rw [descend_lift]))

theorem MemL2Quotient.coeFn_toL2 (h : MemL2Quotient Γ μ φ) : h.toL2 =ᵐ[quotMeasure Γ μ] descend Γ φ := h.2.coeFn_toLp

theorem MemL2Quotient.integrable_mul_conj (h : MemL2Quotient Γ μ φ) (h' : MemL2Quotient Γ μ ψ) :
    Integrable (fun q => descend Γ φ q * conj (descend Γ ψ q)) (quotMeasure Γ μ) :=
  h.2.integrable_mul h'.2.star

theorem MemL2Quotient.inner_toL2_eq_theta_pairing (h : MemL2Quotient Γ μ φ) (h' : MemL2Quotient Γ μ ψ) : ⟪h'.toL2, h.toL2⟫_ℂ = pet Γ μ φ ψ := by
  rw [MeasureTheory.L2.inner_def, pet]
  refine integral_congr_ae ?_
  filter_upwards [h.coeFn_toL2, h'.coeFn_toL2] with q e e'
  simp [e, e']

omit [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [BorelSpace G] [DiscreteTopology Γ] in

theorem LeftInv.convR (h : LeftInv Γ φ) (f : G → ℂ) : LeftInv Γ (convR μ f φ) := fun γ hγ x => by
  simp only [AutomorphicL2Unitary.convR, mul_assoc, h γ hγ]

variable [μ.IsMulLeftInvariant]

omit [SecondCountableTopology G] in

theorem convR_eq (f φ : G → ℂ) (x : G) : convR μ f φ x = ∫ y, f (x⁻¹ * y) * φ y ∂μ := by
  rw [← integral_mul_left_eq_self _ x]
  simp [convR]

theorem memL2_iff_fundamental_domain (h : IsFundamentalDomain Γ 𝓕 μ) : MemL2Quotient Γ μ φ ↔ LeftInv Γ φ ∧ MemLp φ 2 (μ.restrict 𝓕) :=
  and_congr_right fun hφ => by rw [memLp_quotMeasure_iff h, hφ.lift_descend]

theorem pet_eq (h : IsFundamentalDomain Γ 𝓕 μ) (hφ : LeftInv Γ φ) (hψ : LeftInv Γ ψ) :
    pet Γ μ φ ψ = ∫ g in 𝓕, φ g * conj (ψ g) ∂μ := by
  simp only [pet, integral_quotMeasure h, hφ.descend_mk, hψ.descend_mk]

theorem MemL2Quotient.lift_toL2_ae_eq (h : MemL2Quotient Γ μ φ) : lift Γ h.toL2 =ᵐ[μ] φ :=
  (ae_quotMeasure_iff.1 h.coeFn_toL2).mono fun g e => e.trans (h.1.descend_mk g)

theorem l2DiscreteQuotient_ext_iff_lift_ae_eq {F F' : L2 Γ μ} : F = F' ↔ lift Γ F =ᵐ[μ] lift Γ F' :=
  Lp.ext_iff.trans ae_quotMeasure_iff

theorem MemL2Quotient.toL2_eq_iff_ae_eq (h : MemL2Quotient Γ μ φ) (h' : MemL2Quotient Γ μ ψ) : h.toL2 = h'.toL2 ↔ φ =ᵐ[μ] ψ :=
  l2DiscreteQuotient_ext_iff_lift_ae_eq.trans ⟨fun e => h.lift_toL2_ae_eq.symm.trans (e.trans h'.lift_toL2_ae_eq),
    fun e => h.lift_toL2_ae_eq.trans (e.trans h'.lift_toL2_ae_eq.symm)⟩

variable [μ.IsMulRightInvariant]

variable (Γ μ) in

def R : G →* (L2 Γ μ →L[ℂ] L2 Γ μ) where
  toFun g := (Lp.compMeasurePreservingₗᵢ ℂ (rmul Γ g) (measurePreserving_rmul g)).toContinuousLinearMap
  map_one' := ContinuousLinearMap.ext fun F => Lp.ext <|
    (Lp.coeFn_compMeasurePreserving F _).trans (.of_forall fun q => congrArg F (rmul_one q))
  map_mul' g h := ContinuousLinearMap.ext fun F => Lp.ext <|
    (Lp.coeFn_compMeasurePreserving F _).trans <| EventuallyEq.symm <|
      (Lp.coeFn_compMeasurePreserving _ (measurePreserving_rmul g)).trans <|
        ((measurePreserving_rmul g).quasiMeasurePreserving.ae
          (Lp.coeFn_compMeasurePreserving F (measurePreserving_rmul h))).mono fun q e =>
            e.trans (congrArg F (rmul_mul g h q).symm)

variable (Γ μ) in

abbrev Rop (f : G → ℂ) : L2 Γ μ →L[ℂ] L2 Γ μ := repOp (R Γ μ) μ f

variable (Γ μ) in

abbrev L2disc : Submodule ℂ (L2 Γ μ) := disc (R Γ μ)

variable (Γ μ) in

abbrev Rdisc : G →* (L2disc Γ μ →L[ℂ] L2disc Γ μ) := (isSubrep_disc (π := R Γ μ)).rep

theorem coeFn_R (g : G) (F : L2 Γ μ) : R Γ μ g F =ᵐ[quotMeasure Γ μ] fun q => F (rmul Γ g q) :=
  Lp.coeFn_compMeasurePreserving F (measurePreserving_rmul g)

theorem lift_R (g : G) (F : L2 Γ μ) : lift Γ (R Γ μ g F) =ᵐ[μ] fun x => lift Γ F (x * g) :=
  ae_quotMeasure_iff.1 (coeFn_R g F)

theorem norm_R (g : G) (F : L2 Γ μ) : ‖R Γ μ g F‖ = ‖F‖ := Lp.norm_compMeasurePreserving F (measurePreserving_rmul g)

theorem MemL2Quotient.mul_right (h : MemL2Quotient Γ μ φ) (g : G) : MemL2Quotient Γ μ fun x => φ (x * g) :=
  ⟨h.1.mul_right g, by
    have : descend Γ (fun x => φ (x * g)) = descend Γ φ ∘ rmul Γ g := funext fun q =>
      Quotient.inductionOn q fun x => ((h.1.mul_right g).descend_mk x).trans (h.1.descend_mk (x * g)).symm
    rw [this]
    exact h.2.comp_measurePreserving (measurePreserving_rmul g)⟩

theorem right_translate_toL2 (h : MemL2Quotient Γ μ φ) (g : G) : R Γ μ g h.toL2 = (h.mul_right g).toL2 :=
  l2DiscreteQuotient_ext_iff_lift_ae_eq.2 <| (lift_R g _).trans <| EventuallyEq.trans
    ((measurePreserving_mul_right μ g).quasiMeasurePreserving.ae h.lift_toL2_ae_eq) (h.mul_right g).lift_toL2_ae_eq.symm

omit [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] in

theorem memL2_const [IsFiniteMeasure (quotMeasure Γ μ)] (c : ℂ) : MemL2Quotient Γ μ fun _ => c :=
  ⟨fun _ _ _ => rfl, memLp_const c⟩

theorem isIrredSubrep_const [IsFiniteMeasure (quotMeasure Γ μ)] [NeZero μ] :
    IsIrredSubrep (R Γ μ) (ℂ ∙ (memL2_const (Γ := Γ) (μ := μ) 1).toL2) := by
  refine isIrredSubrep_span_singleton (fun h => ?_) fun g => ⟨1, by rw [right_translate_toL2, one_smul]⟩
  have h1 := (memL2_const (Γ := Γ) (μ := μ) 1).coeFn_toL2
  rw [h] at h1
  obtain ⟨q, hq⟩ := ((Lp.coeFn_zero ℂ 2 _).symm.trans h1).exists
  exact zero_ne_one hq

variable [LocallyCompactSpace G] [IsFiniteMeasureOnCompacts μ]

theorem continuous_R (F : L2 Γ μ) : Continuous fun g => R Γ μ g F := by
  refine Lp.induction (p := 2) ENNReal.ofNat_ne_top (fun F => Continuous fun g => R Γ μ g F) ?_ ?_ ?_ F
  · intro c s hs hμs
    rw [Lp.simpleFunc.coe_indicatorConst]
    have hS : MeasurableSet (mk Γ ⁻¹' s ∩ stdDom Γ) := (measurable_mk hs).inter (measurableSet_stdDom Γ)
    have key : ∀ a b : G, rmul Γ a ⁻¹' s \ rmul Γ b ⁻¹' s ⊆
        mk Γ '' ((· * a) ⁻¹' (mk Γ ⁻¹' s ∩ stdDom Γ) \ (· * b) ⁻¹' (mk Γ ⁻¹' s ∩ stdDom Γ)) := by
      intro a b q hq
      have e : mk Γ (sec Γ (rmul Γ a q) * a⁻¹) = q := by rw [← rmul_mk, mk_sec, ← rmul_mul, mul_inv_cancel, rmul_one]
      refine ⟨_, ⟨?_, fun h => hq.2 ?_⟩, e⟩
      · simpa using ⟨hq.1, sec_mem _⟩
      · rw [← e]; exact h.1
    refine (continuous_indicatorConstLp_set (p := 2) (μ := quotMeasure Γ μ) (c := c) ENNReal.ofNat_ne_top
      (hs := fun g => measurable_rmul g hs)
      (hμs := fun g => by rw [(measurePreserving_rmul g).measure_preimage hs.nullMeasurableSet]; exact hμs.ne)
      fun g₀ => ?_).congr fun g =>
        (Lp.indicatorConstLp_compMeasurePreserving hs hμs.ne c (measurePreserving_rmul g)).symm
    let m : C(G, C(G, G)) := ContinuousMap.curry ⟨fun p : G × G => p.2 * p.1, by fun_prop⟩
    have ht := tendsto_measure_symmDiff_preimage_nhds_zero (μ := μ) (ν := μ) (f := m) (g := m g₀)
      (m.continuous.tendsto g₀) (Eventually.of_forall fun g => measurePreserving_mul_right μ g)
      (measurePreserving_mul_right μ g₀) hS.nullMeasurableSet (by
        rw [← Measure.restrict_apply (measurable_mk hs), ← Measure.map_apply measurable_mk hs]; exact hμs.ne)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht (fun _ => zero_le) fun g => ?_
    refine quotMeasure_le ((measurable_rmul g hs).symmDiff (measurable_rmul g₀ hs)) ?_
    exact union_subset ((key g g₀).trans (image_mono subset_union_left))
      ((key g₀ g).trans (image_mono subset_union_right))
  · intro f g hf hg _ h1 h2
    simp only [map_add]
    exact h1.add h2
  · refine isClosed_of_closure_subset fun F hF => ?_
    refine TendstoUniformly.continuous (F := fun F' g => R Γ μ g F') (p := 𝓝 F) ?_
      (mem_closure_iff_frequently.1 hF)
    refine Metric.tendstoUniformly_iff.2 fun ε hε => ?_
    filter_upwards [Metric.ball_mem_nhds F hε] with F' h g
    rw [dist_eq_norm, ← map_sub, norm_R, ← dist_eq_norm, dist_comm]
    exact h

variable (Γ μ) in

theorem isUnitaryRep_R : IsUnitaryRep (R Γ μ) := ⟨norm_R, continuous_R⟩

variable {f f' : G → ℂ}

theorem isRepOp_Rop (hf : Integrable f μ) : IsRepOp (R Γ μ) μ f (Rop Γ μ f) :=
  isRepOp_of_integrable (isUnitaryRep_R Γ μ) hf

theorem IsSubrep.Rop_mem {W : Submodule ℂ (L2 Γ μ)} (hW : IsSubrep (R Γ μ) W) (hf : Integrable f μ) {F : L2 Γ μ}
    (hF : F ∈ W) : Rop Γ μ f F ∈ W := hW.map_mem_of_isRepOp (isRepOp_Rop hf) hF

theorem adjoint_Rop [μ.IsOpenPosMeasure] (hf : Continuous f) (hc : HasCompactSupport f) :
    ContinuousLinearMap.adjoint (Rop Γ μ f) = Rop Γ μ (starFn f) := by
  have : μ.IsHaarMeasure := {}
  have := GlobalTheory.SqIntRep.isInvInvariant_of_unimodular μ
  exact (isUnitaryRep_R Γ μ).adjoint_repOp hf hc

end L2

section Adelic

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.AdelicU

instance discreteTopology_ratPts {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : DiscreteTopology (ratPts σ J) :=
  GlobalTheory.RationalDiscrete.discreteTopology_HFinIn σ J

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (V : HSp D)

instance discreteTopology_GQ : DiscreteTopology (GQ V) := GlobalTheory.RationalDiscrete.discreteTopology_GQ D V

variable (μ : Measure (GA D V))

abbrev autMeasure : Measure (AutQ V) := quotMeasure (GQ V) μ

abbrev DividedPowerChartLift : Type := L2 (GQ V) μ

abbrev kernelG (f : GA D V → ℂ) (x y : GA D V) : ℂ := kernel (GQ V) f x y

abbrev RG [μ.IsHaarMeasure] [μ.IsMulRightInvariant] : GA D V →* (DividedPowerChartLift V μ →L[ℂ] DividedPowerChartLift V μ) := R (GQ V) μ

abbrev RopG [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (f : GA D V → ℂ) : DividedPowerChartLift V μ →L[ℂ] DividedPowerChartLift V μ := Rop (GQ V) μ f

abbrev L2discG [μ.IsHaarMeasure] [μ.IsMulRightInvariant] : Submodule ℂ (DividedPowerChartLift V μ) := L2disc (GQ V) μ

theorem isUnitaryRep_RG [μ.IsHaarMeasure] [μ.IsMulRightInvariant] : IsUnitaryRep (RG V μ) := isUnitaryRep_R _ μ

variable {V μ}

theorem leftInv_of_isAutFun {φ : GA D V → ℂ} (h : IsAutFun V φ) : LeftInv (GQ V) φ := h.left

theorem isVolPair_volPair (h : ∃ p : Measure (GA D V) × Set (GA D V), IsVolPair D V p.1 p.2) :
    IsVolPair D V (volPair V).1 (volPair V).2 := by
  rw [volPair, dif_pos h]; exact h.choose_spec

theorem muQ_eq (h : ∃ p : Measure (GA D V) × Set (GA D V), IsVolPair D V p.1 p.2) :
    muQ V = autMeasure V (volPair V).1 :=
  have := (isVolPair_volPair h).1.1
  (quotMeasure_eq (isVolPair_volPair h).2).symm

end Adelic

example {G : Type} [Group G] (f : G → ℂ) (x y : G) : kernel ⊥ f x y = f (x⁻¹ * y) := by
  rw [kernel, tsum_eq_single 1 fun γ h => absurd (Subsingleton.elim _ _) h]
  simp

example {G : Type} [Group G] [Countable G] [TopologicalSpace G] [DiscreteTopology G] [MeasurableSpace G]
    [BorelSpace G] : quotMeasure (⊤ : Subgroup G) Measure.count univ = 1 := by
  rw [quotMeasure_univ (Γ := ⊤) (𝓕 := {1}) (.mk' (measurableSet_singleton 1).nullMeasurableSet fun x =>
    ⟨⟨x⁻¹, Subgroup.mem_top _⟩, inv_mul_cancel x, fun γ h => Subtype.ext (eq_inv_of_mul_eq_one_left (show (γ : G) * x = 1 from h))⟩)]
  simp

example {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [CompactSpace G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (χ : G →* ℂ) (hχ : Continuous χ) :
    ∃ F : L2 ⊥ μ, F ≠ 0 ∧ lift ⊥ F =ᵐ[μ] χ ∧ (∀ g, R ⊥ μ g F = χ g • F) ∧ F ∈ L2disc ⊥ μ := by
  have hD : IsFundamentalDomain (⊥ : Subgroup G) (univ : Set G) μ :=
    .mk' .univ fun _ => ⟨1, trivial, fun _ _ => Subsingleton.elim _ _⟩
  have h : MemL2Quotient ⊥ μ χ := (memL2_iff_fundamental_domain hD).2 ⟨fun γ hγ g => by rw [Subgroup.mem_bot.1 hγ, one_mul],
    hχ.memLp_of_hasCompactSupport (.of_compactSpace _)⟩
  have h0 : h.toL2 ≠ 0 := fun e => by
    have h1 := h.lift_toL2_ae_eq
    rw [e] at h1
    obtain ⟨x, hx⟩ := ((ae_quotMeasure_iff.1 (Lp.coeFn_zero ℂ 2 (quotMeasure ⊥ μ))).and h1).exists
    exact ((Group.isUnit x).map χ).ne_zero (hx.2.symm.trans hx.1)
  have h2 : ∀ g, R ⊥ μ g h.toL2 = χ g • h.toL2 := fun g => l2DiscreteQuotient_ext_iff_lift_ae_eq.2 <| by
    filter_upwards [lift_R g h.toL2, (measurePreserving_mul_right μ g).quasiMeasurePreserving.ae h.lift_toL2_ae_eq,
      ae_quotMeasure_iff.1 (Lp.coeFn_smul (χ g) h.toL2), h.lift_toL2_ae_eq] with x e1 e2 e3 e4
    rw [e1, e2, map_mul, mul_comm, ← e4]
    exact e3.symm
  exact ⟨_, h0, h.lift_toL2_ae_eq, h2,
    (isIrredSubrep_span_singleton h0 fun g => ⟨_, h2 g⟩).le_disc (Submodule.mem_span_singleton_self _)⟩

end GlobalTheory.AutomorphicL2Unitary

end
