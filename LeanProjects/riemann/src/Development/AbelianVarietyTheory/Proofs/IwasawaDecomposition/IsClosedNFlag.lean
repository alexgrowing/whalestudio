import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DifferentiableOneP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueInfFam
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOpenKer
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionStarStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothAutomorphicFormRightTranslateFiniteAdelicStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionTranslateAtRealPlaceStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterInfinityExponentGroupLawsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCuspFunctionClosedUnderOperationsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousAdelicUnitaryEmbeddingStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryUnimodularExistsFundamentalDomainStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLatticeStabiliserSubgroupOutsidePlacesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeterssonNormSqPosAutomorphicFunctionUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteBesselPeriodSesquilinearStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueNormalizedHaarMeasureAdelicUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BesselCharacterGenericCharacterLawsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotropicUnipotentRadicalsRationalCocompactStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct

namespace GlobalTheory.Mem.TrueRecord

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem exists_pair (V : HSp D) : ∃ m : Measure (GA D V) × Set (GA D V), IsQuot V m.1 m.2 ∧ (V.SigOK → IsVolPair D V m.1 m.2) := by
  by_cases hV : V.SigOK
  · obtain ⟨μ, hμ, -⟩ := GlobalTheory.T.existsUnique_normalizedHaarMeasure_adelicUnitary D V hV
    obtain ⟨-, 𝓕, h𝓕⟩ := GlobalTheory.T.adelicUnitary_unimodular_exists_fundamentalDomain D V μ hμ.1
    exact ⟨(μ, 𝓕), ⟨hμ.1, h𝓕⟩, fun _ => ⟨hμ, h𝓕⟩⟩
  · obtain ⟨i1, i2, i3, i4, i5, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
    obtain ⟨-, 𝓕, h𝓕⟩ := GlobalTheory.T.adelicUnitary_unimodular_exists_fundamentalDomain D V Measure.haar inferInstance
    exact ⟨(Measure.haar, 𝓕), ⟨inferInstance, h𝓕⟩, fun h => absurd h hV⟩

def mu (V : HSp D) : Measure (GA D V) := (exists_pair V).choose.1

def dom (V : HSp D) : Set (GA D V) := (exists_pair V).choose.2

theorem quot_mu (V : HSp D) : IsQuot V (mu V) (dom V) := (exists_pair V).choose_spec.1

theorem integral_mu {V : HSp D} (hV : V.SigOK) {μ 𝓕} (h : IsVolPair D V μ 𝓕) (f : GA D V → ℂ)
    (hf : ∀ γ ∈ GQ V, ∀ g, f (γ * g) = f g) : ∫ g in dom V, f g ∂(mu V) = ∫ g in 𝓕, f g ∂μ := by
  obtain ⟨i1, i2, i3, i4, i5, -, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  have h0 : IsVolPair D V (mu V) (dom V) := (exists_pair V).choose_spec.2 hV
  obtain rfl : μ = mu V := (GlobalTheory.T.existsUnique_normalizedHaarMeasure_adelicUnitary D V hV).unique h.1 h0.1
  haveI := h.1.1
  exact h0.2.setIntegral_eq h.2 fun γ g => hf γ γ.2 g

variable {θ : InfF D}

theorem aut (hθ : IsInfFam θ) {V : HSp D} (φ : AFs θ V) : IsAutFunSm θ V φ.1 :=
  (GlobalTheory.Mem.AutSpace.mem_AFs_iff D θ hθ V φ.1).1 φ.2

theorem formSub (D : D7) : FormSub D := GlobalTheory.Mem.AutSpace.mem_AFs_iff D

theorem cuspF (hθ : IsInfFam θ) {V : HSp D} (φ : CuspS θ V) : IsCuspForm θ V φ.1 := (mem_CuspS (formSub D) hθ).1 φ.2

def intForm {X Y Z : Type} [MeasurableSpace Z] (μ : Measure Z) (P : Submodule ℂ (X → ℂ)) (Q : Submodule ℂ (Y → ℂ))
    (a : Z → X) (b : Z → Y) (hi : ∀ (φ : P) (F : Q), Integrable (fun z => star (φ.1 (a z)) * F.1 (b z)) μ) :
    P →ₗ⋆[ℂ] Q →ₗ[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun φ F => ∫ z, star (φ.1 (a z)) * F.1 (b z) ∂μ)
    (fun φ φ' F => by
      rw [← integral_add (hi φ F) (hi φ' F)]
      simp [add_mul])
    (fun c φ F => by
      rw [← integral_smul]
      simp [mul_assoc])
    (fun φ F F' => by
      rw [← integral_add (hi φ F) (hi φ F')]
      simp [mul_add])
    (fun c φ F => by
      rw [← integral_smul]
      simp [mul_left_comm])

def petForm (hP : PetInt D) (hθ : IsInfFam θ) (V : HSp D) : AFs θ V →ₗ⋆[ℂ] CuspS θ V →ₗ[ℂ] ℂ :=
  intForm ((mu V).restrict (dom V)) _ _ id id fun φ F => hP θ hθ V _ _ (quot_mu V) _ _ (aut hθ φ) (cuspF hθ F)

theorem petForm_apply (hP : PetInt D) (hθ : IsInfFam θ) (V : HSp D) (φ F) :
    petForm hP hθ V φ F = ∫ g in dom V, star (φ.1 g) * F.1 g ∂(mu V) := rfl

theorem exists_top (hT : TopInt D) (hθ : IsInfFam θ) (A B : HSp D) (ι : B.V →ₗ[D.host.E] A.V) :
    ∃ b : AFs θ A →ₗ⋆[ℂ] CuspS θ B →ₗ[ℂ] ℂ, B.SigOK → HSpace.IsIsomEmb B A ι → ∀ μ 𝓕, IsVolPair D B μ 𝓕 →
      ∀ s : GA D B → GA D A, (∀ h, EmbRel A B ι (s h) h) → ∀ φ F, b φ F = ∫ h in 𝓕, star (φ.1 (s h)) * F.1 h ∂μ := by
  by_cases hι : HSpace.IsIsomEmb B A ι
  · obtain ⟨s, -, hs, hq⟩ := GlobalTheory.T.exists_continuous_adelicUnitaryEmbedding D A B ι hι
    refine ⟨intForm ((mu B).restrict (dom B)) _ _ s id fun φ F =>
      hT θ hθ A B ι hι _ _ (quot_mu B) s (fun h => (hs h _).2 rfl) _ _ (aut hθ φ) (cuspF hθ F), ?_⟩
    intro hB _ μ 𝓕 hμ s' hs' φ F
    obtain rfl : s' = s := funext fun h => (hs h _).1 (hs' h)
    refine integral_mu hB hμ (fun h => star (φ.1 (s h)) * F.1 h) fun γ hγ g => ?_
    rw [map_mul, (aut hθ φ).left _ (hq γ hγ), (cuspF hθ F).1.left γ hγ]
  · exact ⟨0, fun _ h => absurd h hι⟩

theorem exists_lift (hL : LiftAut D) (hθ : IsInfFam θ) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1))
    (Wf : WeilFun D ψ) (V W : HSp D) (χ χ' : IdC D) :
    ∃ t : ThS ψ V W →ₗ[ℂ] CuspS θ V →ₗ[ℂ] AFs θ W, (¬ (admitted V W χ χ' ∧ V.SigOK) → t = 0) ∧
      (admitted V W χ χ' → V.SigOK → ∀ μ 𝓕, IsVolPair D V μ 𝓕 → ∀ Φ F h,
        (t Φ F).1 h = ∫ g in 𝓕, Wf.ker V W χ χ' Φ g h * F.1 g ∂μ) := by
  by_cases h : admitted V W χ χ' ∧ V.SigOK
  · have k := fun Φ (F : CuspS θ V) => hL θ hθ ψ hψ Wf V W χ χ' h.1 _ _ (quot_mu V) Φ F.1 (cuspF hθ F)
    refine ⟨LinearMap.mk₂ ℂ (fun Φ F => ⟨_, Submodule.subset_span (k Φ F).2⟩) ?_ ?_ ?_ ?_, fun h' => absurd h h', ?_⟩
    · intro Φ Φ' F
      ext x
      simp only [Submodule.coe_add, Pi.add_apply]
      rw [← integral_add ((k Φ F).1 x) ((k Φ' F).1 x)]
      simp [WeilFun.ker, add_mul]
    · intro c Φ F
      ext x
      simp only [Submodule.coe_smul, Pi.smul_apply]
      rw [← integral_smul]
      simp [WeilFun.ker, mul_assoc]
    · intro Φ F F'
      ext x
      simp only [Submodule.coe_add, Pi.add_apply]
      rw [← integral_add ((k Φ F).1 x) ((k Φ F').1 x)]
      simp [mul_add]
    · intro c Φ F
      ext x
      simp only [Submodule.coe_smul, Pi.smul_apply]
      rw [← integral_smul]
      simp [mul_left_comm]
    · intro ha hV μ 𝓕 hμ Φ F x
      refine integral_mu hV hμ (fun g => Wf.ker V W χ χ' Φ g x * F.1 g) fun γ hγ g => ?_
      have := Wf.ker_left ha Φ hγ (one_mem (GQ W)) g x
      rw [one_mul] at this
      rw [this, (cuspF hθ F).1.left γ hγ]
  · exact ⟨0, fun _ => rfl, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩

theorem integral_unit {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    [LocallyCompactSpace G] [SecondCountableTopology G] (Γ : Subgroup G) [Countable Γ] {μ μ' : Measure G} {𝓕 𝓕' : Set G}
    (h1 : μ.IsHaarMeasure) (h2 : IsFundamentalDomain Γ 𝓕 μ) (h3 : μ 𝓕 = 1)
    (k1 : μ'.IsHaarMeasure) (k2 : IsFundamentalDomain Γ 𝓕' μ') (k3 : μ' 𝓕' = 1)
    (f : G → ℂ) (hf : ∀ γ ∈ Γ, ∀ n, f (γ * n) = f n) : ∫ n in 𝓕, f n ∂μ = ∫ n in 𝓕', f n ∂μ' := by
  have e := Measure.isMulLeftInvariant_eq_smul μ μ'
  set c := Measure.haarScalarFactor μ μ'
  have k4 : IsFundamentalDomain Γ 𝓕' μ := k2.mono (by rw [e]; exact Measure.smul_absolutelyContinuous)
  have h4 : μ 𝓕' = 1 := (k4.measure_eq h2).trans h3
  have hc : c = 1 := by
    rw [e] at h4
    simpa [k3] using h4
  have : μ = μ' := by rw [e, hc, one_smul]
  subst this
  exact h2.setIntegral_eq k2 fun γ g => hf γ γ.2 g

theorem integral_aut {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    [LocallyCompactSpace G] [SecondCountableTopology G] (Γ : Subgroup G) [Countable Γ] {μ : Measure G} {𝓕 : Set G}
    (h1 : μ.IsHaarMeasure) (h2 : IsFundamentalDomain Γ 𝓕 μ) (h3 : μ 𝓕 = 1) (c : G ≃ₜ* G) (hc : ∀ n, c n ∈ Γ ↔ n ∈ Γ)
    (f : G → ℂ) (hf : ∀ γ ∈ Γ, ∀ n, f (γ * n) = f n) : ∫ n in 𝓕, f (c n) ∂μ = ∫ n in 𝓕, f n ∂μ := by
  let m : G ≃ᵐ G := c.toHomeomorph.toMeasurableEquiv
  have k1 : (μ.map m).IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map μ c
  have hq : Measure.QuasiMeasurePreserving m.symm (μ.map m) μ :=
    ⟨m.symm.measurable, by rw [MeasurableEquiv.map_symm_map]⟩
  let e : Γ → Γ := fun γ => ⟨c.symm γ, (hc _).1 (by simpa using γ.2)⟩
  have he : Function.Bijective e := ⟨fun a b h => Subtype.ext (c.symm.injective (congrArg Subtype.val h)),
    fun b => ⟨⟨c b, (hc _).2 b.2⟩, Subtype.ext (by simp [e])⟩⟩
  have k2 : IsFundamentalDomain Γ (m.symm ⁻¹' 𝓕) (μ.map m) := by
    let e' := Equiv.ofBijective e he
    refine h2.preimage_of_equiv hq (e := e'.symm) e'.symm.bijective fun γ x => ?_
    obtain ⟨δ, rfl⟩ := e'.surjective γ
    rw [Equiv.symm_apply_apply]
    exact map_mul c.symm (δ : G) x
  have k3 : (μ.map m) (m.symm ⁻¹' 𝓕) = 1 := by
    rw [MeasurableEquiv.map_apply, ← h3]
    congr 1
    ext x; simp
  rw [integral_unit Γ h1 h2 h3 k1 k2 k3 f hf, MeasurableEquiv.restrict_map, integral_map_equiv]
  have : m ⁻¹' (m.symm ⁻¹' 𝓕) = 𝓕 := by ext x; simp
  rw [this]
  rfl

theorem isClosed_NFlag (B : HSp D) {ρ : ℕ} {e : Matrix (Fin B.rank) (Fin ρ) D.host.E} (he : IsIsoSub B e) :
    IsClosed (NFlag B e : Set (GA D B)) := by
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B
  obtain ⟨K, hK, h⟩ := (GlobalTheory.T.isotropic_unipotentRadicals_rational_cocompact D B ρ e he).1
  haveI : DiscreteTopology (GQ B ⊓ NFlag B e : Subgroup (GA D B)) :=
    DiscreteTopology.of_subset (s := (GQ B : Set (GA D B))) i6 (fun x hx => hx.1)
  have h1 : IsClosed ((GQ B ⊓ NFlag B e : Subgroup (GA D B)) : Set (GA D B)) := Subgroup.isClosed_of_discrete
  have h2 := h1.mul_right_of_isCompact (hK.image continuous_subtype_val)
  convert h2 using 1
  ext x
  constructor
  · intro hx
    obtain ⟨γ, hγ, k, hk, e⟩ := h ⟨x, hx⟩
    exact ⟨γ, ⟨hγ, γ.2⟩, k, ⟨k, hk, rfl⟩, (congrArg Subtype.val e).symm⟩
  · rintro ⟨γ, hγ, _, ⟨k, -, rfl⟩, rfl⟩
    exact mul_mem hγ.2 k.2

theorem top_NFlag (B : HSp D) {ρ : ℕ} {e : Matrix (Fin B.rank) (Fin ρ) D.host.E} (he : IsIsoSub B e) :
    LocallyCompactSpace (NFlag B e) ∧ SecondCountableTopology (NFlag B e) ∧ BorelSpace (NFlag B e) ∧
      Countable (NFlagQ B e) := by
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B
  refine ⟨(isClosed_NFlag B he).locallyCompactSpace,
    (inferInstance : SecondCountableTopology (NFlag B e : Set (GA D B))), inferInstance, ?_⟩
  exact Function.Injective.countable (f := fun γ : NFlagQ B e => (⟨γ.1.1, γ.2⟩ : GQ B))
    fun a b h => Subtype.ext (Subtype.ext (congrArg (fun x : GQ B => (x : GA D B)) h))

def coef (ψ : AddChar (AF D.host.F) ℂ) {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V} (d : BesDat A B ι)
    (ν : Measure (NFlag B d.e)) (𝓝 : Set (NFlag B d.e)) (F : GA D B → ℂ) (g : GA D B) : ℂ :=
  ∫ n in 𝓝, F ((n : GA D B) * g) * star (besChar ψ d (n : GA D B)) ∂ν

section Bessel

variable {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V}
  (hι : HSpace.IsIsomEmb A B ι) (d : BesDat A B ι)

include hψ hι

theorem inv_integrand {F : GA D B → ℂ} (hF : ∀ γ ∈ GQ B, ∀ g, F (γ * g) = F g) (g : GA D B) :
    ∀ γ ∈ NFlagQ B d.e, ∀ n : NFlag B d.e,
      F (((γ * n : NFlag B d.e) : GA D B) * g) * star (besChar ψ d ((γ * n : NFlag B d.e) : GA D B)) =
        F ((n : GA D B) * g) * star (besChar ψ d (n : GA D B)) := fun γ hγ n => by
  obtain ⟨h1, h2, -, -⟩ := GlobalTheory.T.besselCharacter_generic_character_laws D ψ hψ A B ι hι d
  rw [h1, h2 γ hγ, one_mul, Subgroup.coe_mul, mul_assoc, hF (γ : GA D B) hγ]

theorem coef_eq {ν ν' 𝓝 𝓝'} (h1 : ν.IsHaarMeasure) (h2 : IsFundamentalDomain (NFlagQ B d.e) 𝓝 ν) (h3 : ν 𝓝 = 1)
    (k1 : ν'.IsHaarMeasure) (k2 : IsFundamentalDomain (NFlagQ B d.e) 𝓝' ν') (k3 : ν' 𝓝' = 1)
    {F : GA D B → ℂ} (hF : ∀ γ ∈ GQ B, ∀ g, F (γ * g) = F g) (g : GA D B) :
    coef ψ d ν 𝓝 F g = coef ψ d ν' 𝓝' F g := by
  obtain ⟨-, -, -, -, i5, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B
  obtain ⟨j1, j2, j3, j4⟩ := top_NFlag B d.e_iso
  exact integral_unit _ h1 h2 h3 k1 k2 k3 _ (inv_integrand hψ hι d hF g)

theorem coef_left {ν 𝓝} (h1 : ν.IsHaarMeasure) (h2 : IsFundamentalDomain (NFlagQ B d.e) 𝓝 ν) (h3 : ν 𝓝 = 1)
    {F : GA D B → ℂ} (hF : ∀ γ ∈ GQ B, ∀ g, F (γ * g) = F g) {δ : GA D B} (hδ : δ ∈ GQ B) {γ γ' : GA D A}
    (e1 : EmbRel B A ι δ γ) (e2 : EmbRel B A ι δ⁻¹ γ') (g : GA D B) :
    coef ψ d ν 𝓝 F (δ * g) = coef ψ d ν 𝓝 F g := by
  obtain ⟨-, -, -, -, i5, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B
  obtain ⟨j1, j2, j3, j4⟩ := top_NFlag B d.e_iso
  obtain ⟨-, -, -, h4⟩ := GlobalTheory.T.besselCharacter_generic_character_laws D ψ hψ A B ι hι d
  let c : NFlag B d.e ≃ₜ* NFlag B d.e :=
    { toFun := fun n => ⟨δ⁻¹ * n * δ⁻¹⁻¹, (h4 _ _ e2 n n.2).1⟩
      invFun := fun n => ⟨δ * n * δ⁻¹, (h4 _ _ e1 n n.2).1⟩
      left_inv := fun n => Subtype.ext (by simp [mul_assoc])
      right_inv := fun n => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc])
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  have hc : ∀ n, c n ∈ NFlagQ B d.e ↔ n ∈ NFlagQ B d.e := fun n => by
    change δ⁻¹ * (n : GA D B) * δ⁻¹⁻¹ ∈ GQ B ↔ (n : GA D B) ∈ GQ B
    rw [inv_inv, Subgroup.mul_mem_cancel_right _ hδ, Subgroup.mul_mem_cancel_left _ (inv_mem hδ)]
  unfold coef
  refine Eq.trans ?_ (integral_aut _ h1 h2 h3 c hc _ (inv_integrand hψ hι d hF g))
  congr 1
  funext n
  change _ = F (δ⁻¹ * (n : GA D B) * δ⁻¹⁻¹ * g) * star (besChar ψ d (δ⁻¹ * (n : GA D B) * δ⁻¹⁻¹))
  rw [(h4 _ _ e2 n n.2).2, inv_inv, mul_assoc, mul_assoc, hF _ (inv_mem hδ)]

end Bessel

theorem exists_bes (hB : BesInt D) (hθ : IsInfFam θ) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1))
    {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V} (d : BesDat A B ι) :
    ∃ b : AFs θ A →ₗ⋆[ℂ] CuspS θ B →ₗ[ℂ] ℂ, A.SigOK → HSpace.IsIsomEmb A B ι → ∀ μ 𝓕, IsVolPair D A μ 𝓕 →
      ∀ s : GA D A → GA D B, (∀ h, EmbRel B A ι (s h) h) → ∀ (φ : AFs θ A) (F : CuspS θ B),
        IsAniso A ∨ φ.1 ∈ CuspS θ A → GlobalTheory.BesselCompare.ClauseFlag ψ d μ 𝓕 s φ.1 F.1 1 (b φ F) := by
  by_cases hι : HSpace.IsIsomEmb A B ι
  swap
  · exact ⟨0, fun _ h => absurd h hι⟩
  by_cases hN : ∃ (ν : Measure (NFlag B d.e)) (𝓝 : Set (NFlag B d.e)), ν.IsHaarMeasure ∧
    IsFundamentalDomain (NFlagQ B d.e) 𝓝 ν ∧ ν 𝓝 = 1
  swap
  · exact ⟨0, fun _ _ _ _ _ _ _ _ _ _ ν 𝓝 h1 h2 h3 => absurd ⟨ν, 𝓝, h1, h2, h3⟩ hN⟩
  obtain ⟨ν, 𝓝, h1, h2, h3⟩ := hN
  obtain ⟨s, -, hs, hq⟩ := GlobalTheory.T.exists_continuous_adelicUnitaryEmbedding D B A ι hι
  have k := fun (φ : CuspS θ A) (F : CuspS θ B) => hB θ hθ ψ hψ A B ι hι d _ _ (quot_mu A) ν 𝓝 h1 h2 s
    (fun h => (hs h _).2 rfl) φ.1 F.1 (cuspF hθ φ).1 (cuspF hθ F) (Or.inr (cuspF hθ φ).2)
  let b : CuspS θ A →ₗ⋆[ℂ] CuspS θ B →ₗ[ℂ] ℂ := LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ)
    (fun φ F => ∫ h in dom A, ∫ n in 𝓝, star (φ.1 h) * F.1 ((n : GA D B) * s h * (d.y : GA D B)) *
      star (besChar ψ d (n : GA D B)) ∂ν ∂(mu A))
    (fun φ φ' F => by
      rw [← integral_add (k φ F).2 (k φ' F).2]
      congr 1
      funext h
      rw [← integral_add ((k φ F).1 h) ((k φ' F).1 h)]
      simp [add_mul])
    (fun c φ F => by
      simp only [← integral_smul]
      simp [mul_assoc])
    (fun φ F F' => by
      rw [← integral_add (k φ F).2 (k φ F').2]
      congr 1
      funext h
      rw [← integral_add ((k φ F).1 h) ((k φ F').1 h)]
      simp [add_mul, mul_add])
    (fun c φ F => by
      simp only [← integral_smul]
      refine integral_congr_ae (.of_forall fun h => integral_congr_ae (.of_forall fun n => ?_))
      simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
      ring)
  obtain ⟨p, hp⟩ := (Submodule.inclusion (CuspS_le θ A)).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.2 (Submodule.inclusion_injective _))
  refine ⟨b.comp p, fun hA _ μ 𝓕 hμ s' hs' φ F hφ ν' 𝓝' k1 k2 k3 => ?_⟩
  obtain rfl : s' = s := funext fun h => (hs h _).1 (hs' h)
  have hφ' : φ.1 ∈ CuspS θ A := hφ.elim (fun h => by rw [CuspS_eq_of_aniso θ h]; exact φ.2) id
  have e : p φ = ⟨φ.1, hφ'⟩ := LinearMap.congr_fun hp ⟨φ.1, hφ'⟩
  have hF := (cuspF hθ F).1.left
  have f1 : ∀ (ν : Measure (NFlag B d.e)) 𝓝 h, ∫ n in 𝓝, star (φ.1 h) * F.1 ((n : GA D B) * s h * (d.y : GA D B)) *
      star (besChar ψ d (n : GA D B)) ∂ν = star (φ.1 h) * coef ψ d ν 𝓝 F.1 (s h * d.y) := fun ν 𝓝 h => by
    simp only [coef, mul_assoc, integral_const_mul]
  rw [LinearMap.comp_apply, e, one_mul]
  change ∫ h in dom A, ∫ n in 𝓝, star (φ.1 h) * F.1 ((n : GA D B) * s h * (d.y : GA D B)) *
      star (besChar ψ d (n : GA D B)) ∂ν ∂(mu A) = _
  simp only [f1]
  simp only [← coef_eq hψ hι d h1 h2 h3 k1 k2 k3 hF]
  refine integral_mu hA hμ (fun h => star (φ.1 h) * coef ψ d ν 𝓝 F.1 (s h * d.y)) fun γ hγ g => ?_
  rw [(aut hθ φ).left _ hγ, map_mul, mul_assoc,
    coef_left hψ hι d h1 h2 h3 hF (hq γ hγ) ((hs γ _).2 rfl) ((hs γ⁻¹ _).2 (map_inv s γ).symm)]

end GlobalTheory.Mem.TrueRecord

end
