import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfBoundedContinuousInvariant
import Development.AbelianVarietyTheory.Definitions.Foundations.IsRestrictedProdFinAwayIffIsProdMeasureFinAway
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsArchEquivEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteSeriesModelUnitaryIrreducibleOrthonormal
import Development.AbelianVarietyTheory.Proofs.HeightProofs.HilbertSchurUnitaryIrreducibleScalar
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotForallNonemptyLocP
import Development.AbelianVarietyTheory.Definitions.Foundations.ToContinuousLinearMapMemHomIn
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset
import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Mult MeasureTheory IsDedekindDomain
open NumberField Filter GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.AdelicU GlobalTheory.Cusp GlobalTheory.Mem.Th
open Formalism.MainNotions.KudlaSiegelWeil (Restr)
open GlobalTheory.PRep (smoothPart smoothRep IsSmooth IsAdmissible fixed)
open GlobalTheory.Orb (dsRep TypeDataG)
open scoped TensorProduct ComplexConjugate InnerProductSpace

namespace GlobalTheory.AutMult

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (V : HSp D) {H X W : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup X]
  [InnerProductSpace ℂ X] [AddCommGroup W] [Module ℂ W] {S : D.what₂.Tau → SPar}

section Types

variable {Y Z : Type} [AddCommGroup Y] [Module ℂ Y] [AddCommGroup Z] [Module ℂ Z]
  {v : HeightOneSpectrum (𝓞 D.host.F)}

variable {V}

def LocContains (τ : Representation ℂ (Kv V v) Z) (σv : Representation ℂ (Gv V v) Y) : Prop :=
  Contains τ (σv.comp (Kv V v).subtype)

def ContainsAt (τ : Representation ℂ (Kv V v) Z) (σ : Representation ℂ (GfC V) W) : Prop :=
  LocContains τ (σ.comp (locFin V v))

def ContainsTypes (T : TypeDataG V) (σ : Representation ℂ (GfC V) W) : Prop :=
  ∀ v : T.S, ContainsAt ((T.τ v).comp (T.frame v).red) σ

variable (v) in

def IsSphericalAt (σ : Representation ℂ (GfC V) W) : Prop := LGrp.IsSpherical (σ.comp (locFin V v)) (Kv V v)

def IsSphericalOff (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (σ : Representation ℂ (GfC V) W) : Prop :=
  ∀ v ∉ S, IsSphericalAt v σ

variable {σ : Representation ℂ (GfC V) W} {σv : Representation ℂ (Gv V v) Y} {τ : Representation ℂ (Kv V v) Z}

theorem isSphericalOff_of_fixed {S : Finset (HeightOneSpectrum (𝓞 D.host.F))} (h : LGrp.IsSpherical σ (KOff V S)) :
    IsSphericalOff S σ := fun _ hv =>
  let ⟨x, hx, h0⟩ := (Submodule.ne_bot_iff _).1 h
  (Submodule.ne_bot_iff _).2 ⟨x, LGrp.mem_fixed.2 fun _ hk => LGrp.mem_fixed.1 hx _ (emb_mem_levelOff hv hk), h0⟩

end Types

section Mult

variable (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]

def mDisc (π : GA D V →* (H →L[ℂ] H)) : Cardinal := multIn π (RG V μ) (L2discG V μ)

def mCusp (π : GA D V →* (H →L[ℂ] H)) : Cardinal := multIn π (RG V μ) (L2cusp V μ)

abbrev cuspHom (π : GA D V →* (H →L[ℂ] H)) : Submodule ℂ (H →L[ℂ] DividedPowerChartLift V μ) := homIn π (RG V μ) (L2cusp V μ)

abbrev cuspIso (π : GA D V →* (H →L[ℂ] H)) : Submodule ℂ (DividedPowerChartLift V μ) := isoPart π (RG V μ) (L2cusp V μ)

def IsCuspidalRep (π : GA D V →* (H →L[ℂ] H)) : Prop := IsIrrUnitary π ∧ mCusp V μ π ≠ 0

def IsDiscreteRep (π : GA D V →* (H →L[ℂ] H)) : Prop := IsIrrUnitary π ∧ mDisc V μ π ≠ 0

def mDiscT (σ : Representation ℂ (GfC V) W) (δ : GinfC V →* (X →L[ℂ] X)) : Cardinal :=
  multTensor (GfC V).subtype (GinfC V).subtype σ δ (RG V μ) (L2discG V μ)

def mCuspT (σ : Representation ℂ (GfC V) W) (δ : GinfC V →* (X →L[ℂ] X)) : Cardinal :=
  multTensor (GfC V).subtype (GinfC V).subtype σ δ (RG V μ) (L2cusp V μ)

open Classical in

def mDiscPi {Hs : InfinitePlace D.host.F → Type} [∀ w, NormedAddCommGroup (Hs w)] [∀ w, InnerProductSpace ℂ (Hs w)]
    (σ : Representation ℂ (GfC V) W) (δs : ∀ w, Gw V w →* (Hs w →L[ℂ] Hs w)) : Cardinal :=
  multTensorPi (GfC V).subtype (embW V) σ δs (RG V μ) (L2discG V μ)

open Classical in

def mCuspPi {Hs : InfinitePlace D.host.F → Type} [∀ w, NormedAddCommGroup (Hs w)] [∀ w, InnerProductSpace ℂ (Hs w)]
    (σ : Representation ℂ (GfC V) W) (δs : ∀ w, Gw V w →* (Hs w →L[ℂ] Hs w)) : Cardinal :=
  multTensorPi (GfC V).subtype (embW V) σ δs (RG V μ) (L2cusp V μ)

variable {V}

def mDiscDS (σ : Representation ℂ (GfC V) W) (M : DSModel V S) : Cardinal :=
  Module.rank ℂ (homFinDS σ M (RG V μ) (L2discG V μ))

def mCuspDS (σ : Representation ℂ (GfC V) W) (M : DSModel V S) : Cardinal :=
  Module.rank ℂ (homFinDS σ M (RG V μ) (L2cusp V μ))

variable {μ} {π : GA D V →* (H →L[ℂ] H)} {π' : GA D V →* (X →L[ℂ] X)} {σ : Representation ℂ (GfC V) W}
  {δ : GinfC V →* (X →L[ℂ] X)} {M : DSModel V S}

theorem mCusp_eq_Rcusp : mCusp V μ π = multIn π (Rcusp V μ) ⊤ := (multIn_rep (isSubrep_L2cusp V μ)).symm

theorem mDisc_eq_top (hπ : IsIrrUnitary π) : mDisc V μ π = multIn π (RG V μ) ⊤ :=
  congrArg (fun U : Submodule ℂ _ => Module.rank ℂ U) (homIn_disc hπ (isUnitaryRep_RG V μ))

open Classical in

theorem mDS_congr {W' : Type} [AddCommGroup W'] [Module ℂ W'] {σ' : Representation ℂ (GfC V) W'} (e : σ.Equiv σ') :
    mDiscDS μ σ M = mDiscDS μ σ' M ∧ mCuspDS μ σ M = mCuspDS μ σ' M := ⟨multTensorPi_congr e, multTensorPi_congr e⟩

end Mult

section Forms

variable (θ : InfF D) (A : CptF V) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]

def finVec (π : GA D V →* (H →L[ℂ] H)) : Submodule ℂ H := kFinVec (toRep π) (Kinf θ V A) ⊓ smoothPart (finRes π)

omit [μ.IsMulRightInvariant] in
variable {V μ} in

theorem lift_add_ae {F F' : DividedPowerChartLift V μ} {φ ψ : GA D V → ℂ} (e : lift (GQ V) F =ᵐ[μ] φ) (e' : lift (GQ V) F' =ᵐ[μ] ψ) :
    lift (GQ V) (F + F' : DividedPowerChartLift V μ) =ᵐ[μ] φ + ψ :=
  EventuallyEq.trans (ae_quotMeasure_iff.1 (Lp.coeFn_add F F')) (e.add e')

omit [μ.IsMulRightInvariant] in
variable {V μ} in

theorem lift_smul_ae (c : ℂ) {F : DividedPowerChartLift V μ} {φ : GA D V → ℂ} (e : lift (GQ V) F =ᵐ[μ] φ) :
    lift (GQ V) (c • F : DividedPowerChartLift V μ) =ᵐ[μ] c • φ :=
  EventuallyEq.trans (ae_quotMeasure_iff.1 (Lp.coeFn_smul c F)) (e.const_smul c)

omit [μ.IsMulRightInvariant] in

def formsIn (𝒜 : Submodule ℂ (GA D V → ℂ)) (U : Submodule ℂ (DividedPowerChartLift V μ)) : Submodule ℂ (GA D V → ℂ) where
  carrier := {φ | φ ∈ 𝒜 ∧ ∃ F ∈ U, lift (GQ V) F =ᵐ[μ] φ}
  zero_mem' := ⟨zero_mem _, 0, zero_mem _, ae_quotMeasure_iff.1 (Lp.coeFn_zero ℂ 2 _)⟩
  add_mem' := fun ⟨h, F, hF, e⟩ ⟨h', F', hF', e'⟩ => ⟨add_mem h h', _, add_mem hF hF', lift_add_ae e e'⟩
  smul_mem' := fun c _ ⟨h, F, hF, e⟩ => ⟨𝒜.smul_mem c h, _, U.smul_mem c hF, lift_smul_ae c e⟩

abbrev CuspIsotypicForms (π : GA D V →* (H →L[ℂ] H)) : Submodule ℂ (GA D V → ℂ) := formsIn V μ (A0 θ V A) (cuspIso V μ π)

def formHom (π : GA D V →* (H →L[ℂ] H)) : Submodule ℂ (finVec V θ A π →ₗ[ℂ] (GA D V → ℂ)) where
  carrier := {ι | (∀ x, ι x ∈ A0 θ V A) ∧ ∃ T ∈ cuspHom V μ π, ∀ x : finVec V θ A π, lift (GQ V) (T x) =ᵐ[μ] ι x}
  zero_mem' := ⟨fun _ => zero_mem _, 0, zero_mem _, fun _ => ae_quotMeasure_iff.1 (Lp.coeFn_zero ℂ 2 _)⟩
  add_mem' := by
    rintro ι ι' ⟨h, T, hT, e⟩ ⟨h', T', hT', e'⟩
    refine ⟨fun x => (A0 θ V A).add_mem (h x) (h' x), T + T', (cuspHom V μ π).add_mem hT hT', fun x => ?_⟩
    rw [add_apply, LinearMap.add_apply]
    exact lift_add_ae (e x) (e' x)
  smul_mem' := by
    rintro c ι ⟨h, T, hT, e⟩
    refine ⟨fun x => (A0 θ V A).smul_mem c (h x), c • T, (cuspHom V μ π).smul_mem c hT, fun x => ?_⟩
    rw [smul_apply, LinearMap.smul_apply]
    exact lift_smul_ae c (e x)

variable {V}

omit [μ.IsHaarMeasure] [μ.IsMulRightInvariant] in

def beF (ι ι' : X →ₗ[ℂ] (GA D V → ℂ)) : ℂ := petersson V μ (ι (unitVec X)) (ι' (unitVec X))

variable {θ A μ} {π : GA D V →* (H →L[ℂ] H)} {φ ψ : GA D V → ℂ}

omit [μ.IsMulRightInvariant] in

theorem exists_toL2_eq_of_ae_eq {F : DividedPowerChartLift V μ} (hφ : LeftInv (GQ V) φ) (e : lift (GQ V) F =ᵐ[μ] φ) :
    ∃ h : MemL2Quotient (GQ V) μ φ, h.toL2 = F :=
  have hd := isFundamentalDomain_stdDom (GQ V) μ
  have h : MemL2Quotient (GQ V) μ φ := (memL2_iff_fundamental_domain hd).2 ⟨hφ, ((memL2_iff_fundamental_domain hd).1 (memL2_lift F)).2.ae_eq (ae_restrict_of_ae e)⟩
  ⟨h, l2DiscreteQuotient_ext_iff_lift_ae_eq.2 (h.lift_toL2_ae_eq.trans e.symm)⟩

omit [μ.IsMulRightInvariant] in

theorem petersson_eq_inner {F F' : DividedPowerChartLift V μ} (hφ : LeftInv (GQ V) φ) (hψ : LeftInv (GQ V) ψ) (e : lift (GQ V) F =ᵐ[μ] φ)
    (e' : lift (GQ V) F' =ᵐ[μ] ψ) : petersson V μ φ ψ = ⟪F', F⟫_ℂ := by
  obtain ⟨h, rfl⟩ := exists_toL2_eq_of_ae_eq hφ e
  obtain ⟨h', rfl⟩ := exists_toL2_eq_of_ae_eq hψ e'
  exact (h.inner_toL2_eq_theta_pairing h').symm

theorem petersson_rTr_eq_be (hπ : IsIrrUnitary π) {U U' : Submodule ℂ (DividedPowerChartLift V μ)} {T T' : H →L[ℂ] DividedPowerChartLift V μ}
    (hT : T ∈ homIn π (RG V μ) U) (hT' : T' ∈ homIn π (RG V μ) U') {x y : H} (hφ : LeftInv (GQ V) φ)
    (hψ : LeftInv (GQ V) ψ) (e : lift (GQ V) (T x) =ᵐ[μ] φ) (e' : lift (GQ V) (T' y) =ᵐ[μ] ψ) (g : GA D V) :
    petersson V μ (rTr V g φ) ψ = be T T' * ⟪y, π g x⟫_ℂ :=
  (petersson_eq_inner (hφ.mul_right g) hψ ((lift_R g _).trans
    ((measurePreserving_mul_right μ g).quasiMeasurePreserving.ae e)) e').trans
      (inner_apply_eq_be hπ (isUnitaryRep_RG V μ) hT hT' g x y)

variable {ι ι' : finVec V θ A π →ₗ[ℂ] (GA D V → ℂ)}

theorem petersson_rTr_eq_beF (hπ : IsIrrUnitary π) (h : ι ∈ formHom V θ A μ π) (h' : ι' ∈ formHom V θ A μ π)
    (g : GA D V) (x y : finVec V θ A π) : petersson V μ (rTr V g (ι x)) (ι' y) = beF μ ι ι' * ⟪(y : H), π g x⟫_ℂ := by
  obtain ⟨h, T, hT, e⟩ := h
  obtain ⟨h', T', hT', e'⟩ := h'
  rw [petersson_rTr_eq_be hπ hT hT' (h x).2.2.1 (h' y).2.2.1 (e x) (e' y)]
  rcases subsingleton_or_nontrivial (finVec V θ A π) with h0 | h0
  · simp [Subsingleton.elim y 0]
  · rw [beF, petersson_eq_inner (h _).2.2.1 (h' _).2.2.1 (e _) (e' _), inner_eq_be hπ (isUnitaryRep_RG V μ) hT hT',
      ← Submodule.coe_inner, inner_self_eq_norm_sq_to_K, norm_unitVec]
    simp

theorem petersson_eq_beF (hπ : IsIrrUnitary π) (h : ι ∈ formHom V θ A μ π) (h' : ι' ∈ formHom V θ A μ π)
    (x y : finVec V θ A π) : petersson V μ (ι x) (ι' y) = beF μ ι ι' * ⟪y, x⟫_ℂ := by
  have e : rTr V 1 (ι x) = ι x := funext fun g => congrArg (ι x) (mul_one g)
  simpa only [e, map_one, one_apply_eq_self, Submodule.coe_inner] using petersson_rTr_eq_beF hπ h h' 1 x y

omit [μ.IsHaarMeasure] [μ.IsMulRightInvariant] in

theorem beF_smul_left (c : ℂ) (ι ι' : X →ₗ[ℂ] (GA D V → ℂ)) : beF μ (c • ι) ι' = c * beF μ ι ι' :=
  petersson_smul_left c _ _

end Forms

section Examples

variable (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]

theorem multIn_one_ne_zero {U : Submodule ℂ (DividedPowerChartLift V μ)} (h : (memL2_const (Γ := GQ V) (μ := μ) 1).toL2 ∈ U) :
    multIn (charRep (1 : GA D V →* Circle)) (RG V μ) U ≠ 0 := fun e => by
  have h1 : ContinuousLinearMap.toSpanSingleton ℂ (memL2_const (Γ := GQ V) (μ := μ) 1).toL2 ∈
      homIn (charRep (1 : GA D V →* Circle)) (RG V μ) U :=
    ⟨fun c => U.smul_mem c h, fun g c => by simp [charRep, right_translate_toL2]⟩
  rw [multIn_eq_zero_iff.1 e, Submodule.mem_bot] at h1
  exact (isIrredSubrep_const (Γ := GQ V) (μ := μ)).2.1 (Submodule.span_singleton_eq_bot.2
    ((one_smul ℂ _).symm.trans (DFunLike.congr_fun h1 1)))

theorem isDiscreteRep_one : IsDiscreteRep V μ (charRep 1) :=
  ⟨isIrrUnitary_charRep continuous_const,
    multIn_one_ne_zero V μ (isIrredSubrep_const.le_disc (Submodule.mem_span_singleton_self _))⟩

example (v : Formalism.MainNotions.SchurIrreducible.Pl D.host.F) :
    HasCompPl D.sp.cm.sig V.gram v (charRep 1) (charRep (1 : GA D V →* Circle)) :=
  IsFactorisation.hasCompPl (δ := fun _ => charRep 1)
    (isRestrTensor_charRep (projPl _ _) (fun _ => 1) 1 (fun _ => .of_forall fun _ => rfl) fun _ => by simp) v

example : IsSphericalOff ∅ (Representation.trivial ℂ (GfC V) ℂ) :=
  isSphericalOff_of_fixed ((Submodule.ne_bot_iff _).2 ⟨1, LGrp.mem_fixed.2 fun _ _ => rfl, one_ne_zero⟩)

example {v : HeightOneSpectrum (𝓞 D.host.F)} (τ : Representation ℂ (Kv V v) W) (hτ : τ.IsIrreducible)
    (h : 1 < Module.rank ℂ W) : ¬ ContainsAt τ (Representation.trivial ℂ (GfC V) ℂ) := fun hc => by
  obtain ⟨f, h0, e⟩ := contains_iff.1 hc
  have := LinearMap.rank_le_of_injective f (injective_of_mem_homInto (C := ⊤) hτ ⟨fun _ => trivial, e⟩ h0)
  exact h.not_ge (by simpa using this)

end Examples

end GlobalTheory.AutMult

end
