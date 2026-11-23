import Mathlib
import GroundTheory.AutomorphicForms.AdelicGLn
import GroundTheory.AutomorphicForms.Satake
import GroundTheory.AutomorphicForms.TensorProductTheorem.Existence
import GroundTheory.AutomorphicForms.TensorProductTheorem.Uniqueness

noncomputable section

universe u

namespace GroundTheory.Automorphic

open Filter Function Module Set NumberField IsDedekindDomain

open scoped _root_.RestrictedProduct

namespace RestrictedTensor

section Transport

variable {G₁ G₂ : Type*} [Group G₁] [Group G₂] [TopologicalSpace G₁] [TopologicalSpace G₂]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G₂ V}

theorem isSmooth_comp (hρ : IsSmooth ρ) {f : G₁ →* G₂} (hf : Continuous f) :
    IsSmooth (ρ.comp f) := fun v => (hρ v).preimage hf

theorem isAdmissible_comp (hρ : IsAdmissible ρ) (e : G₁ ≃ₜ* G₂) :
    IsAdmissible (ρ.comp e.toMulEquiv.toMonoidHom) := by
  refine ⟨isSmooth_comp hρ.1 e.continuous, fun K₁ hK₁c hK₁o => ?_⟩
  have hc : IsCompact ((K₁.map e.toMulEquiv.toMonoidHom : Subgroup G₂) : Set G₂) := by
    rw [Subgroup.coe_map]
    exact hK₁c.image e.continuous
  have ho : IsOpen ((K₁.map e.toMulEquiv.toMonoidHom : Subgroup G₂) : Set G₂) := by
    rw [Subgroup.coe_map]
    exact e.toHomeomorph.isOpenMap _ hK₁o
  have := hρ.2 _ hc ho
  have heq : fixedVectors (ρ.comp e.toMulEquiv.toMonoidHom) K₁ =
      fixedVectors ρ (K₁.map e.toMulEquiv.toMonoidHom) := by
    ext x
    simp only [mem_fixedVectors, Subgroup.mem_map, MonoidHom.coe_comp, Function.comp_apply]
    constructor
    · rintro h _ ⟨k, hk, rfl⟩
      exact h k hk
    · intro h k hk
      exact h _ ⟨k, hk, rfl⟩
  rw [heq]
  exact this

theorem isIrreducible_comp (hρ : ρ.IsIrreducible) {f : G₁ →* G₂} (hf : Function.Surjective f) :
    Representation.IsIrreducible (ρ.comp f) := by
  let e : Subrepresentation (ρ.comp f) ≃o Subrepresentation ρ :=
    { toFun := fun X => ⟨X.toSubmodule, fun g x hx => by
        obtain ⟨h, rfl⟩ := hf g
        exact X.apply_mem_toSubmodule h hx⟩
      invFun := fun Y => ⟨Y.toSubmodule, fun h x hx => Y.apply_mem_toSubmodule (f h) hx⟩
      left_inv := fun X => rfl
      right_inv := fun Y => rfl
      map_rel_iff' := Iff.rfl }
  exact (OrderIso.isSimpleOrder_iff e).2 hρ

variable {W : Type*} [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ G₂ W}

def equivComp (Φ : ρ.Equiv σ) (f : G₁ →* G₂) : Representation.Equiv (ρ.comp f) (σ.comp f) :=
  Representation.Equiv.mk Φ.toLinearEquiv fun g => LinearMap.ext fun x => by
    show Φ.toLinearEquiv (ρ (f g) x) = σ (f g) (Φ.toLinearEquiv x)
    exact Representation.IntertwiningMap.isIntertwining _ _ Φ.toIntertwiningMap (f g) x

def equivCompOfRightInverse {f : G₁ →* G₂} {g : G₂ →* G₁} (hfg : ∀ x, f (g x) = x) :
    ρ.Equiv ((ρ.comp f).comp g) :=
  Representation.Equiv.mk (LinearEquiv.refl ℂ V) fun x => LinearMap.ext fun y => by
    simp [hfg x]

end Transport

end RestrictedTensor

namespace AdelicGLn

open RestrictedTensor

variable (K : Type*) [Field K] [NumberField K] (n : ℕ)

theorem finrank_fixedVectors_integralGL_le_one {F : Type*} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] {W : Type*} [AddCommGroup W]
    [Module ℂ W] {σ : Representation ℂ (GL (Fin n) F) W} (hσ : IsSmooth σ)
    (hirr : σ.IsIrreducible) :
    Module.finrank ℂ (fixedVectors σ (GLnLocal.integralGL F n)) ≤ 1 := by
  by_cases h : fixedVectors σ (GLnLocal.integralGL F n) = ⊥
  · rw [h, finrank_bot]
    exact zero_le_one
  · haveI := hirr
    exact (Spherical.finrank_fixedVectors_eq_one hσ h).le

instance factIsOpenIntegralGL :
    Fact (∀ v : HeightOneSpectrum (𝓞 K),
      IsOpen (GLnLocal.integralGL (v.adicCompletion K) n : Set (GL (Fin n) (v.adicCompletion K)))) :=
  ⟨fun v => GLnLocal.isOpen_integralGL _ n⟩

instance compactSpaceIntegralGL (v : HeightOneSpectrum (𝓞 K)) :
    CompactSpace (GLnLocal.integralGL (v.adicCompletion K) n) :=
  isCompact_iff_compactSpace.1 (GLnLocal.isCompact_integralGL _ n)

abbrev toRestricted : FiniteAdelicGL K n →* (Πʳ v : HeightOneSpectrum (𝓞 K),
    [GL (Fin n) (v.adicCompletion K), GLnLocal.integralGL (v.adicCompletion K) n]) :=
  (finiteRestrictedEquiv K n).toMulEquiv.toMonoidHom

variable {K n}

def adelicTensorRep {W : HeightOneSpectrum (𝓞 K) → Type*} [∀ v, AddCommGroup (W v)]
    [∀ v, Module ℂ (W v)] (π : ∀ v, Representation ℂ (GL (Fin n) (v.adicCompletion K)) (W v))
    (ξ : ∀ v, W v)
    (hξ : ∀ᶠ v in cofinite, ξ v ∈ fixedVectors (π v) (GLnLocal.integralGL (v.adicCompletion K) n)) :
    Representation ℂ (FiniteAdelicGL K n) (restrictedTensor ξ) :=
  (restrictedTensorRep π ξ hξ).comp (toRestricted K n)

section Local

variable {W : HeightOneSpectrum (𝓞 K) → Type*} [∀ v, AddCommGroup (W v)] [∀ v, Module ℂ (W v)]
  {π : ∀ v, Representation ℂ (GL (Fin n) (v.adicCompletion K)) (W v)} {ξ : ∀ v, W v}

theorem isIrreducible_restrictedTensorRep (hπ : ∀ v, IsAdmissible (π v))
    (hirr : ∀ v, (π v).IsIrreducible)
    (hξ : ∀ᶠ v in cofinite, ξ v ∈ fixedVectors (π v) (GLnLocal.integralGL (v.adicCompletion K) n))
    (hξ0 : ∀ᶠ v in cofinite, ξ v ≠ 0) :
    (adelicTensorRep π ξ hξ).IsIrreducible := by
  refine isIrreducible_comp (RestrictedTensor.isIrreducible_restrictedTensorRep hπ hirr hξ hξ0 ?_)
    (fun y => ⟨(finiteRestrictedEquiv K n).symm y, (finiteRestrictedEquiv K n).apply_symm_apply y⟩)
  filter_upwards [hξ, hξ0] with v h1 h2 u hu
  have : FiniteDimensional ℂ (fixedVectors (π v) (GLnLocal.integralGL (v.adicCompletion K) n)) :=
    (hπ v).2 _ (GLnLocal.isCompact_integralGL _ n) (GLnLocal.isOpen_integralGL _ n)
  have hle := finrank_fixedVectors_integralGL_le_one n (hπ v).1 (hirr v)
  have hspan : Submodule.span ℂ {ξ v} =
      fixedVectors (π v) (GLnLocal.integralGL (v.adicCompletion K) n) :=
    Submodule.eq_of_le_of_finrank_le ((Submodule.span_singleton_le_iff_mem _ _).2 h1)
      (hle.trans (by rw [finrank_span_singleton h2]))
  rw [← hspan, Submodule.mem_span_singleton] at hu
  obtain ⟨c, rfl⟩ := hu
  exact ⟨c, rfl⟩

theorem isAdmissible_restrictedTensorRep (hπ : ∀ v, IsAdmissible (π v))
    (hirr : ∀ v, (π v).IsIrreducible)
    (hξ : ∀ᶠ v in cofinite, ξ v ∈ fixedVectors (π v) (GLnLocal.integralGL (v.adicCompletion K) n))
    (hξ0 : ∀ᶠ v in cofinite, ξ v ≠ 0) :
    IsAdmissible (adelicTensorRep π ξ hξ) := by
  refine isAdmissible_comp (RestrictedTensor.isAdmissible_restrictedTensorRep hπ hξ ?_)
    (finiteRestrictedEquiv K n)
  filter_upwards [hξ, hξ0] with v h1 h2 u hu
  have : FiniteDimensional ℂ (fixedVectors (π v) (GLnLocal.integralGL (v.adicCompletion K) n)) :=
    (hπ v).2 _ (GLnLocal.isCompact_integralGL _ n) (GLnLocal.isOpen_integralGL _ n)
  have hle := finrank_fixedVectors_integralGL_le_one n (hπ v).1 (hirr v)
  have hspan : Submodule.span ℂ {ξ v} =
      fixedVectors (π v) (GLnLocal.integralGL (v.adicCompletion K) n) :=
    Submodule.eq_of_le_of_finrank_le ((Submodule.span_singleton_le_iff_mem _ _).2 h1)
      (hle.trans (by rw [finrank_span_singleton h2]))
  rw [← hspan, Submodule.mem_span_singleton] at hu
  obtain ⟨c, rfl⟩ := hu
  exact ⟨c, rfl⟩

end Local

variable {V : Type u} [AddCommGroup V] [Module ℂ V]

variable (K n) in

structure TensorDecomposition (ρ : Representation ℂ (FiniteAdelicGL K n) V) where

  W : HeightOneSpectrum (𝓞 K) → Type u
  [instAddCommGroup : ∀ v, AddCommGroup (W v)]
  [instModule : ∀ v, Module ℂ (W v)]

  π : ∀ v, Representation ℂ (GL (Fin n) (v.adicCompletion K)) (W v)

  ξ : ∀ v, W v
  mem_fixedVectors : ∀ᶠ v in cofinite,
    ξ v ∈ fixedVectors (π v) (GLnLocal.integralGL (v.adicCompletion K) n)
  ne_zero : ∀ᶠ v in cofinite, ξ v ≠ 0
  isAdmissible : ∀ v, IsAdmissible (π v)
  isIrreducible : ∀ v, (π v).IsIrreducible

  equiv : ρ.Equiv (adelicTensorRep π ξ mem_fixedVectors)

attribute [instance] TensorDecomposition.instAddCommGroup TensorDecomposition.instModule

theorem nonempty_tensorDecomposition {ρ : Representation ℂ (FiniteAdelicGL K n) V}
    (hρ : IsAdmissible ρ) (hirr : ρ.IsIrreducible) : Nonempty (TensorDecomposition K n ρ) := by
  set e := finiteRestrictedEquiv K n
  have hρ' : IsAdmissible (ρ.comp e.symm.toMulEquiv.toMonoidHom) := isAdmissible_comp hρ e.symm
  have hirr' : Representation.IsIrreducible (ρ.comp e.symm.toMulEquiv.toMonoidHom) :=
    isIrreducible_comp hirr e.symm.surjective
  obtain ⟨W, i1, i2, π, ξ, hξ, hπ, hπirr, hξ0, ⟨Φ⟩⟩ :=
    RestrictedTensor.exists_equiv_restrictedTensorRep hρ' hirr'
      (Eventually.of_forall fun v W _ _ σ hσ hσirr =>
        finrank_fixedVectors_integralGL_le_one n hσ.1 hσirr)
  exact ⟨{
    W := W
    π := π
    ξ := ξ
    mem_fixedVectors := hξ
    ne_zero := hξ0
    isAdmissible := hπ
    isIrreducible := hπirr
    equiv := (equivCompOfRightInverse (f := e.symm.toMulEquiv.toMonoidHom)
      (g := e.toMulEquiv.toMonoidHom) (fun x => e.symm_apply_apply x)).trans
      (equivComp Φ e.toMulEquiv.toMonoidHom) }⟩

namespace TensorDecomposition

variable {ρ : Representation ℂ (FiniteAdelicGL K n) V}

theorem eventually_unramified (D : TensorDecomposition K n ρ) :
    ∀ᶠ v in cofinite, fixedVectors (D.π v) (GLnLocal.integralGL (v.adicCompletion K) n) ≠ ⊥ := by
  filter_upwards [D.mem_fixedVectors, D.ne_zero] with v h1 h2 h
  rw [h, Submodule.mem_bot] at h1
  exact h2 h1

theorem nonempty_equiv (D D' : TensorDecomposition K n ρ) (v : HeightOneSpectrum (𝓞 K)) :
    Nonempty ((D.π v).Equiv (D'.π v)) := by
  set e := finiteRestrictedEquiv K n
  have Ψ : (restrictedTensorRep D.π D.ξ D.mem_fixedVectors).Equiv
      (restrictedTensorRep D'.π D'.ξ D'.mem_fixedVectors) :=
    (equivCompOfRightInverse (ρ := restrictedTensorRep D.π D.ξ D.mem_fixedVectors)
      (f := e.toMulEquiv.toMonoidHom) (g := e.symm.toMulEquiv.toMonoidHom)
      (fun x => e.apply_symm_apply x)).trans
      ((equivComp (D.equiv.symm.trans D'.equiv) e.symm.toMulEquiv.toMonoidHom).trans
        (equivCompOfRightInverse (ρ := restrictedTensorRep D'.π D'.ξ D'.mem_fixedVectors)
          (f := e.toMulEquiv.toMonoidHom) (g := e.symm.toMulEquiv.toMonoidHom)
          (fun x => e.apply_symm_apply x)).symm)
  exact nonempty_equiv_of_restrictedTensorRep_equiv D.isIrreducible D'.isIrreducible
    D.mem_fixedVectors D'.mem_fixedVectors D.ne_zero D'.ne_zero Ψ v

end TensorDecomposition

end AdelicGLn

end GroundTheory.Automorphic
