import Formalism.WachLatticeTwists.CharacterSplitJumps.Statement
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.JT
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open ReciprocityTheory.ChartRestriction.T2 (GK PadicCoeff FracTop IsCyc IsCycOn)

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology

def lcH1 {O Γ M : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [AddCommGroup M] [Module O M]
    (ρ : Representation O Γ M) : Submodule O (H1z ρ) :=
  Submodule.map (Submodule.mkQ _)
    { carrier := {c : coZ1s ρ | IsLocallyConstant (c : Γ → M)}
      add_mem' := fun {_ _} ha hb => IsLocallyConstant.add ha hb
      zero_mem' := IsLocallyConstant.const 0
      smul_mem' := fun c _ hx => IsLocallyConstant.comp hx (fun m => c • m) }

def StatShapeRow : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
    (A T' G : Type) [Ring A] [Algebra O A] [CommRing T'] [Algebra T' A] [Group G]
    (M : Type) [AddCommGroup M] [Module A M] [Module O M] [SMulCommClass A O M]
    (r : G →* A) (χ : G →* T'ˣ) (Dw : Subgroup G) [TopologicalSpace Dw] (ε : G →* Oˣ) (e : ℕ),
    FiniteDimensional ℚ_[p] K → PadicCoeff p O → FracTop O → ∀ i : Dw ≃ₜ* GK p K,
    IsCyc p K ((ε.comp Dw.subtype).comp i.symm.toMulEquiv.toMonoidHom) → Nonempty (M ≃ₗ[O] KO O) →
    (∀ g ∈ Dw, ∀ m : M, uElt r χ g • m = ((((ε g) ^ e)⁻¹ : Oˣ) : O) • m) →
    (0 < e → QuotShape (lcH1 (resRep (uRep O (M := M) r χ) Dw)) ⊥ (Module.finrank ℚ_[p] K)) ∧
    (e = 0 → ∀ I : Subgroup Dw, (∀ g, g ∈ I ↔ i g ∈ Formalism.GaloisCohomology.inertiaK p K) →
      QuotShape (lcH1 (resRep (uRep O (M := M) r χ) Dw)) (unrH1 (resRep (uRep O (M := M) r χ) Dw) I)
        (Module.finrank ℚ_[p] K))

def StatShapeDec : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra ℤ_[p] O] [Module.Finite ℤ_[p] O], Function.Injective (algebraMap ℤ_[p] O) →
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (Aw : ValuationSubring Ω), Aw.valuation (p : Ω) < 1 →
    ∀ v : HeightOneSpectrum (𝓞 E), IsPlaceOver Aw v →
    ∀ (A T' : Type) [Ring A] [Algebra O A] [CommRing T'] [Algebra T' A]
    (M : Type) [AddCommGroup M] [Module A M] [Module O M] [SMulCommClass A O M]
    (r : (Ω ≃ₐ[E] Ω) →* A) (χ : (Ω ≃ₐ[E] Ω) →* T'ˣ) (ε : (Ω ≃ₐ[E] Ω) →* Oˣ) (e : ℕ),
    IsCycOn p (Aw.decompositionSubgroup E) (ε.comp (Aw.decompositionSubgroup E).subtype) →
    Nonempty (M ≃ₗ[O] KO O) →
    (∀ g ∈ Aw.decompositionSubgroup E, ∀ m : M, uElt r χ g • m = ((((ε g) ^ e)⁻¹ : Oˣ) : O) • m) →
    (0 < e → QuotShape (lcH1 (resRep (uRep O (M := M) r χ) (Aw.decompositionSubgroup E))) ⊥ (locDeg v)) ∧
    (e = 0 → QuotShape (lcH1 (resRep (uRep O (M := M) r χ) (Aw.decompositionSubgroup E)))
      (unrH1 (resRep (uRep O (M := M) r χ) (Aw.decompositionSubgroup E))
        ((Ine (F := E) Aw).subgroupOf (Aw.decompositionSubgroup E))) (locDeg v))

def StatTB2Dec : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra ℤ_[p] O] [Module.Finite ℤ_[p] O], Function.Injective (algebraMap ℤ_[p] O) →
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (Aw : ValuationSubring Ω), Aw.valuation (p : Ω) < 1 →
    ∀ v : HeightOneSpectrum (𝓞 E), IsPlaceOver Aw v →
    ∀ (A T' : Type) [Ring A] [Algebra O A] [CommRing T'] [Algebra T' A]
    (M : Type) [AddCommGroup M] [Module A M] [Module O M] [SMulCommClass A O M]
    (r : (Ω ≃ₐ[E] Ω) →* A) (χ : (Ω ≃ₐ[E] Ω) →* T'ˣ) (ε : (Ω ≃ₐ[E] Ω) →* Oˣ) (e : ℕ),
    IsCycOn p (Aw.decompositionSubgroup E) (ε.comp (Aw.decompositionSubgroup E).subtype) →
    Nonempty (M ≃ₗ[O] KO O) →
    (∀ g ∈ Aw.decompositionSubgroup E, ∀ m : M, uElt r χ g • m = ((((ε g) ^ e)⁻¹ : Oˣ) : O) • m) →
    ∀ F : Submodule O (H1z (resRep (uRep O (M := M) r χ) (Aw.decompositionSubgroup E))),
    (0 < e → F = ⊥) →
    (e = 0 → F = unrH1 (resRep (uRep O (M := M) r χ) (Aw.decompositionSubgroup E))
        ((Ine (F := E) Aw).subgroupOf (Aw.decompositionSubgroup E))) →
    ∀ ℓ c : ℕ,
    Module.length O
      (↥(lcH1 (resRep (uRep O (M := M) r χ) (Aw.decompositionSubgroup E)) ⊓ divBy F ((ℓ : O) ^ c)) ⧸
        F.comap (lcH1 (resRep (uRep O (M := M) r χ) (Aw.decompositionSubgroup E)) ⊓
          divBy F ((ℓ : O) ^ c)).subtype) ≤
      Module.length O (O ⧸ Ideal.span {(ℓ : O)}) * (c : ℕ∞) * ((locDeg v : ℕ∞) + 1)

end Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology
