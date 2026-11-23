import Formalism.WachLatticeTwists.CoprimeLiftBounds.StatBridgeChiOne
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs

open Formalism.NG
open Formalism.RepresentationBoundsCohomology.BR
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.T2

def StatVhE : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (Av : HeightOneSpectrum (𝓞 E) → ValuationSubring Ω), (∀ v, IsPlaceOver (Av v) v) →
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O]
      [Module.Finite ℤ_[l] O], (l ≠ 2 ∨ InfinitePlace.nrRealPlaces E = 0) →
    ∀ (M : Type) [AddCommGroup M] [Module O M], Nonempty (M ≃ₗ[O] KO O) →
    ∀ (ρ : Representation O (G E Ω) M), (∀ g m, ρ g m = m) →
    ∀ S : Submodule O (H1z ρ),
      (∀ x ∈ S, ∃ z : coZ1s ρ, Submodule.mkQ _ z = x ∧ IsLocallyConstant (z : G E Ω → M)) →
      (∀ v, S ≤ unrH1 ρ (Ine (F := E) (Av v))) →
      Module.length O S ≤ Module.length O (O ⧸ Ideal.span {(l : O)}) * (padicValNat l (classNumber E) : ℕ∞)

def StatVhEInChi : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (Av : HeightOneSpectrum (𝓞 E) → ValuationSubring Ω), (∀ v, IsPlaceOver (Av v) v) →
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O]
      [Module.Finite ℤ_[l] O], (l ≠ 2 ∨ InfinitePlace.nrRealPlaces E = 0) →
    ∀ (A T' : Type) [Ring A] [Algebra O A] [CommRing T'] [Algebra T' A]
      (M : Type) [AddCommGroup M] [Module A M] [Module O M] [SMulCommClass A O M],
      Nonempty (M ≃ₗ[O] KO O) →
    ∀ (r : G E Ω →* A) (χ : G E Ω →* T'ˣ), (∀ g (m : M), uElt r χ g • m = m) →
    ∀ (D : ℕ → Subgroup (G E Ω)) (places : Finset ℕ)
      (HcG : Submodule O (H1z (uRep O (M := M) r χ)))
      (F : ∀ w, Submodule O (H1z (resRep (uRep O (M := M) r χ) (D w))))
      (Vo VS : Type) (Io : Vo → Subgroup (G E Ω)) (IS : VS → Subgroup (G E Ω)),
      (∀ x ∈ HcG, ∃ z : coZ1s (uRep O (M := M) r χ), Submodule.mkQ _ z = x ∧
        IsLocallyConstant (z : G E Ω → M)) →
      (∀ v, (∃ a, Ine (F := E) (Av v) ≤ Io a) ∨ (∃ a, Ine (F := E) (Av v) ≤ IS a) ∨
        ∃ w ∈ places, ∃ I : Subgroup (D w), F w ≤ unrH1 (resRep (uRep O (M := M) r χ) (D w)) I ∧
          Ine (F := E) (Av v) ≤ I.map (D w).subtype) →
      Module.length O ↥((HcG ⊓ (⨅ v, unrH1 (uRep O (M := M) r χ) (Io v)) ⊓
          ⨅ v, unrH1 (uRep O (M := M) r χ) (IS v)) ⊓
        ⨅ w ∈ places, (F w).comap (resH1 (uRep O (M := M) r χ) (D w))) ≤
      Module.length O (O ⧸ Ideal.span {(l : O)}) * (padicValNat l (classNumber E) : ℕ∞)

end Formalism.RepresentationBoundsCohomology.T2
