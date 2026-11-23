import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntDerApply
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat GlobalTheory.FormalOrigin
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory

theorem spMap_fromSpecStalk_le_preimage_iff (X : Scheme.{0}) (x : X) (Ω : Type) [CommRing Ω] [IsLocalRing Ω]
    (ψ : X.presheaf.stalk x →+* Ω) (hψ : IsLocalHom ψ) (O : X.Opens) :
    ⊤ ≤ (spMap ψ ≫ X.fromSpecStalk x) ⁻¹ᵁ O ↔ x ∈ O := by
  constructor
  · intro h
    let p : ↥(Sp Ω) := closedPoint Ω
    have hm : (spMap ψ ≫ X.fromSpecStalk x) p ∈ O := h (x := p) trivial
    rw [Scheme.Hom.comp_apply] at hm
    have e : (spMap ψ) p = (closedPoint (X.presheaf.stalk x) : ↥(Spec (X.presheaf.stalk x))) := by
      show PrimeSpectrum.comap ψ (closedPoint Ω) = _
      exact IsLocalRing.comap_closedPoint ψ
    rw [e, Scheme.fromSpecStalk_closedPoint] at hm
    exact hm
  · intro hx w _
    have : X.fromSpecStalk x (spMap ψ w) ∈ Set.range (X.fromSpecStalk x) := ⟨_, rfl⟩
    rw [Scheme.range_fromSpecStalk] at this
    show (spMap ψ ≫ X.fromSpecStalk x) w ∈ O
    rw [Scheme.Hom.comp_apply]
    exact Specializes.mem_open (x := X.fromSpecStalk x (spMap ψ w)) this O.isOpen hx

theorem spMap_fromSpecStalk_top_le_iff : ∀ (X : Scheme.{0}) (x : X) (Ω : Type) [CommRing Ω] [IsLocalRing Ω]
    (ψ : X.presheaf.stalk x →+* Ω), IsLocalHom ψ → ∀ O : X.Opens,
    ⊤ ≤ (spMap ψ ≫ X.fromSpecStalk x) ⁻¹ᵁ O ↔ x ∈ O :=
  fun X x Ω _ _ ψ hψ O => spMap_fromSpecStalk_le_preimage_iff X x Ω ψ hψ O

end GlobalTheory
