import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpMapGermFromSpec
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.KeyVals

theorem ring_of_isAffineOpen : ∀ (S : Scheme.{0}) [IsIntegral S] (s : S ⟶ Sp ℤ) (W : S.Opens), IsAffineOpen W → (W : Set S).Nonempty →
    Geo.Tor.IsNormalScheme S → LocallyOfFiniteType s → CharZero Γ(S, ⊤) →
    IsIntegrallyClosed Γ(S, W) ∧ CharZero Γ(S, W) ∧ Algebra.FiniteType ℤ Γ(S, W) := by
  intro S _ s W hW hne hN hs hc
  haveI : Nonempty W := hne.to_subtype
  haveI : GlobalTheory.IsNormalScheme S := (GlobalTheory.isNormalScheme_iff_pred S).2 hN
  refine ⟨GlobalTheory.IsNormalScheme.isIntegrallyClosed_of_isAffineOpen hW, ?_, ?_⟩
  · exact charZero_of_injective_ringHom (map_injective_of_isIntegral S (homOfLE (le_top : W ≤ ⊤)))
  · have h₁ : (s.appLE ⊤ W le_top).hom.FiniteType :=
      HasRingHomProperty.appLE (P := @LocallyOfFiniteType) s hs ⟨⊤, isAffineOpen_top _⟩ ⟨W, hW⟩ le_top
    have h₂ : ((Scheme.ΓSpecIso (CommRingCat.of ℤ)).inv.hom).FiniteType :=
      RingHom.FiniteType.of_surjective _ (Scheme.ΓSpecIso (CommRingCat.of ℤ)).symm.commRingCatIsoToRingEquiv.surjective
    have h₃ := h₁.comp h₂
    rw [← RingHom.finiteType_algebraMap, RingHom.ext_int (algebraMap ℤ Γ(S, W))
      ((s.appLE ⊤ W le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℤ)).inv.hom)]
    exact h₃

end GlobalTheory.KeyVals
