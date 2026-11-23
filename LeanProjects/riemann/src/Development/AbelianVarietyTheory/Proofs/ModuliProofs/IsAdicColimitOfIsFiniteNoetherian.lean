import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.FiniteAlgebraLocalCompletion

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.FlatTors GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator
open scoped TensorProduct

namespace GlobalTheory.FiniteTorsLift

open GlobalTheory.TorusModel GlobalTheory.FormalPoint GlobalTheory.AdicColimit GlobalTheory.TorsionFormCompare

theorem isAdicColimit_of_isFinite_noetherian {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hc : IsAdicComplete (maximalIdeal R) R) (N : Over (Sp R)) [IsFinite N.hom] :
    IsAdicColimit (maximalIdeal R) N := by
  have : IsAffine N.left := isAffine_of_isAffineHom N.hom
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (N.left.isoSpec.inv ≫ N.hom)
  have hf : IsFinite (Spec.map φ) := by rw [hφ]; infer_instance
  rw [IsFinite.SpecMap_iff] at hf
  letI : Algebra R Γ(N.left, ⊤) := φ.hom.toAlgebra
  have : Module.Finite R Γ(N.left, ⊤) := hf
  have : HenselianLocalRing R :=
    { is_henselian := fun f hf a₀ h₁ h₂ =>
        HenselianRing.is_henselian (I := maximalIdeal R) f hf a₀ h₁ (h₂.map _) }
  have H := isAdicColimit_finite_henselian_of_local isAdicColimit_spec_of_isLocalRing
    isAdicColimit_of_disjoint_cover R (maximalIdeal R) R Γ(N.left, ⊤) (algebraMap R _)
    (ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.isAdicComplete_finite_algebra _)
  exact IsAdicColimit.of_iso (Over.isoMk N.left.isoSpec.symm hφ.symm) H

theorem main : AllFlat fun {E} _ _ _ {H} {R} _ _ _ {t} P {W} ψW k => ∀ (N : Over (Sp R)) (g₀ : GtPt P.D.toPre N) (x₀ : N ⟶ t.G), IsFinite N.hom → GtTors k g₀ → (∀ (T : Over (Sp R)) (g : GtPt P.D.toPre T), GtTors k g → ∃! h : T ⟶ N, GtPt.IsPull h.left g₀ g) → FormalEq P.U.toUnifPre x₀ g₀ → ∀ T : Over (Sp R), IsFinite T.hom → ∀ x : T ⟶ t.G, x ^ k = 1 → ∃ h : T ⟶ N, h ≫ x₀ = x := by
  intro E _ _ _ H R _ _ _ _ hR t P W _ _ ψW k _ N g₀ x₀ _ _ huniv hform T _ x hx
  obtain ⟨_, _, _, hc⟩ := hR
  have hT := isAdicColimit_of_isFinite_noetherian hc T
  obtain ⟨Gt, _, _, Φ, hΦ, -⟩ := exists_represents P.D.toPre
  obtain ⟨J, hJ⟩ := exists_mulEquiv P.U.toUnifPre abelianSchemeLaws_all.1.globalFns hΦ
  obtain ⟨w, rfl⟩ := (J T hT).surjective x
  have hw : w ^ k = 1 := (J T hT).injective (by rw [map_pow, hx, map_one])
  obtain ⟨h, hh, -⟩ := huniv T (Φ T w) ((tors_iff hΦ k w).2 hw)
  exact ⟨h, ((hJ T hT w _).2 (((formalEq_iff _ _ _).1 hform).pull h hh)).symm⟩

end GlobalTheory.FiniteTorsLift
