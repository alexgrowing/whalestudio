import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.GlobFnsDvrPf
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsUnimodularSolTwoTorsion
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SystemPrimesDistinctLevelsGeThree
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LeftEqIffLieVecSmul

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GlobFnsDvrChecks

theorem premises_met {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) :
    IsAdicComplete (IsLocalRing.maximalIdeal ℤ_[3]) ℤ_[3] ∧ ∃ t : SAB H (Sp ℤ_[3]),
      IsProper ((Over.pullback (spMap (algebraMap ℤ_[3] (FractionRing ℤ_[3])))).obj t.G).hom ∧ ¬ IsIso t.G.hom := by
  open GlobalTheory.Models GlobalTheory.Models.EllipticModel GlobalTheory.WeierstrassCurve in
  obtain ⟨_, hc, -⟩ := GlobalTheory.exists_grpObj_weierstrass _ curve isUnit_curve_Δ
  open GlobalTheory.Models GlobalTheory.Models.EllipticModel GlobalTheory.WeierstrassCurve in
  have hA := isAbelianScheme_schemeOver _ curve isUnit_curve_Δ hc
  refine ⟨inferInstance, GlobalTheory.Models.tensorTriple H _ hA, ?_,
    GlobalTheory.Models.EllipticModel.not_isIso_tensorTriple H _ hA GlobalTheory.Models.EllipticModel.not_mono_toSpec⟩
  have := GlobalTheory.Models.isProper_tensorTriple (H := H) _ hA
  exact inferInstanceAs (IsProper (pullback.snd _ _))

theorem not_surjective_splitTorus (S : Scheme.{0}) [Nonempty S] (X : Type) [AddCommGroup X] [Nontrivial X] :
    ¬ Function.Surjective (splitTorus S X).hom.appTop.hom := by
  intro h
  refine GlobalTheory.Diag.id_ne_one S (X := X) (GlobalTheory.Diag.hom_ext fun x => ?_)
  have h1 : ∀ t : splitTorus S X ⟶ splitTorus S X,
      (Rosenlicht.coord t).hom (AddMonoidAlgebra.single x 1) = t.left.appTop.hom (Rosenlicht.chi X x) :=
    fun t => by rw [← Category.comp_id t, Rosenlicht.coord_comp, Category.comp_id]; rfl
  obtain ⟨c, hc⟩ := h (Rosenlicht.chi X x)
  have h2 : ∀ t : splitTorus S X ⟶ splitTorus S X,
      t.left.appTop.hom (Rosenlicht.chi X x) = (splitTorus S X).hom.appTop.hom c := fun t => by
    rw [← hc, ← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Scheme.Hom.comp_appTop, Over.w]
  rw [h1, h1, h2, h2]

theorem properness_needed {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V]
    [IsDomain V] : ∃ t : SAB H (Sp V), ¬ Function.Bijective (powObj t.G 1).hom.appTop.hom := by
  refine ⟨GlobalTheory.Models.Inhab.trivTriple H (splitTorus (Sp V) (𝓞 E)) (GlobalTheory.Diag.isSemiAbelian _ _)
    (GlobalTheory.Diag.diagAct _ _ _), fun h => ?_⟩
  exact not_surjective_splitTorus (Sp V) (𝓞 E)
    (GlobalFunctionsDvrPowers.bijective_of_iso (ρ_ (splitTorus (Sp V) (𝓞 E))).symm h).2

theorem not_without_properness : ¬ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type)
    [CommRing V] [IsDomain V] [IsDiscreteValuationRing V], IsAdicComplete (IsLocalRing.maximalIdeal V) V →
    ∀ t : SAB H (Sp V), ∀ n : ℕ, Function.Bijective (powObj t.G n).hom.appTop.hom := fun h => by
  obtain ⟨t, ht⟩ := properness_needed GlobalTheory.HostModel.host ℤ_[3]
  exact ht (h _ _ ℤ_[3] inferInstance t 1)

end GlobalTheory.GlobFnsDvrChecks
