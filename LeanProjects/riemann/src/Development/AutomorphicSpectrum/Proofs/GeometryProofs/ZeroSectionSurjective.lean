import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TranslDiffEq
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Ar.Coc

theorem tensor_isPullback {X0 : Scheme.{0}} (A B : Over X0) :
    IsPullback (fst A B).left (snd A B).left A.hom B.hom :=
  IsPullback.of_hasPullback A.hom B.hom

theorem secZ_isPullback {X0 : Scheme.{0}} (G : Over X0) {k : Type} [Field k] (x : Sp k ⟶ X0) (m : ℕ) :
    IsPullback (secZ G x m) (pullback.snd G.hom x) (fst (Tm x m) G).left
      (spMap ((jetAug : Jet k Unit m →ₐ[k] k) : Jet k Unit m →+* k)) := by
  have hR := (tensor_isPullback (Tm x m) G).flip
  have hO : IsPullback (secZ G x m ≫ (snd (Tm x m) G).left) (pullback.snd G.hom x) G.hom
      (spMap ((jetAug : Jet k Unit m →ₐ[k] k) : Jet k Unit m →+* k) ≫ (Tm x m).hom) := by
    rw [secZ_snd]
    have e : spMap ((jetAug : Jet k Unit m →ₐ[k] k) : Jet k Unit m →+* k) ≫ (Tm x m).hom = x := by
      dsimp
      rw [← Category.assoc, spMap_comp_alg]
      simp [spMap]
    rw [e]
    exact IsPullback.of_hasPullback G.hom x
  exact IsPullback.of_right hO (secZ_fst G x m) hR

theorem secZ_surj (X0 : Scheme.{0}) (G : Over X0) (k : Type) [Field k] (x : Sp k ⟶ X0) (m : ℕ) :
    Function.Surjective (secZ G x m).base := by
  have hs : Surjective (spMap ((jetAug : Jet k Unit m →ₐ[k] k) : Jet k Unit m →+* k)) := ⟨fun q =>
    ⟨IsLocalRing.closedPoint k, jet_pt m q _⟩⟩
  have := MorphismProperty.of_isPullback (P := @Surjective) (secZ_isPullback G x m).flip hs
  exact this.surj

end GlobalTheory.CompanionTheory.Ar.Coc
