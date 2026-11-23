import Mathlib
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsClosedImmersionIffPullRatio
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsProjByOfIsPullback

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap PSpace resG IsProjOver)
namespace GlobalTheory.ProjSpace

theorem isProjOver_pspace_str (R : Type) [CommRing R] (N : ℕ) : IsProjOver (PSpace.str R N) :=
  ⟨N, 𝟙 _, inferInstance, Category.id_comp _⟩

theorem isProjOver_of_isPullback {R : Type} [CommRing R] {X Y Z : Scheme.{0}} {p : Z ⟶ X} {q : Z ⟶ Y}
    {f : X ⟶ Sp R} {g : Y ⟶ Sp R} (sq : IsPullback p q f g) (hf : IsProjOver f) (hg : IsProjOver g) :
    IsProjOver (p ≫ f) :=
  (isProjBy_iff_isProjOver _).1 (GlobalTheory.AbLaw.Segre.isProjBy_of_isPullback p q sq
    ((isProjBy_iff_isProjOver f).2 hf) ((isProjBy_iff_isProjOver g).2 hg))

theorem isProjOver_pullback_str (R : Type) [CommRing R] (N M : ℕ) :
    IsProjOver (pullback.fst (PSpace.str R N) (PSpace.str R M) ≫ PSpace.str R N) :=
  isProjOver_of_isPullback (IsPullback.of_hasPullback _ _) (isProjOver_pspace_str R N)
    (isProjOver_pspace_str R M)

end GlobalTheory.ProjSpace
