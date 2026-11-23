import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBoxGenOfSection
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd GlobalTheory.ProdUnif

namespace GlobalTheory.ProdDim

theorem smoothDim_tensor {S : Scheme.{0}} {A B : Over S} {g g' : ℕ} (hg : SmoothOfRelativeDimension g A.hom)
    (hg' : SmoothOfRelativeDimension g' B.hom) : SmoothOfRelativeDimension (g' + g) (A ⊗ B).hom := by
  have : SmoothOfRelativeDimension g' (Limits.pullback.fst A.hom B.hom) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g').of_isPullback
      (IsPullback.of_hasPullback A.hom B.hom).flip hg'
  rw [Over.tensorObj_hom]
  exact smoothOfRelativeDimension_comp g' g _ _

theorem g_eq_add : ∀ (S : Scheme.{0}) (P P₁ P₂ : PolAV S) (a₁ : P.A ⟶ P₁.A) (a₂ : P.A ⟶ P₂.A),
    Nonempty S → IsIso (lift a₁ a₂) → P.g = P₁.g + P₂.g := by
  intro S P P₁ P₂ a₁ a₂ ⟨s⟩ hi
  have h := smoothDim_tensor P₁.smoothDim P₂.smoothDim
  haveI : IsIso (lift a₁ a₂).left := inferInstanceAs (IsIso ((Over.forget S).map (lift a₁ a₂)))
  have hw : (lift a₁ a₂).left ≫ (P₁.A ⊗ P₂.A).hom = P.A.hom := Over.w _
  have h2 : SmoothOfRelativeDimension (0 + (P₂.g + P₁.g)) P.A.hom := by
    rw [← hw]
    exact smoothOfRelativeDimension_comp 0 (P₂.g + P₁.g) _ _
  have := ReciprocityTheory.ChartRestriction.G.H1.dim_unique P.A.hom P.smoothDim h2 (eSec P.A s)
  omega

end GlobalTheory.ProdDim
