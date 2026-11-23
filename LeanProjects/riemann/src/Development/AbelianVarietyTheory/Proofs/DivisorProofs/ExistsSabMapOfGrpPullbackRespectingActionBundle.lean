import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsPullCubicalOfIso
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UCanon.TriplePull

theorem exists_sabMap_of_isProper : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' : Scheme.{0}} (t' : SAB H S') (t : SAB H S) (f : S' ⟶ S) (π : t'.G.left ⟶ t.G.left), IsProper t.G.hom → IsGrpPullback t'.G t.G f π → (∀ a, (t'.act.act a).left ≫ π = π ≫ (t.act.act a).left) → LBIso t'.PP.L (t.PP.L.pull π) → ∃ m : SABMap t' t f, m.φ = π := by
  intro E _ _ _ H S S' t' t f π hp gp hact h
  have hp' : IsProper t'.G.hom := MorphismProperty.of_isPullback (P := @IsProper) gp.1 hp
  exact GlobalTheory.CartTriple.exists_tripleMap GlobalTheory.lawsFieldsSeparately.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 E H S S' f t' t π
    ⟨t'.semi.comm, t'.semi.smooth, hp', t'.semi.geomConnected⟩ gp hact h

end GlobalTheory.UCanon.TriplePull
