import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniversalAbelianSchemeTorsionRationalFieldPoint
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.universalAbelianScheme_torsion_rational_fieldPoint : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), ∀ (K K' : Type) [Field K] [Field K'] [IsAlgClosed K'] (κ : K →+* K') (y : Sp K ⟶ Xo.XF c) (x : Over.mk (spMap κ ≫ y ≫ pullback.fst _ _) ⟶ Xo.univ.t.G), x ^ l.M' = 1 → ∃ x₀ : Over.mk (y ≫ pullback.fst _ _) ⟶ Xo.univ.t.G, x₀ ^ l.M' = 1 ∧ x.left = spMap κ ≫ x₀.left := by
  first | exact @GlobalTheory.XFTorsion.torsion_rational | exact GlobalTheory.XFTorsion.torsion_rational | (intros; apply GlobalTheory.XFTorsion.torsion_rational <;> assumption)
