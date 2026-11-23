import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvrLiftOfGeometricPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntEmbCoe
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSemiabelianExtensionDvr
open CategoryTheory AlgebraicGeometry Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Mean4 GlobalTheory.Mean4O
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dvr_lift_of_geometric_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Z : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : Sp Ω ⟶ Z.X), ∃ (T : Formalism.L2.Pj.CDVR) (χ : Sp T.V ⟶ Z.X) (y : Sp T.Fr ⟶ Xo.XF c) (ι : IsLocalRing.ResidueField T.V →+* Ω), y ≫ Z.j = Out.jK T.V ≫ χ ∧ spMap ι ≫ spMap (IsLocalRing.residue T.V) ≫ χ = x := by
  first | exact @GlobalTheory.GeomTrait.exists_trait_through | exact GlobalTheory.GeomTrait.exists_trait_through | (intros; apply GlobalTheory.GeomTrait.exists_trait_through <;> assumption)
