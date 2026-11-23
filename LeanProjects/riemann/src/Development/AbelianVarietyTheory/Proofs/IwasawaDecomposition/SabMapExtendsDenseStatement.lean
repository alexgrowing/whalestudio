import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SabMapExtendsDense
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sabMap_extends_dense : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (X Z : GMod Xo c) (π : Z.X ⟶ X.X), Z.j ≫ π = X.j → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ξ' : Sp R' ⟶ Z.X) (t' : SAB H (Sp R')), IsCN R' → Dense (ξ' ⁻¹' Set.range Z.j) → SABMap t' X.t (ξ' ≫ π) → Nonempty (SABMap t' Z.t ξ') := by
  first | exact @GlobalTheory.TorRef.TriplePull.sab_of_chart | exact GlobalTheory.TorRef.TriplePull.sab_of_chart | (intros; apply GlobalTheory.TorRef.TriplePull.sab_of_chart <;> assumption)
