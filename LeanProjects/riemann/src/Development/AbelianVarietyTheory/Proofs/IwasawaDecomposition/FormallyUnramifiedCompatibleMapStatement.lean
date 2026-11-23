import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormallyUnramifiedCompatibleMap
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formally_unramified_compatible_map : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (X Z : GMod Xo c) (π : Z.X ⟶ X.X), Z.j ≫ π = X.j → π ≫ X.s = Z.s → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (ξ : Sp R ⟶ X.X) (z : Z.X), IsCN R → IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom → ((residue R).comp (Scheme.stalkClosedPointTo ξ).hom).FormallyUnramified → ξ (closedPoint R) = π z → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ξ' : Sp R' ⟶ Z.X) (φ : R →+* R'), IsCN R' ∧ ξ' (closedPoint R') = z ∧ IsEtaleCompletion (Scheme.stalkClosedPointTo ξ').hom ∧ ((residue R').comp (Scheme.stalkClosedPointTo ξ').hom).FormallyUnramified ∧ Function.Injective φ ∧ IsLocalHom φ ∧ ξ' ≫ π = spMap φ ≫ ξ ∧ Dense (ξ' ⁻¹' Set.range Z.j) := by
  first | exact @GlobalTheory.TorRef.ChartAbove.exists_chart_above | exact GlobalTheory.TorRef.ChartAbove.exists_chart_above | (intros; apply GlobalTheory.TorRef.ChartAbove.exists_chart_above <;> assumption)
