import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TangentBasisOfSplitTorsion
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasPRatio
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
open AlgebraicGeometry CategoryTheory Limits NumberField MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.HTLine
open Formalism.MainNotions.DIV.Cons (intO SCF)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangent_basis_of_split_torsion : HTBoundSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) [IsLocallyNoetherian X], X.IsSeparated → ∀ (p : ℕ), p.Prime → ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [CharZero R] (x : Sp R ⟶ X), (∃ ζ : R, IsPrimitiveRoot ζ p) → GlobalTheory.LineNorm.SplitTors t x p → ∀ (g : ℕ) (e : Fin g → (Sp (DualNumber R) ⟶ t.G.left)), GlobalTheory.LineNorm.IsTanBasis t x e → ∀ b : Bool, ∃ (M : ℕ) (h : Fin (M + 1) → Fin g → R), Pres t x p b e h := by
  first | exact @GlobalTheory.HTPres.exists_pres | exact GlobalTheory.HTPres.exists_pres | (intros; apply GlobalTheory.HTPres.exists_pres <;> assumption)
