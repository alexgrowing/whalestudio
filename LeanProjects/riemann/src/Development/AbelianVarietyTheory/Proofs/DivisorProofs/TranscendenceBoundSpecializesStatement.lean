import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranscendenceBoundSpecializes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfRingHom
open CategoryTheory AlgebraicGeometry Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.BdDim GlobalTheory.SiegelTor GlobalTheory.ZM GlobalTheory.CM GlobalTheory.Models
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transcendence_bound_specializes : ∀ (X : Scheme.{0}) (x y : X) (n : ℕ), x ⤳ y → TrLe (X.residueField x) n → TrLe (X.residueField y) n := by
  first | exact @GlobalTheory.BdDim.trLe_residueField_of_specializes | exact GlobalTheory.BdDim.trLe_residueField_of_specializes | (intros; apply GlobalTheory.BdDim.trLe_residueField_of_specializes <;> assumption)
