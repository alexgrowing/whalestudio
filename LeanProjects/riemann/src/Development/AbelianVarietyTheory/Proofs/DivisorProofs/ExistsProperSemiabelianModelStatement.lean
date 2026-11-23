import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProperSemiabelianModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfRingHom
open CategoryTheory AlgebraicGeometry Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.BdDim GlobalTheory.SiegelTor GlobalTheory.ZM GlobalTheory.CM GlobalTheory.Models
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_proper_semiabelian_model : ∀ (k₀ k : Type) [Field k₀] [Field k] [IsAlgClosed k] (ι : k₀ →+* k) (P₀ : Out.PolAV (Sp k₀)) (X : Scheme.{0}) (G : Over X) [GrpObj G] (x : Sp k ⟶ X), IsSemiAbelian G → IsAbPart G x P₀.A (spMap ι) → ∃ (X' : Scheme.{0}) (s' : X' ⟶ Sp k₀) (E : SplitExt X') (G' : Over X') (_ : GrpObj G') (x' : Sp k ⟶ X') (π : E.B.left ⟶ P₀.A.left), IsProper s' ∧ x' ≫ s' = spMap ι ∧ IsGrpPullback E.B P₀.A s' π ∧ IsSemiAbelian G' ∧ E.IsGt G' ∧ SameFibre G x G' x' := by
  first | exact @GlobalTheory.BdDim.UnivExt.exists_universal | exact GlobalTheory.BdDim.UnivExt.exists_universal | (intros; apply GlobalTheory.BdDim.UnivExt.exists_universal <;> assumption)
