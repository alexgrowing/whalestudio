import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteTypeModelSameFibre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfRingHom
open CategoryTheory AlgebraicGeometry Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.BdDim GlobalTheory.SiegelTor GlobalTheory.ZM GlobalTheory.CM GlobalTheory.Models
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_type_model_same_fibre : ∀ (k₀ k : Type) [Field k₀] [Field k] (ι : k₀ →+* k) (Y : Scheme.{0}) (s : Y ⟶ Sp k₀) (G G' : Over Y) [GrpObj G] [GrpObj G'] (z : Sp k ⟶ Y), LocallyOfFiniteType s → IsSemiAbelian G → IsSemiAbelian G' → z ≫ s = spMap ι → SameFibre G z G' z → ∃ (A : Type) (_ : CommRing A) (_ : Algebra k₀ A) (j : A →+* k) (a : Sp A ⟶ Y), Algebra.FiniteType k₀ A ∧ Function.Injective j ∧ spMap j ≫ a = z ∧ a ≫ s = spMap (algebraMap k₀ A) ∧ SameFibre G a G' a := by
  first | exact @GlobalTheory.sameFibre_spreads_to_fg_subalgebra | exact GlobalTheory.sameFibre_spreads_to_fg_subalgebra | (intros; apply GlobalTheory.sameFibre_spreads_to_fg_subalgebra <;> assumption)
