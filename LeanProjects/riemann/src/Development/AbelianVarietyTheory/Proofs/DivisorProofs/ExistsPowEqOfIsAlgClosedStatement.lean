import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowEqOfIsAlgClosed
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtLevOver
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pow_eq_point_of_isAbelianScheme : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (n : ℕ), 0 < n → ∀ g : Over.mk x ⟶ A, ∃ g' : Over.mk x ⟶ A, g' ^ n = g := by
  first | (exact @GlobalTheory.AbDivPt.exists_pow_eq_of_isAlgClosed) | (exact GlobalTheory.AbDivPt.exists_pow_eq_of_isAlgClosed) | (intros; apply GlobalTheory.AbDivPt.exists_pow_eq_of_isAlgClosed  <;> assumption)
