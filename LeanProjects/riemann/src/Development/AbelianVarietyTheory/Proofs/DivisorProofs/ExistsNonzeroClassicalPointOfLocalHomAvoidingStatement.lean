import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroClassicalPointOfLocalHomAvoiding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeSpanSupPow
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ZH GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nonzero_classicalPoint_of_localHom_avoiding : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (U : M.Z.Opens), (U : Set M.Z).Nonempty → ∀ x : M.Z, ∃ s : M.O x, s ≠ 0 ∧ ∀ (p : ℕ) [Fact p.Prime] (χ : M.O x →+* OO p), IsLocalHom χ → χ s ≠ 0 → ∃ y : Sp (OO p) ⟶ M.Z, M.Cen U x y ∧ ∀ a : M.O x, M.val (gPt p ≫ y) a = ((χ a : OO p) : PadicAlgCl p) := by
  first | exact @GlobalTheory.Izumi.exists_ne_zero_forall_exists_cen | exact GlobalTheory.Izumi.exists_ne_zero_forall_exists_cen | (intros; apply GlobalTheory.Izumi.exists_ne_zero_forall_exists_cen <;> assumption)
