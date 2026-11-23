import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionDescentFlatSurjectiveQuasiCompact
import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.InvariantFunctionsDescend
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupSchemeUnitStalkDataGerm
open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_descent_flat_surjective_quasiCompact : ∀ {X B H : Scheme.{0}} (L : LB X), L.IsLB → ∀ (q : H ⟶ B), Flat q → Surjective q → QuasiCompact q → ∀ {K : Type} [Fintype K] (ψ : K → (B ⟶ X)) (ε : K → ℤ) (σ : LB.Sec (LB.LinComb L (fun k => q ≫ ψ k) ε)), (∀ (S : Type) [CommRing S] [IsLocalRing S] (g₁ g₂ : Sp S ⟶ H), g₁ ≫ q = g₂ ≫ q → ∀ J, Good L (closedPoint S) J → sval σ g₁ (closedPoint S) J = sval σ g₂ (closedPoint S) J) → ∃ b : LB.Sec (LB.LinComb L ψ ε), ∀ (Z : Scheme.{0}) (r : Z ⟶ H) (z : Z) J, Good L z J → sval σ r z J = sval b (r ≫ q) z J := by
  first | exact @GlobalTheory.LocDescent.exists_sec_descend | exact GlobalTheory.LocDescent.exists_sec_descend | (intros; apply GlobalTheory.LocDescent.exists_sec_descend <;> assumption)
