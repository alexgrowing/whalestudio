import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExpansionConstantTermIndependent
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SvalUpSec
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.LN GlobalTheory.TorRef GlobalTheory.IntegralCombination
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.expansion_constant_term_independent : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R →
    ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G]
      [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (N : ℕ), 1 ≤ N →
    ∀ (n : ℕ) (σ : Fin n → H0 U.LG.L N) (f : Fin n → ∀ α, SecAb D.toPre N α),
      (∀ i, U.ExpandsAt 0 N (σ i) (f i)) →
      (∀ c : Fin n → R, (∃ i, c i ∉ maximalIdeal R) →
        ∃ (α : D.toPre.X) (j : Fin 4 → D.toPre.P.L.ι) (b : D.toPre.P.A.left),
          D.toPre.P.A.hom b = closedPoint R ∧
          b ∈ D.toPre.P.A.left.basicOpen ((∑ i, c i • f i α).f j)) →
      IndepAlong G U.LG.L N (toBase (residue R)) (fun i => upSec G (σ i)) := by
  first | exact @GlobalTheory.ClosedIndep.main | exact GlobalTheory.ClosedIndep.main | (intros; apply GlobalTheory.ClosedIndep.main <;> assumption)
