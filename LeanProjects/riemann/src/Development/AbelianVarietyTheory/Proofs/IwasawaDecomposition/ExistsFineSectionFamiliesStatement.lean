import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFineSectionFamilies
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SvalUpSec
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.LN GlobalTheory.TorRef GlobalTheory.IntegralCombination
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fine_section_families : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R →
    ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G]
      [IsCommMonObj G], IsSemiAbelian G → Unif (maximalIdeal R) D A G → ∀ N : ℕ, 1 ≤ N → FineData D.toPre N →
    ∃ (n : ℕ) (Φ : Fin n → Fam D.toPre (FractionRing R) N) (f : Fin n → ∀ α, SecAb D.toPre N α),
      (∀ i α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) α) (DegPre.famε N) ((Φ i).s α)
        (D.toPre.famφB α) (DegPre.famε N) (f i α) (DegPre.prB D.toPre (FractionRing R)).left 1) ∧
      LinearIndependent (FractionRing R) Φ ∧ Submodule.span (FractionRing R) (Set.range Φ) = ⊤ ∧
      ∀ c : Fin n → R, (∃ i, c i ∉ maximalIdeal R) →
        ∃ (α : D.toPre.X) (j : Fin 4 → D.toPre.P.L.ι) (b : D.toPre.P.A.left),
          D.toPre.P.A.hom b = closedPoint R ∧
          b ∈ D.toPre.P.A.left.basicOpen ((∑ i, c i • f i α).f j) := by
  first | exact @GlobalTheory.IntFam.intFam | exact GlobalTheory.IntFam.intFam | (intros; apply GlobalTheory.IntFam.intFam <;> assumption)
