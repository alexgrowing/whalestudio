import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExpansionIndependentSections
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SvalUpSec
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.LN GlobalTheory.TorRef GlobalTheory.IntegralCombination
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.expansion_independent_sections : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R →
    ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G]
      [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (N : ℕ), 1 ≤ N →
    ∀ (n : ℕ) (σ : Fin n → H0 U.LG.L N) (Φ : Fin n → Fam D.toPre (FractionRing R) N)
      (f : Fin n → ∀ α, SecAb D.toPre N α), (∀ i e, U.ExpandsAt e N (σ i) (f i)) →
      (∀ i α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) α) (DegPre.famε N) ((Φ i).s α)
        (D.toPre.famφB α) (DegPre.famε N) (f i α) (DegPre.prB D.toPre (FractionRing R)).left 1) →
      LinearIndependent (FractionRing R) Φ → Submodule.span (FractionRing R) (Set.range Φ) = ⊤ →
      BasisAlong G U.LG.L N (toBase (algebraMap R (FractionRing R))) (fun i => upSec G (σ i)) := by
  first | exact @GlobalTheory.GenBasis.main | exact GlobalTheory.GenBasis.main | (intros; apply GlobalTheory.GenBasis.main <;> assumption)
