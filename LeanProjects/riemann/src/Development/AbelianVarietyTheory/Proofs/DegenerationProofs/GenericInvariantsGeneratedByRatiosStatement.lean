import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GenericInvariantsGeneratedByRatios
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfTorusBased
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_invariants_generated_by_ratios : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] [IsSeparated G.hom] [QuasiCompact G.hom] (C : Charts G.left) (d : ℕ) (c : Fin d → C.Cl) (Sg : Set (Sp R)) [IsAffineHom (pullback.fst G.hom (Out.jK R))], Dense Sg → C.SplitOn c Sg → ∀ (a) (j : Fin d → C.I), C.Based c a j → ∀ i : splitTorus (Sp (FractionRing R)) (Fin d → ℤ) ⟶ ((Over.pullback (Out.jK R)).obj G), Charts.KerIs (H := ((Over.pullback (Out.jK R)).obj G)) (C.pull (pullback.fst G.hom (Out.jK R))) a j i → (∀ a', Stable i ((C.pull (pullback.fst G.hom (Out.jK R))).W a')) → ∀ a' (u : Γ(((Over.pullback (Out.jK R)).obj G).left, (C.pull (pullback.fst G.hom (Out.jK R))).W a')), HasWt i _ u 0 → u ∈ Subring.closure (Set.range (((Over.pullback (Out.jK R)).obj G).hom.appLE ⊤ ((C.pull (pullback.fst G.hom (Out.jK R))).W a') le_top).hom ∪ {v | ∃ j', C.wt j' = C.c₀ ∧ v = (C.pull (pullback.fst G.hom (Out.jK R))).r a' j'}) := by
  first | exact @GlobalTheory.ZJ.GenericInv.generic_invariants | exact GlobalTheory.ZJ.GenericInv.generic_invariants | (intros; apply GlobalTheory.ZJ.GenericInv.generic_invariants <;> assumption)
