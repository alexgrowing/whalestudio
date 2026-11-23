import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsClosedImmersionOfSpanLinePowerSections
import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsVVGenOfIsThetaFamily
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsIndepSections
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ZH
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isClosedImmersion_of_span_linePowerSections : Out.Laws → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (N : ℕ) (J : Type) [Fintype J] (t : J → LB.Sec (Out.LPow P.A P.L N (Out.baseOver (Sp K)))) (ρ : P.A.left ⟶ ((Out.baseOver (Sp K)) ⊗ P.A).left) (e : ρ ≫ (snd (Out.baseOver (Sp K)) P.A).left = 𝟙 P.A.left), 4 ≤ N → Submodule.span Γ((Out.baseOver (Sp K)).left, ⊤) (Set.range fun a => (Out.SecM.ofSec P.A (t a) : Out.SecM P.A P.L N (Out.baseOver (Sp K)))) = ⊤ → ImmBy P.A.hom (lbPow P.L N) (fun a => PowSec.down P.L (snd (Out.baseOver (Sp K)) P.A).left ρ e ((N : ℕ) : ℤ) (t a)) Set.univ := by
  first | exact @GlobalTheory.PowSec.immBy_down_of_span | exact GlobalTheory.PowSec.immBy_down_of_span | (intros; apply GlobalTheory.PowSec.immBy_down_of_span <;> assumption)
