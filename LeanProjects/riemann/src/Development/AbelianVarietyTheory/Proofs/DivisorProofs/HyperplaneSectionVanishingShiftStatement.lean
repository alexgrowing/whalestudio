import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperplaneSectionVanishingShift
import Development.AbelianVarietyTheory.Definitions.Divisors.IntegralBound
import Formalism.HarderNarasimhan.StatementPl
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hyperplane_section_vanishing_shift : ∀ (k : Type) [Field k] (Y : Scheme.{0}) [Algebra k Γ(Y, ⊤)], IsProjOver (GlobalTheory.strHom k Y) → ∀ (L : LB Y) (hL : L.IsLB) (F : Y.Modules) [IsFiniteQC F] (t : L.Sec) [Mono (GlobalTheory.cutHom F hL t)] (j₀ : ℤ), VanishFrom L F j₀ → VanishFrom L (GlobalTheory.cut F hL t) (j₀ + 1) ∧ ∀ j : ℤ, j₀ + 1 ≤ j → GlobalTheory.hdim k (GlobalTheory.twistZ F L j) 0 = GlobalTheory.hdim k (GlobalTheory.twistZ F L (j - 1)) 0 + GlobalTheory.hdim k (GlobalTheory.twistZ (GlobalTheory.cut F hL t) L j) 0 := by
  first | exact @GlobalTheory.HSCore.vanishFrom_cut_and_hdim | exact GlobalTheory.HSCore.vanishFrom_cut_and_hdim | (intros; apply GlobalTheory.HSCore.vanishFrom_cut_and_hdim <;> assumption)
