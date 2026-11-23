import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericDegreePullbackFormula
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfIntersectionPowScales
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSAmp.PullPow

theorem gdeg_pull_and_isSelfInter_pow : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → (∀ (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k), IsArithVar q D → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q), π (genericPoint Y) = genericPoint X → π.residueDegree (genericPoint Y) ≠ 0 → ∀ L : HermLB p, gdeg (L.pull π hπ) D = (π.residueDegree (genericPoint Y) : ℝ) * gdeg L D) ∧ ∀ (L : HermLB p) (n : ℕ) (a : ℝ), L.IsSelfInter a → (L.pow n).IsSelfInter ((n : ℝ) ^ (D + 1) * a) := by
  intro hC k _ X _ p D hX
  refine ⟨fun Y _ q hY π hπ hη hδ L => GlobalTheory.CovTest.gdegPull k X Y p q D hX hY π hπ hη hδ L, ?_⟩
  intro L n a ha
  exact GlobalTheory.SelfInterPow.isSelfInter_pow hC k X p D hX L a ha n

end GlobalTheory.HSAmp.PullPow

end
