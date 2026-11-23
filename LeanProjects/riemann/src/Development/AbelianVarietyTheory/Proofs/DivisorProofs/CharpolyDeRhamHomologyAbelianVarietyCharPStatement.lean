import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyDeRhamHomologyAbelianVarietyCharP
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.BlockTheory.AbelianSchemeLaw.SemiAbelianSchemes
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.charpoly_deRhamHomology_abelianVariety_charP : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p]
    (B : GlobalTheory.AV.AbVar k) (f : B ⟶ B) [Module.Finite k (HdR B.X)],
    LinearMap.charpoly (push (dp0 k) (𝟙 _) f.hom) = (GlobalTheory.AV.AbVar.charpoly f).map (Int.castRingHom k) := by
  first | (exact @GlobalTheory.DeRhamCharpolyP.charpoly_push) | (exact GlobalTheory.DeRhamCharpolyP.charpoly_push) | (intros; apply GlobalTheory.DeRhamCharpolyP.charpoly_push <;> assumption)
