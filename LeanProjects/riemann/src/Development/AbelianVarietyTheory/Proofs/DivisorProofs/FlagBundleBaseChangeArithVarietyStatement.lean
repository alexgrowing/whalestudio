import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleBaseChangeArithVariety
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BcFlag
open CategoryTheory AlgebraicGeometry Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CovTest GlobalTheory.Published
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_bundle_base_change_arith_variety : ∀ (k : Type) [CommRing k] (B Y B' : Scheme.{0}) [IsIntegral B] [IsIntegral Y] [IsIntegral B']
    (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d : ℕ), IsArithVar q d → IsArithVar p (d + 1) → ∀ (π : Y ⟶ B) (_ : π ≫ q = p)
    (E : B.Modules), GlobalTheory.VB.IsVB E 2 → ∀ (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2),
    IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl) → ∀ g : B' ⟶ B, IsArithVar (g ≫ q) d →
    g (genericPoint B') = genericPoint B → g.residueDegree (genericPoint B') ≠ 0 →
    ∃ (_ : IsIntegral (pullback π g : Scheme.{0})), IsArithVar (pullback.fst π g ≫ p) (d + 1) ∧
      pullback.fst π g (genericPoint (pullback π g : Scheme.{0})) = genericPoint Y ∧
      (pullback.fst π g).residueDegree (genericPoint (pullback π g : Scheme.{0})) ≠ 0 := by
  first | exact @GlobalTheory.LineBundleBaseChange.main | exact GlobalTheory.LineBundleBaseChange.main | (intros; apply GlobalTheory.LineBundleBaseChange.main <;> assumption)
