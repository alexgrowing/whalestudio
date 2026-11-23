import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankTwoFlagBundleSection
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BcFlag
open CategoryTheory AlgebraicGeometry Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CovTest GlobalTheory.Published
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_two_flag_bundle_section : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k)
    (p : Y ⟶ Sp k) (d : ℕ), IsArithVar q d → IsArithVar p (d + 1) → ∀ (π : Y ⟶ B) (_ : π ≫ q = p) (E : B.Modules),
    GlobalTheory.VB.IsVB E 2 → ∀ (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2),
    IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl) →
    ∃ (Z : Scheme.{0}) (_ : IsIntegral Z) (i : Z ⟶ Y), IsArithVar (i ≫ p) d ∧
      (i ≫ π) (genericPoint Z) = genericPoint B ∧ (i ≫ π).residueDegree (genericPoint Z) ≠ 0 := by
  first | exact @GlobalTheory.CovTest.Multisection.exists_multisection | exact GlobalTheory.CovTest.Multisection.exists_multisection | (intros; apply GlobalTheory.CovTest.Multisection.exists_multisection <;> assumption)
