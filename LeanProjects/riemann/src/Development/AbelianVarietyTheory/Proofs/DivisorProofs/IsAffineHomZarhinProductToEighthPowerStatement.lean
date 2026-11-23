import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineHomZarhinProductToEighthPower
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZphiPowPr
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAffineHom_zarhinProduct_to_eighthPower : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A) (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu), 0 < d → IsUnit ((d : ℕ) : Γ(S, ⊤)) → IsAffineHom (GlobalTheory.ZarhinFam.zphi c.A B mu).left := by
  first | (exact @GlobalTheory.ZarhinFam.isAffineHom_zphi) | (exact GlobalTheory.ZarhinFam.isAffineHom_zphi) | (intros; apply GlobalTheory.ZarhinFam.isAffineHom_zphi  <;> assumption)
