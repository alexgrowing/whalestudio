import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinBundleKernelFirstCoordEquations
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZphiPowPr
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zarhinBundle_kernel_firstCoord_equations : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A) (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu) (T : Over S) (x : T ⟶ GlobalTheory.ZarhinFam.Zob c.A B), (∃ t : ((GlobalTheory.ZarhinFam.zP c.A B c.isLB hZ.2.1.isLB d mu).pull (lift (snd (GlobalTheory.ZarhinFam.Zob c.A B) T ≫ x) (fst (GlobalTheory.ZarhinFam.Zob c.A B) T)).left).Gen, t.IsGen) → ∀ i, (x ≫ GlobalTheory.ZarhinFam.pa c.A B i ≫ la) * ∏ j, (x ≫ GlobalTheory.ZarhinFam.pb c.A B j) ^ GlobalTheory.ZarhinFam.quat d j i = 1 := by
  first | (exact @GlobalTheory.ZarhinKerA.zarhinBundle_kernel) | (exact GlobalTheory.ZarhinKerA.zarhinBundle_kernel) | (intros; apply GlobalTheory.ZarhinKerA.zarhinBundle_kernel  <;> assumption)
