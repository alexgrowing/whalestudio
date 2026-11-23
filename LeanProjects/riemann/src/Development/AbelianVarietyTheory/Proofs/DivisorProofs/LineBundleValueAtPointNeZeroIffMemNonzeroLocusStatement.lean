import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleValueAtPointNeZeroIffMemNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GapGeSubKapBase
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open GlobalTheory.Discrepancy GlobalTheory.QCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundleValueAtPoint_ne_zero_iff_mem_nonzeroLocus : ∀ (K : Type) [Field K] (Y : Scheme.{0}) (q : Y ⟶ Sp K) (L : LB Y) (σ : L.Sec) (z : Sp K ⟶ Y) (i : L.ι) (hi : ⊤ ≤ z ⁻¹ᵁ L.U i), (H0.val (p := q) z i le_top hi (H0.ofSec q ⊤ σ) ≠ 0 ↔ z (IsLocalRing.closedPoint K) ∈ nonzeroLocus σ) := by
  first | exact @GlobalTheory.ValNe.val_ofSec_ne_zero_iff | exact GlobalTheory.ValNe.val_ofSec_ne_zero_iff | (intros; apply GlobalTheory.ValNe.val_ofSec_ne_zero_iff <;> assumption)
