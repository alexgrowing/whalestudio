import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCuspRuleOfBoundaryVanishingComponentSectio
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
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cuspRule_of_boundaryVanishing_componentSection : ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂) (la : AllWt.Weight (T.Q.Dw j)) (L : LB (X₀ TF.Y Z)) (hL : L.IsLB), CechPic.pull (π₀ TF.X Z) (cls L hL) = cls (L₀ TF.X Z la) (isLB_L₀ TF.X Z _) → ∃ Φ : H0 (s₀ TF.Y Z) L ⊤ → Rul Y.d.Xo₂ Y.d.c₂, (∀ t, nonzeroLocus (toSec t) ≤ (j₀ TF.Y Z).opensRange → Φ t ∈ cuspOn Y.U Z (wtOf (T.Q.Dw j) la 0)) ∧ ∀ (y : FrPt Y.d.Xo₂ Y.d.c₂ ℂ) (v : Sp ℂ ⟶ V₀ TF.Y Z), v ≫ i₀ TF.Y Z = ptF y → ∀ (k : L.ι) (hk : ⊤ ≤ (v ≫ j₀ TF.Y Z) ⁻¹ᵁ L.U k), ∃ lam : ℂˣ, ∀ t, evR Y.d.Xo₂ Y.d.c₂ (Φ t) y = lam * H0.val (v ≫ j₀ TF.Y Z) k le_top hk t := by
  first | exact @GlobalTheory.OrbitSep.exists_rule_of_cls_pull | exact GlobalTheory.OrbitSep.exists_rule_of_cls_pull | (intros; apply GlobalTheory.OrbitSep.exists_rule_of_cls_pull <;> assumption)
