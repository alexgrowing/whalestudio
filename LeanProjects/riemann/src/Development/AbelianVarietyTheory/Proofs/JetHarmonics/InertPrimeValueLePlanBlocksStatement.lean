import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.InertPrimeValueLePlanBlocks
import Development.AbelianVarietyTheory.Definitions.Jets.DepthNumbersThresholdEq
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.UnitaryBoundIntegral Formalism.L2.DIV Formalism.L2.Pj Formalism.BasicNotions GlobalTheory.GoodDepth NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertPrime_value_le_planBlocks : ∀ (P : RF.Par) (l : ℕ) (C1 : ℝ), ParOK P → 5 ≤ l → ∀ (Pk : RF.PkgInert P l C1) (p : ∀ z, Plan l P.d (RF.alongOrb P z Pk.W)),
  (∀ z ∈ Pk.Z, ∀ a i, i0 P.k l ≤ i → (p z).y a i = 0) →
  (∀ z ∈ Pk.Z, ∀ a i, (p z).y a i ≠ 0 → (RF.GlobalTheory.bi (RF.bg a) a i ((p z).y a i)).Attains (Pk.R.X z) (Pk.R.F z) (RF.blockBd l (P.k - 1) P.m i ((p z).y a i))) →
  Pk.ν ≤ (∑ z ∈ Pk.Z, (p z).bound (P.k - 1) P.m) + Pk.rest / ((l : ℝ) - 1) := by
  first | exact @GlobalTheory.PlanValue.val_le_plan | exact GlobalTheory.PlanValue.val_le_plan | (intros; apply GlobalTheory.PlanValue.val_le_plan <;> assumption)
