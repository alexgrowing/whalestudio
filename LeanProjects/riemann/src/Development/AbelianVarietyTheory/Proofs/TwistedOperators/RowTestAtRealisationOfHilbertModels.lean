import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestHilbertModelsOfChoiceClaimsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestComplexSideOfHilbertModelsStatement
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RationalRowTestKernel
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowClaim

theorem GlobalTheory.RowTest.rowTest_realisation : GlobalTheory.Published.CuspRapidDecay → LinK → InjK → ConstK → SumOKK → Formula2K → SumRatK → RatioK → ∃ CF0 : ℝ, ∀ ε CF : ℝ, CF0 ≤ CF → ∃ x₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D), large₂.sc.eps = ε → x₀ ≤ large₂.sc.x → ∀ (G : Type) [Group G] [Fintype G] (Pl0 I0 T0 : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), GlobalTheory.RowClaim.HidaSetting large₂ R.toRealDat F.lv2 → (∃ ch : GlobalTheory.RowTest.Choice R.toRealDat, ch.Is ∧ ch.AtScale CF large₂.sc.b ∧ ch.FieldOK) → Formalism.IndefR.Rat.RowTest (R.toCx3 F) := by
  intro hC hL hI hCo hS hF hSR hR
  obtain ⟨CF0, hCF0⟩ := GlobalTheory.T.rowTest_hilbertModels_of_choiceClaims hC hL hI hCo hS hF hSR hR
  refine ⟨CF0, fun ε CF hCF => ?_⟩
  obtain ⟨x₀, hx₀⟩ := hCF0 ε CF hCF
  refine ⟨x₀, fun D large₂ hε hx G _ _ Pl0 I0 T0 A3 Ks _ _ _ R F hSet hch => ?_⟩
  exact GlobalTheory.T.rowTest_complexSide_of_hilbert_models D G Pl0 I0 T0 A3 Ks R F (hx₀ D large₂ hε hx G Pl0 T0 _ Ks R.toRealDat F.lv2 hSet hch)
