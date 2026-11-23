import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralFundamentalDomainEqVolMulClassSum
import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinPt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_fundamentalDomain_eq_vol_mul_classSum : ∀ {D : D7} (A : HSp D), A.gram = 1 → ∀ (m : Measure (Formalism.L2.Theta.GA D A)) (fd : Set (Formalism.L2.Theta.GA D A)),
    m.IsHaarMeasure → IsFundamentalDomain (GQ A) fd m →
    ∃ v : ℂ, v ≠ 0 ∧ ∀ (n : ℕ), n = A.rank → ∀ (pt : Formalism.MainNotions.StandardLatticesGL3.GA D n → Formalism.L2.Theta.GA D A),
      (∀ x, GlobalTheory.BotFormula.IsFinPt A (pt x) x) → ∀ Φ : Formalism.L2.Theta.GA D A → ℂ,
      (∀ γ ∈ GQ A, ∀ h, Φ (γ * h) = Φ h) → (∀ k ∈ GinfC A, ∀ h, Φ (h * k) = Φ h) →
      (∀ (x : Formalism.MainNotions.StandardLatticesGL3.GA D n) (k : Formalism.L2.Theta.GA D A), x ∈ GlobalTheory.NormSum.intG D n → GlobalTheory.BotFormula.IsFinPt A k x →
        ∀ h, Φ (h * k) = Φ h) →
      ∫ g in fd, Φ g ∂m = v * ∑ᶠ x : GlobalTheory.NormSum.Cls D n (GlobalTheory.NormSum.intG D n),
        ((GlobalTheory.NormSum.gam D (GlobalTheory.NormSum.intG D n) x.out : ℂ))⁻¹ * Φ (pt x.out) := by
  first | exact @GlobalTheory.BotClassMeas.integral_eq_vol_mul_classSum | exact GlobalTheory.BotClassMeas.integral_eq_vol_mul_classSum | (intros; apply GlobalTheory.BotClassMeas.integral_eq_vol_mul_classSum <;> assumption)
