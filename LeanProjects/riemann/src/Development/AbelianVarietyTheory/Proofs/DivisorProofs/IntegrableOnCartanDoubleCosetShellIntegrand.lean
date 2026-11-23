import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ScaledIntegerPeriodic
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EventuallyDeepSubset
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instMeasMat
open GlobalTheory.IndefiniteRowSideFullHecke.ScaledIntegerPeriodic

namespace GlobalTheory.ShellInt

theorem integrableOn_shell : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ϖ : kˣ) (ν : kˣ →* ℂˣ) (e : ℕ), CondLE ϖ e ν →
    ∀ (a : ℕ) (μ : Measure (GL (Fin a) k)) [μ.IsHaarMeasure] (φ : Matrix (Fin a) (Fin a) k → ℂ),
      φ ∈ SB (Matrix (Fin a) (Fin a) k) → ∀ (n : Fin a → ℤ) (z : ℂ),
        IntegrableOn (fun g : GL (Fin a) k => φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) z) (shellSet ϖ n) μ := by
  intro k _ _ _ _ _ _ ϖ ν e hν a μ _ φ hφ n z
  have hcomp : IsCompact (shellSet ϖ n : Set (GL (Fin a) k)) :=
    (isCompact_KO.mul isCompact_singleton).mul isCompact_KO
  let χ : GL (Fin a) k →* ℂ :=
    { toFun := fun g => (ν (gdet g) : ℂ) * apow (gdet g) z
      map_one' := by simp
      map_mul' := fun g h => by simp only [gdet_mul, map_mul, Units.val_mul, apow_mul]; ring }
  have hχ1 : ∀ g ∈ detCong (ϖ ^ e) (Fin a), χ g = 1 := by
    intro g hg
    have h1 : ν (gdet g) = 1 := hν _ hg.2
    have h2 : apow (gdet g) z = 1 := apow_of_valuation_eq_one (valuation_gdet_of_mem_KO hg.1) z
    simp [χ, h1, h2]
  have hχc : Continuous χ := by
    refine continuous_of_continuousAt_one χ ?_
    have hev : (fun _ => (1 : ℂ)) =ᶠ[nhds (1 : GL (Fin a) k)] χ := by
      filter_upwards [(isOpen_detCong (ϖ ^ e) (Fin a)).mem_nhds (one_mem _)] with g hg
      exact (hχ1 g hg).symm
    have := (continuousAt_const (x := (1 : GL (Fin a) k)) (y := (1 : ℂ))).congr hev
    simpa using this
  have hcont : Continuous (fun g : GL (Fin a) k => φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) z) := by
    have h := (hφ.1.continuous.comp Units.continuous_val).mul hχc
    refine h.congr fun g => ?_
    simp [χ, mul_assoc]
  exact hcont.continuousOn.integrableOn_compact hcomp

end GlobalTheory.ShellInt
