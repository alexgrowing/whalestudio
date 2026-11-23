import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankDeficientSchwartzAverage
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MajINonneg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay GlobalTheory.ThKTorus
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_deficient_schwartz_average : ∀ (F : Type) [Field F] [NumberField F] (v : Pl F) (ψ₀ : AddChar (Fv F v) ℂ), Continuous ψ₀ → ψ₀ ≠ 1 →
    ∀ (n d : ℕ) (c : Fin n → Fv F v), c ≠ 0 → ∀ f ∈ SB (Matrix (Fin n) (Fin d) (Fv F v)),
    (∀ Y : Matrix (Fin n) (Fin d) (Fv F v), Y.rank ≠ n → f Y = 0) →
    ∃ (N : ℕ) (a : Fin N → ℂ) (w : Fin N → Fin d → Fv F v), ∑ m, a m = 1 ∧
      ∀ Y : Matrix (Fin n) (Fin d) (Fv F v), (∑ m, a m * ψ₀ (∑ k, ∑ l, Y k l * c k * w m l)) * f Y = 0 := by
  first | exact @GlobalTheory.TorusSupportAvg.exists_charAvg_mul_eq_zero | exact GlobalTheory.TorusSupportAvg.exists_charAvg_mul_eq_zero | (intros; apply GlobalTheory.TorusSupportAvg.exists_charAvg_mul_eq_zero <;> assumption)
