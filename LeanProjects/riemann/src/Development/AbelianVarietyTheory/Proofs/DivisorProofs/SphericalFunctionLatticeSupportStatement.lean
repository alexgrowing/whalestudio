import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SphericalFunctionLatticeSupport
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling GlobalTheory.ThK.Bot
open Formalism.L2.Host (aboveF)
open Formalism.UG (IsUnifV qV)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.spherical_function_lattice_support : ∀ (F : Type) [Field F] [NumberField F] (v : Pl F) (n d : ℕ),
    ∀ (ϖ : (Fv F v)ˣ), IsUnifV F v ϖ.1 → ∀ (e : Fin n → ℤ) (T : GL (Fin n) (Fv F v)), T.1 = Matrix.diagonal (fun i => ϖ.1 ^ e i) → ∀ k₁ ∈ KGL v n, ∀ k₂ ∈ KGL v n,
    ∀ T' : GL (Fin n) (Fv F v), T'.1 = Matrix.diagonal (fun i => ϖ.1 ^ max (e i) 0) → ∀ Y : Matrix (Fin n) (Fin d) (Fv F v),
      (∀ i j, (((k₁ * T')⁻¹).1 * Y) i j ∈ v.adicCompletionIntegers F) ↔
        (∀ i j, (((k₁ * T * k₂)⁻¹).1 * Y) i j ∈ v.adicCompletionIntegers F) ∧ ∀ i j, Y i j ∈ v.adicCompletionIntegers F := by
  first | exact @GlobalTheory.ThK.Bot.inter_kdiag_int_iff | exact GlobalTheory.ThK.Bot.inter_kdiag_int_iff | (intros; apply GlobalTheory.ThK.Bot.inter_kdiag_int_iff <;> assumption)
