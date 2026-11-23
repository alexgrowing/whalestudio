import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceNondegeneratePartialFourierIntegral
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AvgFormApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaDiagInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSchwartzNe

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_nondegenerate_partial_fourier_integral : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (κ κa κb : Type) [Fintype κ] [Fintype κa] [Fintype κb] (ε : κ ≃ κa ⊕ (κb ⊕ κb)) (C : Matrix κa (Fin n) E),
    (∀ z : Fin n → E, (∀ k, ∑ j, Algebra.trace F E (C k j * z j) = 0) → z = 0) →
    ∀ μ₁ : @Measure (κb → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ₁ →
    ∀ μ : @Measure (Fin n → AE F E) (borel _), GlobalTheory.SiegelAvg.IsHaarB μ →
      (∀ Ψ ∈ schA F κ, (letI : MeasurableSpace (Fin n → AE F E) := borel _;
        Integrable (fun y => GlobalTheory.DiagSiegel.diagInt μ₁ (fun v => Ψ (GlobalTheory.ThK.Adapt.glue ε
          (fun k => ∑ j, Algebra.trace (AF F) (AE F E) (inclR (F := F) (AF F) (C k j) * y j)) v))) μ)) ∧
      ∃ Λ ∈ (adeleClass F).adm κ, ∀ Ψ ∈ schA F κ, Λ Ψ = (letI : MeasurableSpace (Fin n → AE F E) := borel _;
        ∫ y, GlobalTheory.DiagSiegel.diagInt μ₁ (fun v => Ψ (GlobalTheory.ThK.Adapt.glue ε
          (fun k => ∑ j, Algebra.trace (AF F) (AE F E) (inclR (F := F) (AF F) (C k j) * y j)) v)) ∂μ) := by
  first | exact @GlobalTheory.SubspaceInt.integrable_and_adm | exact GlobalTheory.SubspaceInt.integrable_and_adm | (intros; apply GlobalTheory.SubspaceInt.integrable_and_adm <;> assumption)
