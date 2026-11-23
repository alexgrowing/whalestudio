import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianDualLatticeDenominator
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Classical

noncomputable section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_dual_lattice_denominator : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (hJ : J.det ≠ 0) (c : E) (hc : c ≠ 0),
    ∃ N : ℕ, 1 ≤ N ∧ ∀ ξ : Fin n → E, (∀ β : Fin n → 𝓞 E, ∃ z : ℤ, Algebra.trace ℚ E (c * form σ J ξ (fun i => (β i : E))) = z) →
      ∀ i, ∃ o : 𝓞 E, (N : E) * ξ i = o := by
  first | exact @GlobalTheory.TraceDenom.nat_mul_integral_of_trace_form_int | exact GlobalTheory.TraceDenom.nat_mul_integral_of_trace_form_int | (intros; apply GlobalTheory.TraceDenom.nat_mul_integral_of_trace_form_int <;> assumption)
