import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrangianEvaluationGauss
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsArchimedeanPairNegativeSymplecticPairing
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

noncomputable section

namespace GlobalTheory.ThK.EvAt0.PlaneQ

theorem trace_symp_neg_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (τ : ∀ w : InfinitePlace F, EmbOver E w) (n d : ℕ) (JX : Matrix (Fin n) (Fin n) E) (JW : Matrix (Fin d) (Fin d) E)
      (u v : Matrix (Fin n) (Fin d) (AE F E)),
      Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (symp (R := AF F) (cA σ) (-1) (incM F JX) (incM F JW) u v)) =
        ∑ w, -2 * (∑ i, ∑ j, ∑ k, ∑ l, piInf (τ w) (u i j) * (τ w).1 (JX i k) * (τ w).1 (JW j l) *
          star (piInf (τ w) (v k l))).re := by
  intro F E _ _ _ _ _ σ hCM τ n d JX JW u v
  haveI : IsTotallyReal F := hCM.1
  rw [trace_rho]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [symp, rho_trace hCM (τ w)]
  simp only [map_mul, map_neg, map_one, hTens, map_sum, incM, Matrix.map_apply, piInf_inclR,
    GlobalTheory.WrongSignPair.piInf_cA hCM, neg_one_mul, Complex.neg_re]
  ring
