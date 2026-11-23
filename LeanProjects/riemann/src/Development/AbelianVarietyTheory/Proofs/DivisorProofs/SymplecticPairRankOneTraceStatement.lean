import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticPairRankOneTrace
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
theorem _root_.GlobalTheory.T.symplectic_pair_rank_one_trace : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n d : ℕ} (J : Matrix (Fin n) (Fin n) E) (K : Matrix (Fin d) (Fin d) E)
    (ξ β : Fin n → E) (x y : Fin d → E) (t : AF F),
    symp (cA σ) (-1) (incM F J) (incM F K) (Matrix.vecMulVec (incV F ξ) (incV F y))
      (Matrix.vecMulVec (t • incV F β) (incV F x)) =
      t * algebraMap F (AF F) (Algebra.trace F E (-(form σ J ξ β * form σ K y x))) := by
  first | exact @GlobalTheory.SympPure.symp_pure | exact GlobalTheory.SympPure.symp_pure | (intros; apply GlobalTheory.SympPure.symp_pure <;> assumption)
