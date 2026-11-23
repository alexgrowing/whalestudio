import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormLeIncInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinHasTemperateGrowth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneModelRestrictionCompatible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchimedeanAdeleCMPrescribedEmbeddingValue
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalCompactOneParameterLinesOfLieLines
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneVectorCcOfSiegelWeil
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.TrSumOf
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.ThK.EvAt0
open GlobalTheory.ThK.EvAt0.PolD

noncomputable section

namespace GlobalTheory.ThK.EvAt0.PlaneQ

section Complex

def qLoc {n : ℕ} (k : ℝ) (J θ : Matrix (Fin n) (Fin n) ℂ) : LinearMap.BilinForm ℝ (Fin n → ℂ) :=
  LinearMap.mk₂ ℝ (fun s t => 2 * k * (s ⬝ᵥ J *ᵥ star (θ *ᵥ t)).re)
    (fun s s' t => by rw [add_dotProduct, Complex.add_re]; ring)
    (fun c s t => by rw [smul_dotProduct, Complex.smul_re, smul_eq_mul, smul_eq_mul]; ring)
    (fun s t t' => by rw [Matrix.mulVec_add, star_add, Matrix.mulVec_add, dotProduct_add, Complex.add_re]; ring)
    (fun c s t => by
      rw [Matrix.mulVec_smul, star_smul, Matrix.mulVec_smul, dotProduct_smul, Complex.smul_re, smul_eq_mul, smul_eq_mul,
        star_trivial]; ring)

end Complex

section Adelic

open scoped Classical
open GlobalTheory.RealLift.KLineProof

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def rho [IsTotallyReal F] (w : InfinitePlace F) : mixedEmbedding.mixedSpace F →ₐ[ℝ] ℝ :=
  (Pi.evalAlgHom ℝ (fun _ : {w : InfinitePlace F // w.IsReal} => ℝ) ⟨w, IsTotallyReal.isReal w⟩).comp (AlgHom.fst ℝ _ _)

theorem trace_rho [IsTotallyReal F] (v : mixedEmbedding.mixedSpace F) :
    Algebra.trace ℝ (mixedEmbedding.mixedSpace F) v = ∑ w, rho w v := by
  haveI : IsEmpty {w : InfinitePlace F // w.IsComplex} :=
    ⟨fun w => InfinitePlace.not_isReal_iff_isComplex.2 w.2 (IsTotallyReal.isReal w.1)⟩
  rw [Algebra.trace_prod_apply, PI.ProdFormulaE.Tr.trace_pi, PI.ProdFormulaE.Tr.trace_pi, Finset.univ_eq_empty (α := {w : InfinitePlace F // w.IsComplex}),
    Finset.sum_empty, add_zero]
  refine Fintype.sum_equiv (Equiv.subtypeUnivEquiv fun w => IsTotallyReal.isReal w) _ _ fun w => ?_
  rw [Algebra.trace_self_apply]
  rfl

theorem rho_evI [IsTotallyReal F] (w : InfinitePlace F) (a : AF F) :
    ((rho w (evI F a) : ℝ) : ℂ) = InfinitePlace.Completion.extensionEmbedding w (evInf F w a) := by
  rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply (IsTotallyReal.isReal w)]
  rfl

theorem piInf_algebraMap [IsTotallyReal F] {w : InfinitePlace F} (τ : EmbOver E w) (a : AF F) :
    piInf τ (algebraMap (AF F) (AE F E) a) = ((rho w (evI F a) : ℝ) : ℂ) := by
  rw [rho_evI]
  change piInf τ (a ⊗ₜ[F] (1 : E)) = _
  rw [piInf_tmul, map_one, mul_one]

theorem piInf_inclR {w : InfinitePlace F} (τ : EmbOver E w) (e : E) :
    piInf τ (inclR (F := F) (AF F) e) = τ.1 e := by
  change piInf τ ((1 : AF F) ⊗ₜ[F] e) = _
  rw [piInf_tmul, map_one, map_one, one_mul]

theorem rho_trace [IsTotallyReal F] {σ : E →ₐ[F] E} (hCM : IsCMExt F E σ) {w : InfinitePlace F} (τ : EmbOver E w)
    (z : AE F E) : rho w (evI F (Algebra.trace (AF F) (AE F E) z)) = 2 * (piInf τ z).re := by
  have h1 : z + cA σ z = algebraMap (AF F) (AE F E) (Algebra.trace (AF F) (AE F E) z) :=
    GlobalTheory.GaussMean.OneVec.add_sigR (AF F) hCM z
  have h2 := congrArg (fun y => (piInf τ y).re) h1
  simp only [map_add, piInf_cA hCM, piInf_algebraMap, Complex.ofReal_re, Complex.add_re] at h2
  rw [← h2]
  simp [two_mul]

def phi [IsTotallyReal F] (h2 : Module.finrank F E = 2) {n : ℕ} {w : InfinitePlace F} (τ : EmbOver E w) :
    (Fin n × Fin 2 → mixedEmbedding.mixedSpace F) →ₗ[ℝ] (Fin n → ℂ) where
  toFun t i := ∑ r, ((rho w (t (i, r)) : ℝ) : ℂ) * piInf τ (tb F E h2 r)
  map_add' t t' := by
    funext i
    simp only [Pi.add_apply, map_add, Complex.ofReal_add, add_mul, Finset.sum_add_distrib]
  map_smul' c t := by
    funext i
    simp only [Pi.smul_apply, map_smul, smul_eq_mul, Complex.ofReal_mul, RingHom.id_apply, Complex.real_smul,
      Finset.mul_sum, mul_assoc]

end Adelic

end GlobalTheory.ThK.EvAt0.PlaneQ
