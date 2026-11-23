import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousLeviIdeleHomExists
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalCompactOneParameterLinesOfLieLines
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchimedeanAdeleCMPrescribedEmbeddingValue
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartanCompatibleTransitive
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
open GlobalTheory.Doubling (absE)

open scoped TensorProduct NNReal Matrix

noncomputable section

namespace GlobalTheory.IwaAdelicIso

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

variable (F E) in

def infIdeal : Ideal (AE F E) where
  carrier := {z | At (evI F) z}
  zero_mem' := fun u _ => smul_zero u
  add_mem' := fun ha hb u hu => by rw [smul_add, ha u hu, hb u hu, add_zero]
  smul_mem' := fun c z hz u hu => by
    show u • (c • z) = 0
    rw [smul_eq_mul, ← mul_smul_comm, hz u hu, mul_zero]

theorem piInf_inclR {w : InfinitePlace F} (τ : EmbOver E w) (e : E) : piInf τ (inclR (F := F) (AF F) e) = τ.1 e := by
  rw [show inclR (F := F) (AF F) e = (1 : AF F) ⊗ₜ[F] e from rfl, GlobalTheory.RealLift.KLineProof.piInf_tmul, map_one, map_one, one_mul]

end GlobalTheory.IwaAdelicIso

namespace GlobalTheory.IwaAdelicIso

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem form_map {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) (τ : E →+* ℂ) {d : ℕ} (J : Matrix (Fin d) (Fin d) E) (a b : Fin d → E) :
    (fun i => τ (a i)) ⬝ᵥ J.map τ *ᵥ star (fun i => τ (b i)) = τ (form σ J a b) := by
  simp [form, dotProduct, Matrix.mulVec, map_sum, map_mul, ← hcm.2.2.2]

end GlobalTheory.IwaAdelicIso
