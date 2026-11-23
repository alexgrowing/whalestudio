import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabilizerEigenvectorIdeleAbsolute
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stabilizer_eigenvector_idele_absolute : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ)
    (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    B.IsGood σ → G.IsGood B → ∀ (K : Subgroup (UA σ G.V.J)), IsStab B K →
    ∀ k ∈ KAt K (evI F), ∀ t ∈ idelesAt E (evI F), mat k *ᵥ incV F H.x = t.1 • incV F H.x → absE F E t = 1 := by
  first | exact @GlobalTheory.ThK.absE_eq_one_of_KInf_eigen | exact GlobalTheory.ThK.absE_eq_one_of_KInf_eigen | (intros; apply GlobalTheory.ThK.absE_eq_one_of_KInf_eigen <;> assumption)
