import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabiliserArchFiniteDecomposition
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAut
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegFamOfContinuousAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoxC
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling GlobalTheory.ThK.DblKer
open GlobalTheory.DblDatum
open GlobalTheory.DblDatum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stabiliser_arch_finite_decomposition : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n : ℕ) (X : Spc F E n) (K : Subgroup (UA σ X.J)), IsStab B K →
    ∀ k ∈ K, ∃ a ∈ KInf σ X B.emb, ∃ f ∈ K, f ∈ UAt σ X (sndA F) ∧ k = a * f := by
  first | exact @GlobalTheory.DblDatum.StabDec.exists_kInf_mul_fin | exact GlobalTheory.DblDatum.StabDec.exists_kInf_mul_fin | (intros; apply GlobalTheory.DblDatum.StabDec.exists_kInf_mul_fin <;> assumption)
