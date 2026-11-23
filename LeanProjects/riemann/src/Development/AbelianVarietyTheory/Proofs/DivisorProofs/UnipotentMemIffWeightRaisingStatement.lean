import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentMemIffWeightRaising
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Idem3
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotropicUnipotentRadicalsRationalCocompact

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.UnipHaar GlobalTheory.Mem.UnipCocompact
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotent_mem_iff_weight_raising : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n n₁ : ℕ) (W : Spc F E n) (W₁ : Spc F E n₁) (H : Plane E n n₁) (i₀ i₁ r s r₁ s₁ : ℕ), B.IsGood σ → W.IsSkew σ B r s → W₁.IsSkew σ B r₁ s₁ → H.IsAdapted σ B W W₁ i₀ i₁ → ∀ u : UA σ W.J, u ∈ unip σ W H ↔ mat u - 1 ∈ raise (idem3 σ W.J H) wt3 0 := by
  first | exact @GlobalTheory.UnipHaar.RadMem.mem_unip_iff_raise | exact GlobalTheory.UnipHaar.RadMem.mem_unip_iff_raise | (intros; apply GlobalTheory.UnipHaar.RadMem.mem_unip_iff_raise <;> assumption)
