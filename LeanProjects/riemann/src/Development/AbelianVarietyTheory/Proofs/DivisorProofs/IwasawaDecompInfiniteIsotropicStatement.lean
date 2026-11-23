import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IwasawaDecompInfiniteIsotropic
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iwasawa_decomp_infinite_isotropic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) {n : ℕ} (W : Spc F E n) (r s : ℕ) (x : Fin n → E), IsCMExt F E σ → W.IsSkew σ B r s → x ≠ 0 →
    form σ W.J x x = 0 → ∀ g ∈ UAt σ W (evI F), ∃ (p : UA σ W.J) (t : (AE F E)ˣ), mat p *ᵥ incV F x = t.1 • incV F x ∧
      ∃ k ∈ KInf σ W B.emb, g = p * k := by
  first | exact @GlobalTheory.ArchIwasawaLine.arch_iwasawa_line | exact GlobalTheory.ArchIwasawaLine.arch_iwasawa_line | (intros; apply GlobalTheory.ArchIwasawaLine.arch_iwasawa_line <;> assumption)
