import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalEmbeddingRangeCharacterization
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAtAlt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaIsotropicStabilizerInertPlace
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_embedding_range_characterization : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (v : Pl F) (g : GAd σ J), g ∈ (emb σ J v).range ↔
      ∀ u : AF F, evFin F v u = 0 → u • ((HA.mat (AF F) σ J g : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) - 1) = 0 := by
  first | exact @GlobalTheory.AdelicPointsAt.range_emb_iff_smul | exact GlobalTheory.AdelicPointsAt.range_emb_iff_smul | (intros; apply GlobalTheory.AdelicPointsAt.range_emb_iff_smul <;> assumption)
