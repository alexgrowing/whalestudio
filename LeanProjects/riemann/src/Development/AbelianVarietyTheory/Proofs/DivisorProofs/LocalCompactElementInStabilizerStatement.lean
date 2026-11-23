import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalCompactElementInStabilizer
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.LeviBlockExponent
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_compact_element_in_stabilizer : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x) (n : ℕ) (W : Spc F E n) (c : E) (hc : c ≠ 0) (v : Pl F) (t : E →ₐ[F] Fv F v)
    (B₀ g : GL (Fin n) (Fv F v)) (x : GLoc σ (c • W.J.map σ) v), IsCompAt σ (c • W.J.map σ) t B₀ g x →
    (toGAd hσ W.J hc).symm (emb σ (c • W.J.map σ) v x) ∈ UAt σ W (evFin F v) ∧
      (mat ((toGAd hσ W.J hc).symm (emb σ (c • W.J.map σ) v x))).map (piW t) = (B₀ * g * B₀⁻¹).1 := by
  first | exact @GlobalTheory.LeviBlockExponentEmbedding.emb_mem_UAt_and_piW | exact GlobalTheory.LeviBlockExponentEmbedding.emb_mem_UAt_and_piW | (intros; apply GlobalTheory.LeviBlockExponentEmbedding.emb_mem_UAt_and_piW <;> assumption)
