import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactSubgroupUnitaryPointsSupportedAtPla
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.LeviBlockExponent
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.LeviBlockExponentEmbedding

theorem emb_mem_UAt_and_piW : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x) (n : ℕ) (W : Spc F E n) (c : E) (hc : c ≠ 0) (v : Pl F) (t : E →ₐ[F] Fv F v)
    (B₀ g : GL (Fin n) (Fv F v)) (x : GLoc σ (c • W.J.map σ) v), IsCompAt σ (c • W.J.map σ) t B₀ g x →
    (toGAd hσ W.J hc).symm (emb σ (c • W.J.map σ) v x) ∈ UAt σ W (evFin F v) ∧
      (mat ((toGAd hσ W.J hc).symm (emb σ (c • W.J.map σ) v x))).map (piW t) = (B₀ * g * B₀⁻¹).1 := by
  intro F E _ _ _ _ _ σ hσ n W c hc v t B₀ g x hx
  have hm : mat ((toGAd hσ W.J hc).symm (emb σ (c • W.J.map σ) v x)) =
      (HA.mat (AF F) σ (c • W.J.map σ) (emb σ (c • W.J.map σ) v x)).1 := by
    have h := toGAd_mat hσ W.J hc ((toGAd hσ W.J hc).symm (emb σ (c • W.J.map σ) v x))
    rw [MulEquiv.apply_symm_apply] at h
    exact (congrArg Units.val h).symm
  refine ⟨fun u hu => ?_, ?_⟩
  · rw [hm]
    exact GlobalTheory.SmallAtPlace.smul_mat_emb_sub_one σ (c • W.J.map σ) v x hu
  · have hx' : (matHom _ σ _ x).1.map (splitProj t) = (B₀ * g * B₀⁻¹).1 := hx
    rw [hm, ← hx']
    have hp := matHom_proj σ (c • W.J.map σ) v (emb σ (c • W.J.map σ) v x)
    rw [proj_emb_self] at hp
    rw [hp]
    ext r s
    rfl

end GlobalTheory.LeviBlockExponentEmbedding
