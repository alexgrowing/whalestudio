import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegFamConst
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelEisensteinDoubled
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelWeilAnisotropicHermitian
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling
noncomputable section

namespace GlobalTheory.DoublingCont

theorem continuous_and_rat : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : ℕ)
    (J : Matrix (Fin d) (Fin d) E) (J₂ : Matrix (Fin (d + d)) (Fin (d + d)) E),
    ∀ i : UA σ J × UA σ J →* UA σ J₂, (∀ h h', mat (i (h, h')) = blkMat finSumFinEquiv (mat h) (mat h')) →
      Continuous i ∧ ∀ δ ∈ ratU σ J, i (1, δ) ∈ ratU σ J₂ := by
  intro F E _ _ _ _ _ σ d J J₂ i hi
  refine ⟨?_, ?_⟩
  ·
    have hb : Continuous fun p : Matrix (Fin d) (Fin d) (AE F E) × Matrix (Fin d) (Fin d) (AE F E) =>
        blkMat finSumFinEquiv p.1 p.2 :=
      (continuous_fst.matrix_fromBlocks continuous_const continuous_const continuous_snd).matrix_submatrix _ _
    have hv : Continuous fun g : UA σ J => ((g.1 : GL (Fin d) (AE F E)) : Matrix (Fin d) (Fin d) (AE F E)) :=
      Units.continuous_val.comp continuous_subtype_val
    have hw : Continuous fun g : UA σ J => (((g.1 : GL (Fin d) (AE F E))⁻¹ : GL (Fin d) (AE F E)) :
        Matrix (Fin d) (Fin d) (AE F E)) :=
      Units.continuous_coe_inv.comp continuous_subtype_val
    refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _
    · have : (fun x : UA σ J × UA σ J => (((i x).1 : GL (Fin (d + d)) (AE F E)) : Matrix (Fin (d + d)) (Fin (d + d)) (AE F E))) =
          fun x => blkMat finSumFinEquiv ((x.1.1 : GL (Fin d) (AE F E)) : Matrix (Fin d) (Fin d) (AE F E))
            ((x.2.1 : GL (Fin d) (AE F E)) : Matrix (Fin d) (Fin d) (AE F E)) := by
        funext x; exact hi x.1 x.2
      have key := hb.comp ((hv.comp continuous_fst).prodMk (hv.comp continuous_snd))
      exact (continuous_congr fun x => (congrFun this x).symm).1 key
    · have : (fun x : UA σ J × UA σ J => ((((i x).1 : GL (Fin (d + d)) (AE F E))⁻¹ : GL (Fin (d + d)) (AE F E)) :
            Matrix (Fin (d + d)) (Fin (d + d)) (AE F E))) =
          fun x => blkMat finSumFinEquiv (((x.1.1 : GL (Fin d) (AE F E))⁻¹ : GL _ (AE F E)) : Matrix (Fin d) (Fin d) (AE F E))
            (((x.2.1 : GL (Fin d) (AE F E))⁻¹ : GL _ (AE F E)) : Matrix (Fin d) (Fin d) (AE F E)) := by
        funext x
        have h1 := hi x⁻¹.1 x⁻¹.2
        rw [Prod.mk.eta, map_inv] at h1
        exact h1
      have key := hb.comp ((hw.comp continuous_fst).prodMk (hw.comp continuous_snd))
      exact (continuous_congr fun x => (congrFun this x).symm).1 key
  · intro δ hδ
    obtain ⟨g, hg⟩ := MonoidHom.mem_range.1 (Subgroup.mem_subgroupOf.1 hδ)
    refine Subgroup.mem_subgroupOf.2 (MonoidHom.mem_range.2 ⟨blkGL finSumFinEquiv ((1 : GL (Fin d) E), g), ?_⟩)
    apply Units.ext
    change ((blkGL finSumFinEquiv ((1 : GL (Fin d) E), g) : GL _ E) : Matrix _ _ E).map (inclR (AF F)) = mat (i (1, δ))
    rw [val_blkGL, blkMat_map _ _ (map_zero _), hi]
    have h1 : mat δ = (g : Matrix _ _ E).map (inclR (AF F)) := by
      show δ.1.val = _
      rw [← hg]; rfl
    rw [h1]
    rw [Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
    rfl

end GlobalTheory.DoublingCont
