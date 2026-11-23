import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPairingStdP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open Classical

noncomputable section

namespace GlobalTheory.ArchConeCont

theorem continuous_omega_coordI : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a'))
    (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W),
    CfgA B G G₁ H H' → IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ (K : Subgroup (UA σ G.V.J)) (y : Fin (b + 2) → AE F E),
      Continuous fun p : KAt K (evI F) × idelesAt E (evI F) =>
        GlobalTheory.ArchUniq.omega (GlobalTheory.ArchUniq.trP F (Fin (b + 2) × Fin (b + 2 + a')))
          (GlobalTheory.ArchUniq.Coord.coordI G.M (shiftA H H' p.2.1))
          (GlobalTheory.ArchUniq.Coord.coordI G.M (Matrix.vecMulVec (mat p.1.1 *ᵥ y) (incV F H'.x))) := by
  intro F E _ _ _ _ _ σ B b a' G G₁ H H' X om om' om₁ om₁' _ _ _ K y
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) (AE F E)
  haveI : IsModuleTopology (AF F) (Matrix (Fin (b + 2)) (Fin (b + 2 + a')) (AE F E)) :=
    (inferInstance : IsModuleTopology (AF F) (Fin (b + 2) → Fin (b + 2 + a') → AE F E))
  have hev : Continuous (evI F) := by
    have h : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
      change Continuous fun x : InfiniteAdeleRing F =>
        ((fun (v : {w : InfinitePlace F // w.IsReal}) => InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2 (x v)),
         (fun (v : {w : InfinitePlace F // w.IsComplex}) => InfinitePlace.Completion.extensionEmbedding v.1 (x v)))
      refine Continuous.prodMk (continuous_pi fun v => ?_) (continuous_pi fun v => ?_)
      · exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp (continuous_apply _)
      · exact (InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp (continuous_apply _)
    exact h.comp continuous_fst
  have hL : Continuous G.M.co.e := IsModuleTopology.continuous_of_linearMap G.M.co.e.toLinearMap
  have hco : Continuous (GlobalTheory.ArchUniq.Coord.coordI G.M) := by
    unfold GlobalTheory.ArchUniq.Coord.coordI GlobalTheory.ArchUniq.locV
    exact (continuous_pi fun i => hev.comp ((continuous_apply i).comp (continuous_fst.comp hL))).prodMk
      (continuous_pi fun i => hev.comp ((continuous_apply i).comp (continuous_snd.comp hL)))
  have htr : Continuous fun q : (Fin (b + 2) × Fin (b + 2 + a') → mixedEmbedding.mixedSpace F) ×
      (Fin (b + 2) × Fin (b + 2 + a') → mixedEmbedding.mixedSpace F) =>
      GlobalTheory.ArchUniq.trP F (Fin (b + 2) × Fin (b + 2 + a')) q.1 q.2 := by
    unfold GlobalTheory.ArchUniq.trP
    exact (LinearMap.continuous_of_finiteDimensional (Algebra.trace ℝ (mixedEmbedding.mixedSpace F))).comp
      (continuous_finset_sum _ fun i _ =>
        ((continuous_apply i).comp continuous_fst).mul ((continuous_apply i).comp continuous_snd))
  have hom : Continuous fun q : ((Fin (b + 2) × Fin (b + 2 + a') → mixedEmbedding.mixedSpace F) ×
      (Fin (b + 2) × Fin (b + 2 + a') → mixedEmbedding.mixedSpace F)) ×
      ((Fin (b + 2) × Fin (b + 2 + a') → mixedEmbedding.mixedSpace F) ×
      (Fin (b + 2) × Fin (b + 2 + a') → mixedEmbedding.mixedSpace F)) =>
      GlobalTheory.ArchUniq.omega (GlobalTheory.ArchUniq.trP F (Fin (b + 2) × Fin (b + 2 + a'))) q.1 q.2 := by
    unfold GlobalTheory.ArchUniq.omega
    exact (htr.comp ((continuous_fst.comp continuous_fst).prodMk (continuous_snd.comp continuous_snd))).sub
      (htr.comp ((continuous_fst.comp continuous_snd).prodMk (continuous_snd.comp continuous_fst)))
  have hmat : Continuous fun g : UA σ G.V.J => mat g := Units.continuous_val.comp continuous_subtype_val
  have h1 : Continuous fun p : KAt K (evI F) × idelesAt E (evI F) => shiftA H H' p.2.1 := by
    unfold shiftA
    exact (Units.continuous_val.comp (continuous_subtype_val.comp continuous_snd)).smul continuous_const
  have h2 : Continuous fun p : KAt K (evI F) × idelesAt E (evI F) => Matrix.vecMulVec (mat p.1.1 *ᵥ y) (incV F H'.x) :=
    Continuous.matrix_vecMulVec
      (Continuous.matrix_mulVec (hmat.comp (continuous_subtype_val.comp continuous_fst)) continuous_const) continuous_const
  have hfin := hom.comp ((hco.comp h1).prodMk (hco.comp h2))
  exact hfin

end GlobalTheory.ArchConeCont

end
