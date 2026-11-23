import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegFamConst
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelEisensteinDoubled
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactOfIsStabSkew
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling

noncomputable section
namespace GlobalTheory.DblStabSkew

theorem isCompact_of_isStab_dbl : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (n r s : ℕ) (W : Spc F E n), W.IsSkew σ B r s →
    ∀ W₂ : Spc F E (n + n), W₂.J = dblGram finSumFinEquiv W.J → W₂.L = sumLat finSumFinEquiv W.L W.L →
    (∀ w, W₂.θ w = blkMat finSumFinEquiv (W.θ w) (-W.θ w)) →
    ∀ K : Subgroup (UA σ W₂.J), IsStab B K → IsCompact (K : Set (UA σ W₂.J)) := by
  intro _ F E _ _ _ _ _ σ B hB n r s W hW W₂ hJ hL hθ K hK
  have hL₂ : W₂.L.IsLattice E := by rw [hL]; haveI : Submodule.IsLattice E W.L := hW.lat; infer_instance
  have hθ₂ : ∀ w, IsCartan (Complex.I • W₂.J.map (B.emb w).1) (W₂.θ w) := by
    intro w
    rw [hθ w, hJ, dblGram, blkMat_map _ _ (map_zero _), Matrix.map_neg _ (map_neg _), GlobalTheory.DblUnfoldCont.smul_blkMat, smul_neg]
    exact GlobalTheory.DblUnfoldCont.isCartan_dbl _ _ (hW.cartan w)
  exact GlobalTheory.DblUnfoldCont.isCompact_of_isStab_skew hB.cm B W₂ hL₂ hθ₂ hK

end GlobalTheory.DblStabSkew
