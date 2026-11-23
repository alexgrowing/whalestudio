import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThLiftDef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrongApproximationSplitPlaceSkewHermitianUnitar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPlaceSplitsCompletelyNotMemEmbedding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNormOneIdeles
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LiftConst
namespace GlobalTheory.ThK.LiftConst

theorem det_mul_conj_det_eq_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n : ℕ) (V : Spc F E n) (r s : ℕ), V.IsHerm σ B r s → ∀ g : UA σ V.J, (mat g).det * cA σ (mat g).det = 1 := by
  intro F E _ _ _ _ _ σ B n V r s hV g
  have hg : (g.1.1)ᵀ * incM F V.J * (g.1.1).map (cA σ) = incM F V.J := g.2
  have hd := congrArg Matrix.det hg
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at hd
  have hmap : ((g.1.1).map (cA σ)).det = cA σ (g.1.1).det :=
    ((RingHom.map_det (cA σ).toRingHom (g.1.1)).symm)
  have hinc : (incM F V.J).det = inclR (F := F) (AF F) V.J.det :=
    ((RingHom.map_det (inclR (F := F) (AF F)) V.J).symm)
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hJ : V.J.det ≠ 0 :=
    GlobalTheory.SplitApprox.det_ne_zero_of_map V.J (B.emb w).1 (GlobalTheory.SplitApprox.det_ne_zero_of_hasSig (hV.sig w))
  have hu : IsUnit (incM F V.J).det := by
    rw [hinc]; exact (isUnit_iff_ne_zero.mpr hJ).map _
  rw [hmap] at hd
  show (g.1.1).det * cA σ (g.1.1).det = 1
  apply hu.mul_left_injective
  simp only
  linear_combination hd

end GlobalTheory.ThK.LiftConst
