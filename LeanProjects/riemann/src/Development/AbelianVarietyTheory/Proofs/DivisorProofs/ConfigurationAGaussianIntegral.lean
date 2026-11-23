import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFinsetOfEventually
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LintegralFintypeProdEqProd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdemSmulUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DOpMemDStep
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchimedeanAdeleCMPrescribedEmbeddingValue
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealScalarArchimedeanAdeleSmulMatrixRealPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinHasTemperateGrowth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHermitianCartanInvolutionSystemsConjugateArc
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.ConeEuler
open GlobalTheory.ThK.EvAt0.PolD GlobalTheory.ArchUniq GlobalTheory.ArchUniq.Coord
open GlobalTheory.Doubling (absE absEv unitFin ideleAt)
open Classical

noncomputable section

namespace GlobalTheory.ThK.VacDualPart

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem conj_vecMulVec {m k : Type} [Fintype m] [Fintype k] (A : Matrix m m ℂ) (B : Matrix k k ℂ) (a : m → ℂ)
    (b : k → ℂ) : A * Matrix.vecMulVec a b * Bᵀ = Matrix.vecMulVec (A *ᵥ a) (B *ᵥ b) := by
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_transpose]

theorem map_vecMulVec {m k : Type} (f : AE F E →+* ℂ) (a : m → AE F E) (b : k → AE F E) :
    (Matrix.vecMulVec a b).map f = Matrix.vecMulVec (fun i => f (a i)) (fun j => f (b j)) := by
  ext i j; simp [Matrix.vecMulVec_apply]

theorem map_mulVec' {m k : Type} [Fintype k] (f : AE F E →+* ℂ) (A : Matrix m k (AE F E)) (z : k → AE F E) :
    (fun i => f ((A *ᵥ z) i)) = A.map f *ᵥ fun j => f (z j) := by
  funext i; exact RingHom.map_mulVec f A z i

theorem piInf_incV {n : ℕ} {w : InfinitePlace F} (τ : EmbOver E w) (x : Fin n → E) :
    (fun i => piInf τ (incV F x i)) = fun i => τ.1 (x i) := by
  funext i
  have := congrFun (congrFun (GlobalTheory.CartanConjSkew.incM_map_piInf (F := F) (Matrix.replicateCol Unit x) τ) i) ()
  simpa [incM, incV, Matrix.replicateCol] using this

theorem dOp_dual_vac : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a'))
    (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), CfgA B G G₁ H H' → IsTriple B G X om om' →
    ∀ g, GaussD G.M B.emb g → ∀ (y : Fin (b + 2) → AE F E) (z : Fin (b + a') → AE F E),
      ∃ (y₁ : Fin (b + 2) → AE F E) (z₁ : Fin (b + a') → AE F E),
        dOp (coordI G.M (Matrix.vecMulVec y (incV F H'.y) + Matrix.vecMulVec (incV F H.y) (incM F H'.ι *ᵥ z))).1
          (coordI G.M (Matrix.vecMulVec y (incV F H'.y) + Matrix.vecMulVec (incV F H.y) (incM F H'.ι *ᵥ z))).2 g =
        (-Complex.I) • dOp (coordI G.M (Matrix.vecMulVec y₁ (incV F H'.x) + Matrix.vecMulVec (incV F H.x) (incM F H'.ι *ᵥ z₁))).1
          (coordI G.M (Matrix.vecMulVec y₁ (incV F H'.x) + Matrix.vecMulVec (incV F H.x) (incM F H'.ι *ᵥ z₁))).2 g := by
  intro F E _ _ _ _ _ σ B b a' G G₁ H H' X om om' hC hT g hg y z
  obtain ⟨ε, hε⟩ := hg
  have hcm := hT.base.cm
  choose c hc0 hc using fun w => (hC.hH.cartan w).2
  choose c' hc'0 hc' using fun w => (hC.hH'.cartan w).2
  choose y₁ hy₁ using fun i => GlobalTheory.PolRangeInf.exists_at_inf_values hcm B.emb
    (fun w => ((((ε w : ℤ) : ℂ) * Complex.I * c' w) • (G.V.θ w *ᵥ fun j => piInf (B.emb w) (y j))) i)
  choose z₁ hz₁ using fun i => GlobalTheory.PolRangeInf.exists_at_inf_values hcm B.emb
    (fun w => ((((ε w : ℤ) : ℂ) * Complex.I * c w) • (G₁.W.θ w *ᵥ fun j => piInf (B.emb w) (z j))) i)
  refine ⟨y₁, z₁, ?_⟩
  set U := Matrix.vecMulVec y (incV F H'.y) + Matrix.vecMulVec (incV F H.y) (incM F H'.ι *ᵥ z) with hU
  set U' := Matrix.vecMulVec y₁ (incV F H'.x) + Matrix.vecMulVec (incV F H.x) (incM F H'.ι *ᵥ z₁) with hU'
  have hat : ∀ V : Matrix (Fin (b + 2)) (Fin (b + 2 + a')) (AE F E), At (evI F) (realAd F 1 • V) := fun V c hc => by
    rw [smul_smul, mul_realAd_eq_zero c hc, zero_smul]
  have hmap : ∀ w, (realAd F 1 • U').map (piInf (B.emb w)) =
      (((ε w : ℤ) : ℂ) * Complex.I) • (G.V.θ w * (realAd F 1 • U).map (piInf (B.emb w)) * (G.W.θ w)ᵀ) := by
    intro w
    rw [GlobalTheory.RealScalar.realAd_smul_map σ B.emb hcm, GlobalTheory.RealScalar.realAd_smul_map σ B.emb hcm, Complex.ofReal_one,
      one_smul, one_smul]
    have eY : (fun i => piInf (B.emb w) (y₁ i)) =
        (((ε w : ℤ) : ℂ) * Complex.I * c' w) • (G.V.θ w *ᵥ fun j => piInf (B.emb w) (y j)) :=
      funext fun i => (hy₁ i).2 w
    have eZ : (fun i => piInf (B.emb w) (z₁ i)) =
        (((ε w : ℤ) : ℂ) * Complex.I * c w) • (G₁.W.θ w *ᵥ fun j => piInf (B.emb w) (z j)) :=
      funext fun i => (hz₁ i).2 w
    have θV2 : G.V.θ w * G.V.θ w = 1 := (hT.geo.hV.cartan w).1
    have θW2 : G.W.θ w * G.W.θ w = 1 := (hT.geo.hW.cartan w).1
    have eι := (hC.hH'.cartan w).1
    simp only [hU, hU', Matrix.map_add _ (map_add _), map_vecMulVec, map_mulVec', piInf_incV,
      GlobalTheory.CartanConjSkew.incM_map_piInf, eY, eZ, Matrix.mul_add, Matrix.add_mul, conj_vecMulVec, hc w, hc' w,
      Matrix.mulVec_smul, Matrix.mulVec_mulVec, θV2, θW2, Matrix.one_mulVec, eι, smul_add]
    simp only [Matrix.smul_vecMulVec, Matrix.vecMulVec_smul, smul_smul]
  have key := hε (realAd F 1 • U) (realAd F 1 • U') (hat U) (hat U') hmap
  change dOp (coordI G.M (realAd F 1 • U')).1 (coordI G.M (realAd F 1 • U')).2 g =
    Complex.I • dOp (coordI G.M (realAd F 1 • U)).1 (coordI G.M (realAd F 1 • U)).2 g at key
  rw [coordI_one, coordI_one] at key
  rw [key, smul_smul]
  simp

end GlobalTheory.ThK.VacDualPart
