import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFinsetOfEventually
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LintegralFintypeProdEqProd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdemSmulUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DOpMemDStep
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.ConeEuler
open GlobalTheory.ThK.EvAt0.PolD GlobalTheory.ArchUniq GlobalTheory.ArchUniq.Coord
open GlobalTheory.Doubling (absE absEv unitFin ideleAt)
open Classical

noncomputable section

namespace GlobalTheory.ThK.VacImg

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem incM_map_piInf_emb {n m : Type} (J : Matrix n m E) {w : InfinitePlace F} (τ : EmbOver E w) :
    (incM F J).map (piInf τ) = J.map τ.1 := by
  ext i j
  simp [incM, piInf, compInf, inclR, infEmb_tmul]

theorem at_sandwich {n n₁ d d₁ : ℕ} (P : Matrix (Fin n) (Fin n₁) (AE F E)) (Q : Matrix (Fin d) (Fin d₁) (AE F E))
    (z : Matrix (Fin n₁) (Fin d₁) (AE F E)) (hz : At (evI F) z) : At (evI F) (P * z * Qᵀ) := by
  intro a ha
  rw [← Matrix.smul_mul, ← Matrix.mul_smul, hz a ha, Matrix.mul_zero, Matrix.zero_mul]

theorem map_sandwich {n n₁ d d₁ : ℕ} (P : Matrix (Fin n) (Fin n₁) (AE F E)) (Q : Matrix (Fin d) (Fin d₁) (AE F E))
    (z : Matrix (Fin n₁) (Fin d₁) (AE F E)) (φ : AE F E →+* ℂ) :
    (P * z * Qᵀ).map φ = P.map φ * z.map φ * (Q.map φ)ᵀ := by
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]

theorem gaussD_of_inter {σ : E →ₐ[F] E} (B : Base F E) {n n₁ d d₁ : ℕ} {X : Spc F E n} {W : Spc F E d}
    {X₁ : Spc F E n₁} {W₁ : Spc F E d₁} (M : Model σ X W) (M₁ : Model σ X₁ W₁)
    (ι : Matrix (Fin n) (Fin n₁) E) (ι' : Matrix (Fin d) (Fin d₁) E)
    (hι : ∀ w, X.θ w * ι.map (B.emb w).1 = ι.map (B.emb w).1 * X₁.θ w)
    (hι' : ∀ w, W.θ w * ι'.map (B.emb w).1 = ι'.map (B.emb w).1 * W₁.θ w)
    (ei : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n₁ × Fin d₁))
    (hint : ∀ (z : Matrix (Fin n₁) (Fin d₁) (AE F E)) (f : SInf F (Fin n × Fin d)),
      ei (dOp (coordI M (incM F ι * z * (incM F ι')ᵀ)).1 (coordI M (incM F ι * z * (incM F ι')ᵀ)).2 f) =
        dOp (coordI M₁ z).1 (coordI M₁ z).2 (ei f))
    (g : SInf F (Fin n × Fin d)) (hg : GaussD M B.emb g) : GaussD M₁ B.emb (ei g) := by
  obtain ⟨ε, hε⟩ := hg
  refine ⟨ε, fun u₁ u₁' hu₁ hu₁' hrel => ?_⟩
  have key := hε (incM F ι * u₁ * (incM F ι')ᵀ) (incM F ι * u₁' * (incM F ι')ᵀ)
    (at_sandwich _ _ _ hu₁) (at_sandwich _ _ _ hu₁') (fun w => ?_)
  · change dOp (coordI M₁ u₁').1 (coordI M₁ u₁').2 (ei g) = Complex.I • dOp (coordI M₁ u₁).1 (coordI M₁ u₁).2 (ei g)
    rw [← hint, ← hint]
    change ei (dOp (arc (M.co.e (incM F ι * u₁' * (incM F ι')ᵀ)).1) (arc (M.co.e (incM F ι * u₁' * (incM F ι')ᵀ)).2) g) =
      Complex.I • ei (dOp (arc (M.co.e (incM F ι * u₁ * (incM F ι')ᵀ)).1) (arc (M.co.e (incM F ι * u₁ * (incM F ι')ᵀ)).2) g)
    rw [key, map_smul]
  · rw [map_sandwich, map_sandwich, incM_map_piInf_emb, incM_map_piInf_emb, hrel w, Matrix.mul_smul, Matrix.smul_mul]
    congr 1
    have e1 := hι w
    have e2 := congrArg Matrix.transpose (hι' w)
    rw [Matrix.transpose_mul, Matrix.transpose_mul] at e2
    calc ι.map (B.emb w).1 * (X₁.θ w * u₁.map (piInf (B.emb w)) * (W₁.θ w)ᵀ) * (ι'.map (B.emb w).1)ᵀ
        = (ι.map (B.emb w).1 * X₁.θ w) * u₁.map (piInf (B.emb w)) * ((W₁.θ w)ᵀ * (ι'.map (B.emb w).1)ᵀ) := by
          simp only [Matrix.mul_assoc]
      _ = (X.θ w * ι.map (B.emb w).1) * u₁.map (piInf (B.emb w)) * ((ι'.map (B.emb w).1)ᵀ * (W.θ w)ᵀ) := by
          rw [← e1, ← e2]
      _ = _ := by simp only [Matrix.mul_assoc]

end GlobalTheory.ThK.VacImg
