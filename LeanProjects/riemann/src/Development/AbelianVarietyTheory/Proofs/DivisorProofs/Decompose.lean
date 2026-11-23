import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrPApply
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ArchSch

noncomputable section

namespace GlobalTheory.ThK.DecW

theorem decompose : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} (B : Base F E)
    {n d d₁ : ℕ} (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (r' s' i₀ i₁ : ℕ),
    W.IsSkew σ B r' s' → H'.IsAdapted σ B W W₁ i₀ i₁ → ∀ w : Matrix (Fin n) (Fin d) (AE F E), At (evI F) w →
    ∃ (a b : Fin n → AE F E) (z : Matrix (Fin n) (Fin d₁) (AE F E)), At (evI F) a ∧ At (evI F) b ∧ At (evI F) z ∧
      w = Matrix.vecMulVec a (incV F H'.x) + incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ +
        Matrix.vecMulVec b (incV F H'.y) := by
  intro F E _ _ _ _ _ σ B n d d₁ W W₁ H' r' s' i₀ i₁ hW hH w hw
  have key : ∀ v : Fin d → E, ∃ (s t : E) (u : Fin d₁ → E), v = s • H'.x + H'.ι *ᵥ u + t • H'.y := by
    intro v
    let f : (E × (Fin d₁ → E) × E) →ₗ[E] (Fin d → E) :=
      (LinearMap.fst E E ((Fin d₁ → E) × E)).smulRight H'.x +
        (Matrix.mulVecLin H'.ι).comp ((LinearMap.fst E (Fin d₁ → E) E).comp (LinearMap.snd E E ((Fin d₁ → E) × E))) +
        ((LinearMap.snd E (Fin d₁ → E) E).comp (LinearMap.snd E E ((Fin d₁ → E) × E))).smulRight H'.y
    have hf : ∀ s u t, f (s, u, t) = s • H'.x + H'.ι *ᵥ u + t • H'.y := fun s u t => by
      simp [f, LinearMap.smulRight_apply]
    have hle : Submodule.span E (W.L : Set (Fin d → E)) ≤ LinearMap.range f := by
      rw [Submodule.span_le]
      intro z hz
      obtain ⟨s, t, u, -, -, -, rfl⟩ := hH.split z hz
      exact ⟨(s, u, t), hf s u t⟩
    haveI := hW.lat
    have hv : v ∈ Submodule.span E (W.L : Set (Fin d → E)) := by
      rw [Submodule.IsLattice.span_eq_top (A := E) (M := W.L)]; trivial
    obtain ⟨⟨s, u, t⟩, h⟩ := hle hv
    exact ⟨s, t, u, by rw [← h, hf]⟩
  choose s t u hsu using fun j : Fin d => key (Pi.single j 1)
  have hI : (1 : Matrix (Fin d) (Fin d) E) =
      Matrix.vecMulVec s H'.x + Matrix.of u * H'.ιᵀ + Matrix.vecMulVec t H'.y := by
    ext j l
    have := congrFun (hsu j) l
    simp only [Pi.single_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct] at this
    simp only [Matrix.one_apply, Matrix.add_apply, Matrix.vecMulVec_apply, Matrix.mul_apply, Matrix.of_apply,
      Matrix.transpose_apply]
    have e : (if j = l then (1:E) else 0) = if l = j then 1 else 0 := by
      by_cases h : j = l <;> simp [h, eq_comm]
    rw [e, this]
    congr 2
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  have h0 : ∀ c : AF F, evI F c = 0 → ∀ i j, c • w i j = 0 := fun c hc i j => by
    simpa using congrFun (congrFun (hw c hc) i) j
  have hAt : ∀ v : Fin d → AE F E, At (evI F) (w *ᵥ v) := by
    intro v c hc; funext i
    simp only [Pi.smul_apply, Matrix.mulVec, dotProduct, Finset.smul_sum, ← smul_mul_assoc, h0 c hc, zero_mul,
      Finset.sum_const_zero, Pi.zero_apply]
  refine ⟨w *ᵥ incV F s, w *ᵥ incV F t, w * incM F (Matrix.of u), hAt _, hAt _, ?_, ?_⟩
  · intro c hc; ext i k
    simp only [Matrix.smul_apply, Matrix.mul_apply, Finset.smul_sum, ← smul_mul_assoc, h0 c hc, zero_mul,
      Finset.sum_const_zero, Matrix.zero_apply]
  · have hI' := congrArg (incM F) hI
    have e1 : incM F (1 : Matrix (Fin d) (Fin d) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
    have e1n : incM F (1 : Matrix (Fin n) (Fin n) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
    have e2 : incM F (Matrix.vecMulVec s H'.x + Matrix.of u * H'.ιᵀ + Matrix.vecMulVec t H'.y) =
        Matrix.vecMulVec (incV F s) (incV F H'.x) + incM F (Matrix.of u) * (incM F H'.ι)ᵀ +
          Matrix.vecMulVec (incV F t) (incV F H'.y) := by
      ext i j
      simp [incM, incV, Matrix.vecMulVec_apply, Matrix.mul_apply, map_sum, map_add, map_mul]
    rw [e1, e2] at hI'
    rw [e1n, Matrix.one_mul]
    conv_lhs => rw [← Matrix.mul_one w, hI']
    have hv : ∀ a b : Fin d → AE F E, w * Matrix.vecMulVec a b = Matrix.vecMulVec (w *ᵥ a) b := by
      intro a b; ext i l
      simp [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct, Finset.sum_mul, mul_assoc]
    rw [Matrix.mul_add, Matrix.mul_add, hv, hv, Matrix.mul_assoc]

end GlobalTheory.ThK.DecW
