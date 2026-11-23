import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOfMemSchA
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairDoubleDescentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviEmbeddingExistsDoublingConfiguration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeviElementSkewGood
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPairOfIsTriple

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThK.WeilEvExch

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem mat_inv_mul {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) : mat g⁻¹ * mat g = 1 := by
  show (g.1⁻¹ * g.1 : GL _ _).1 = 1
  simp

theorem mat_mul_inv {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) : mat g * mat g⁻¹ = 1 := by
  show (g.1 * g.1⁻¹ : GL _ _).1 = 1
  simp

theorem levi_inv {n n₁ : ℕ} {W : Spc F E n} {W₁ : Spc F E n₁} {H : Plane E n n₁}
    {γ : UA σ W₁.J} {m : UA σ W.J} (h : IsLevi (W₁ := W₁) H 1 γ m) :
    mat m⁻¹ *ᵥ incV F H.x = incV F H.x ∧ mat m⁻¹ * incM F H.ι = incM F H.ι * mat γ⁻¹ := by
  have h1 : mat m *ᵥ incV F H.x = incV F H.x := by simpa using h.1
  refine ⟨?_, ?_⟩
  · conv_lhs => rw [← h1]
    rw [Matrix.mulVec_mulVec, mat_inv_mul, Matrix.one_mulVec]
  · calc mat m⁻¹ * incM F H.ι = mat m⁻¹ * incM F H.ι * (mat γ * mat γ⁻¹) := by rw [mat_mul_inv, Matrix.mul_one]
      _ = mat m⁻¹ * (incM F H.ι * mat γ) * mat γ⁻¹ := by simp only [Matrix.mul_assoc]
      _ = mat m⁻¹ * (mat m * incM F H.ι) * mat γ⁻¹ := by rw [h.2.2]
      _ = incM F H.ι * mat γ⁻¹ := by rw [← Matrix.mul_assoc (mat m⁻¹), mat_inv_mul, Matrix.one_mul]

theorem mul_vecMulVec' {R : Type} [CommRing R] {k l p : ℕ} (A : Matrix (Fin l) (Fin k) R)
    (a : Fin k → R) (b : Fin p → R) : A * Matrix.vecMulVec a b = Matrix.vecMulVec (A *ᵥ a) b := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct, Finset.sum_mul]
  exact Finset.sum_congr rfl fun x _ => by ring

theorem vecMulVec_mul_transpose' {R : Type} [CommRing R] {k p q : ℕ} (a : Fin k → R) (b : Fin p → R)
    (M : Matrix (Fin q) (Fin p) R) : Matrix.vecMulVec a b * Mᵀ = Matrix.vecMulVec a (M *ᵥ b) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.transpose_apply, Matrix.mulVec, dotProduct, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by ring

theorem mul_vecMulVec_mul_transpose {R : Type} [CommRing R] {k l p q : ℕ} (A : Matrix (Fin l) (Fin k) R)
    (a : Fin k → R) (b : Fin p → R) (M : Matrix (Fin q) (Fin p) R) :
    A * Matrix.vecMulVec a b * Mᵀ = Matrix.vecMulVec (A *ᵥ a) (M *ᵥ b) := by
  rw [mul_vecMulVec', vecMulVec_mul_transpose']

end GlobalTheory.ThK.WeilEvExch

open GlobalTheory.ThK.WeilEvExch in

theorem GlobalTheory.ThK.weil_ev_exchange : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' → ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W), IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ x : UA σ G₁.V.J × UA σ G₁.W.J, ∃ (c : ℂ) (g : UA σ G.V.J × UA σ G.W.J),
      mat g.1 *ᵥ incV F H.x = incV F H.x ∧ mat g.2 *ᵥ incV F H'.y = incV F H'.y ∧
      ∀ Φ ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')), om₁ x (e Φ) = c • e (om g Φ) := by
  intro hKP F E _ _ _ _ _ σ B b a' G G₁ H H' cfg e hev X om om' om₁ om₁' T T₁ x
  have P := (GlobalTheory.ThK.Check.isPair_of_isTriple T).1
  obtain ⟨mV, hmV⟩ := GlobalTheory.LeviElem.levi_exists F E σ B b a' G G₁ H H' cfg T.base T.geo T₁.geo
  obtain ⟨g₂, hg₂⟩ := GlobalTheory.ThK.exists_isLevi_unitary_smaller F E σ B _ _ G.W G₁.W H' 0 (b + 1) _ _ _ _ T.base T.geo.hW
    T₁.geo.hW cfg.hH' x.2
  have hg₁ := hmV 1 x.1
  set g₁ := mV 1 x.1
  set g : UA σ G.V.J × UA σ G.W.J := (g₁, g₂) with hgdef
  have S := T.weil.isUSplitting
  have S₁ := T₁.weil.isUSplitting
  obtain ⟨i1x, i1ι⟩ := levi_inv hg₁
  obtain ⟨i2x, i2ι⟩ := levi_inv hg₂
  let f : Fn F (b + 2) (b + 2 + a') →ₗ[ℂ] Fn F b (b + a') := om₁ x ∘ₗ e ∘ₗ om g⁻¹
  have hf : ∀ Φ, f Φ = om₁ x (e (om g⁻¹ Φ)) := fun _ => rfl
  have fheis : ∀ (z : Matrix (Fin b) (Fin (b + a')) (AE F E)), ∀ Φ ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')),
      f (G.M.co.rho B.ψ (incM F H.ι * z * (incM F H'.ι)ᵀ) Φ) = G₁.M.co.rho B.ψ z (f Φ) := by
    intro z Φ hΦ
    have hp := S.pres g⁻¹ Φ hΦ
    rw [hf, hf, S.impl g⁻¹ _ Φ hΦ]
    have ha : actAB (cA σ) g⁻¹ (incM F H.ι * z * (incM F H'.ι)ᵀ) =
        incM F H.ι * actAB (cA σ) x⁻¹ z * (incM F H'.ι)ᵀ := by
      show mat g₁⁻¹ * (incM F H.ι * z * (incM F H'.ι)ᵀ) * (mat g₂⁻¹)ᵀ =
        incM F H.ι * (mat x.1⁻¹ * z * (mat x.2⁻¹)ᵀ) * (incM F H'.ι)ᵀ
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, i1ι, Matrix.mul_assoc _ (incM F H'.ι)ᵀ, ← Matrix.transpose_mul, i2ι,
        Matrix.transpose_mul]
      simp only [Matrix.mul_assoc]
    rw [ha, hev.Heisenberg₂ _ _ hp, S₁.impl x _ _ (hev.maps _ hp)]
    congr 2
    show mat x.1 * (mat x.1⁻¹ * z * (mat x.2⁻¹)ᵀ) * (mat x.2)ᵀ = z
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, mat_mul_inv, Matrix.one_mul, Matrix.mul_assoc, ← Matrix.transpose_mul,
      mat_mul_inv, Matrix.transpose_one, Matrix.mul_one]
  have finv : ∀ u ∈ isoA H H', ∀ Φ ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')), f (G.M.co.rho B.ψ u Φ) = f Φ := by
    intro u hu Φ hΦ
    have hp := S.pres g⁻¹ Φ hΦ
    rw [hf, hf, S.impl g⁻¹ _ Φ hΦ, hev.inv _ ?_ _ hp]
    show mat g₁⁻¹ * u * (mat g₂⁻¹)ᵀ ∈ isoA H H'
    rcases hu with ⟨y, rfl⟩ | ⟨z, rfl⟩
    · left
      refine ⟨mat g₁⁻¹ *ᵥ y, ?_⟩
      rw [mul_vecMulVec_mul_transpose, i2x]
    · right
      refine ⟨mat x.2⁻¹ *ᵥ z, ?_⟩
      rw [mul_vecMulVec_mul_transpose, i1x, Matrix.mulVec_mulVec, i2ι, ← Matrix.mulVec_mulVec]
  obtain ⟨c, hc⟩ := GlobalTheory.T.pair_double_descent hKP.base F E σ B (b + 2) (b + 2 + a') b (b + a') G.V G.W G₁.V G₁.W G.M X.β (X.β / X.α) om
    _ _ _ _ P H H' 0 (b + 1) 0 (b + 1) G₁.M cfg.hH cfg.hH' T₁.geo.hM e hev f fheis finv
  refine ⟨c, g, by simpa using hg₁.1, by simpa using hg₂.2.1, fun Φ hΦ => ?_⟩
  have h := hc _ (S.pres g Φ hΦ)
  rw [hf, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at h
  exact h
