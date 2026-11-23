import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Idem3

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.UnipHaar

noncomputable section
namespace GlobalTheory.ProjIdem
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem vmv_mul {n : ℕ} (a b c d : Fin n → E) :
    Matrix.vecMulVec a b * Matrix.vecMulVec c d = (b ⬝ᵥ c) • Matrix.vecMulVec a d := by
  ext i j
  simp [Matrix.mul_apply, Matrix.vecMulVec_apply, dotProduct, Finset.smul_sum, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => by ring

theorem cA_incl (σ : E →ₐ[F] E) (e : E) : cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := by
  simp [cA, inclR]

theorem incM_map_cA (σ : E →ₐ[F] E) {n : ℕ} (P : Matrix (Fin n) (Fin n) E) :
    (incM F P).map (cA σ) = incM F (P.map σ) := by
  ext i j; simp [incM, cA_incl]

theorem incM_mul {n : ℕ} (P Q : Matrix (Fin n) (Fin n) E) : incM F P * incM F Q = incM F (P * Q) := by
  simp [incM, Matrix.map_mul]

theorem adj_incM (σ : E →ₐ[F] E) {n : ℕ} (J P Q : Matrix (Fin n) (Fin n) E) (hJ : J.det ≠ 0)
    (h : (P.map σ)ᵀ * J.map σ = J.map σ * Q) : adj σ J (incM F P) = incM F Q := by
  have hdet : IsUnit (incM F (J.map σ)).det := by
    have h1 : (incM F (J.map σ)).det = inclR (F := F) (AF F) (σ J.det) := by
      simp [incM, RingHom.map_det, AlgHom.map_det]
    rw [h1]
    exact (isUnit_iff_ne_zero.2 ((map_ne_zero σ).2 hJ)).map _
  change (incM F (J.map σ))⁻¹ * ((incM F P).map (cA σ))ᵀ * incM F (J.map σ) = incM F Q
  have ht : (incM F (P.map σ))ᵀ = incM F ((P.map σ)ᵀ) := by simp [incM, Matrix.transpose_map]
  rw [incM_map_cA, ht, Matrix.mul_assoc, incM_mul, h, ← incM_mul, Matrix.nonsing_inv_mul_cancel_left _ _ hdet]

theorem skew_flip (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (hσ : ∀ x, σ (σ x) = x)
    (hJ : ∀ i j, σ (J j i) = -J i j) (x y : Fin n → E) :
    form σ J y x = -σ (form σ J x y) := by
  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, hJ, Finset.mul_sum, Finset.sum_neg_distrib,
    neg_mul, mul_neg, neg_neg]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem adjX (σ : E →ₐ[F] E) {n n₁ : ℕ} (J : Matrix (Fin n) (Fin n) E) (H : Plane E n n₁) (hσ : ∀ x, σ (σ x) = x)
    (hJ : ∀ i j, σ (J j i) = -J i j) :
    ((prX σ J H).map σ)ᵀ * J.map σ = J.map σ * prY σ J H := by
  ext i j
  simp only [prX, prY, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.vecMulVec_apply, Matrix.neg_apply,
    Matrix.mulVec, dotProduct, map_sum, map_mul, hσ, hJ, Finset.mul_sum, Finset.sum_mul, Finset.sum_neg_distrib,
    neg_mul, mul_neg, neg_neg]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

theorem adjY (σ : E →ₐ[F] E) {n n₁ : ℕ} (J : Matrix (Fin n) (Fin n) E) (H : Plane E n n₁) (hσ : ∀ x, σ (σ x) = x)
    (hJ : ∀ i j, σ (J j i) = -J i j) :
    ((prY σ J H).map σ)ᵀ * J.map σ = J.map σ * prX σ J H := by
  ext i j
  simp only [prX, prY, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.vecMulVec_apply, Matrix.neg_apply,
    Matrix.mulVec, dotProduct, map_sum, map_mul, map_neg, hσ, hJ, Finset.mul_sum, Finset.sum_mul, Finset.sum_neg_distrib,
    neg_mul, mul_neg, neg_neg]
  rw [neg_inj, Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

theorem adjOne (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) :
    (((1 : Matrix (Fin n) (Fin n) E)).map σ)ᵀ * J.map σ = J.map σ * 1 := by
  simp

theorem adjAdd (σ : E →ₐ[F] E) {n : ℕ} (J P Q P' Q' : Matrix (Fin n) (Fin n) E)
    (h : (P.map σ)ᵀ * J.map σ = J.map σ * Q) (h' : (P'.map σ)ᵀ * J.map σ = J.map σ * Q') :
    ((P - P').map σ)ᵀ * J.map σ = J.map σ * (Q - Q') := by
  rw [Matrix.map_sub _ (map_sub σ), Matrix.transpose_sub, Matrix.sub_mul, Matrix.mul_sub, h, h']

theorem formXY_E (σ : E →ₐ[F] E) {n n₁ : ℕ} (J : Matrix (Fin n) (Fin n) E) (H : Plane E n n₁) (u v : Fin n → E) :
    (J *ᵥ fun i => σ (v i)) ⬝ᵥ u = form σ J u v := by
  rw [dotProduct_comm]; rfl

theorem prods (σ : E →ₐ[F] E) {n n₁ : ℕ} (J : Matrix (Fin n) (Fin n) E) (H : Plane E n n₁) (hσ : ∀ x, σ (σ x) = x)
    (hJ : ∀ i j, σ (J j i) = -J i j) (xx : form σ J H.x H.x = 0) (yy : form σ J H.y H.y = 0)
    (xy : form σ J H.x H.y = 1) :
    prX σ J H * prX σ J H = prX σ J H ∧ prY σ J H * prY σ J H = prY σ J H ∧
      prX σ J H * prY σ J H = 0 ∧ prY σ J H * prX σ J H = 0 := by
  have yx : form σ J H.y H.x = -1 := by rw [skew_flip σ J hσ hJ, xy, map_one]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [prX, vmv_mul, formXY_E σ J H, xy, one_smul]
  · rw [prY, neg_mul_neg, vmv_mul, formXY_E σ J H, yx, neg_one_smul]
  · rw [prX, prY, mul_neg, vmv_mul, formXY_E σ J H, yy, zero_smul, neg_zero]
  · rw [prX, prY, neg_mul, vmv_mul, formXY_E σ J H, xx, zero_smul, neg_zero]

theorem coi_E (σ : E →ₐ[F] E) {n n₁ : ℕ} (J : Matrix (Fin n) (Fin n) E) (H : Plane E n n₁) (hσ : ∀ x, σ (σ x) = x)
    (hJ : ∀ i j, σ (J j i) = -J i j) (xx : form σ J H.x H.x = 0) (yy : form σ J H.y H.y = 0)
    (xy : form σ J H.x H.y = 1) :
    CompleteOrthogonalIdempotents ![prX σ J H, prI σ J H, prY σ J H] := by
  obtain ⟨hXX, hYY, hXY, hYX⟩ := prods σ J H hσ hJ xx yy xy
  have hI1 : prX σ J H * prI σ J H = 0 := by simp [prI, mul_sub, hXX, hXY]
  have hI2 : prI σ J H * prX σ J H = 0 := by simp [prI, sub_mul, hXX, hYX]
  have hI3 : prY σ J H * prI σ J H = 0 := by simp [prI, mul_sub, hYY, hYX]
  have hI4 : prI σ J H * prY σ J H = 0 := by simp [prI, sub_mul, hYY, hXY]
  have hII : prI σ J H * prI σ J H = prI σ J H := by
    have e : prI σ J H * prI σ J H = (1 - prX σ J H - prY σ J H) * prI σ J H := rfl
    rw [e, sub_mul, sub_mul, one_mul, hI1, hI3, sub_zero, sub_zero]
  refine ⟨⟨fun i => ?_, fun i j hij => ?_⟩, ?_⟩
  · fin_cases i <;> simp [IsIdempotentElem, hXX, hYY, hII]
  · fin_cases i <;> fin_cases j <;> simp_all
  · simp only [Fin.sum_univ_three, prI, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    abel

theorem idem_main : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n n₁ : ℕ) (W : Spc F E n) (W₁ : Spc F E n₁) (H : Plane E n n₁) (i₀ i₁ : ℕ),
    (∀ x, σ (σ x) = x) → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 → H.IsAdapted σ B W W₁ i₀ i₁ →
    CompleteOrthogonalIdempotents (idem3 σ W.J H) ∧
    (∀ a, idem3 σ W.J H a ∈ ((inclR (F := F) (E := E) (AF F)).mapMatrix (m := Fin n)).range) ∧
    ∀ a, ∃ a', GlobalTheory.UnipHaar.adj σ W.J (idem3 σ W.J H a) = idem3 σ W.J H a' ∧ wt3 a' = -wt3 a := by
  intro F E _ _ _ _ _ σ B n n₁ W W₁ H i₀ i₁ hσ hJ hdet hA
  have hc := coi_E σ W.J H hσ hJ hA.xx hA.yy hA.xy
  have he : idem3 σ W.J H = ((inclR (F := F) (E := E) (AF F)).mapMatrix (m := Fin n)) ∘
      ![prX σ W.J H, prI σ W.J H, prY σ W.J H] := by
    funext a; fin_cases a <;> rfl
  have hXY := adjX σ W.J H hσ hJ
  have hYX := adjY σ W.J H hσ hJ
  have hII : ((prI σ W.J H).map σ)ᵀ * W.J.map σ = W.J.map σ * prI σ W.J H := by
    unfold prI
    exact adjAdd σ W.J _ _ _ _ (adjAdd σ W.J _ _ _ _ (adjOne σ W.J) hXY) hYX |>.trans (by
      rw [show (1 : Matrix (Fin n) (Fin n) E) - prY σ W.J H - prX σ W.J H = 1 - prX σ W.J H - prY σ W.J H by abel])
  refine ⟨he ▸ hc.map _, fun a => ⟨_, (congrFun he a).symm⟩, fun a => ?_⟩
  fin_cases a
  · exact ⟨2, adj_incM σ W.J _ _ hdet hXY, by simp [wt3]⟩
  · exact ⟨1, adj_incM σ W.J _ _ hdet hII, by simp [wt3]⟩
  · exact ⟨0, adj_incM σ W.J _ _ hdet hYX, by simp [wt3]⟩

end GlobalTheory.ProjIdem
end
