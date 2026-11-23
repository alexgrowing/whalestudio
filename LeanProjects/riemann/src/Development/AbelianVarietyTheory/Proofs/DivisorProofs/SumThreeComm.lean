import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrPApply
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ArchSch

namespace GlobalTheory.ArchSch.OrthPlane

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem hTens_eq_sum {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A) {α β : Type}
    [Fintype α] [Fintype β] (JA : Matrix α α A) (JB : Matrix β β A) (x y : Matrix α β A) :
    hTens c JA JB x y = ∑ i, ∑ k, JA i k * ∑ j, ∑ l, x i j * JB j l * c (y k l) := by
  unfold hTens
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

theorem sum_three_comm {A α β γ : Type} [AddCommMonoid A] [Fintype α] [Fintype β] [Fintype γ] (f : α → β → γ → A) :
    ∑ j, ∑ l, ∑ m, f j l m = ∑ m, ∑ j, ∑ l, f j l m := by
  rw [Finset.sum_congr rfl fun j _ => Finset.sum_comm]
  rw [Finset.sum_comm]

theorem cA_inclR (σ : E →ₐ[F] E) (e : E) :
    cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := by
  simp [cA, inclR]

theorem incM_one {n : ℕ} : incM F (1 : Matrix (Fin n) (Fin n) E) = 1 := by
  simp [incM]

theorem form_swap {σ : E →ₐ[F] E} (hinv : ∀ t, σ (σ t) = t) {d : ℕ} {J : Matrix (Fin d) (Fin d) E}
    (hskew : ∀ i j, σ (J j i) = -J i j) (x v : Fin d → E) : form σ J x v = -σ (form σ J v x) := by
  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hinv, hskew, Finset.mul_sum]
  rw [Finset.sum_comm (f := fun a b => σ (v a) * (-J b a * x b)), ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

theorem inner_left {σ : E →ₐ[F] E} {n d d₁ : ℕ} (J : Matrix (Fin d) (Fin d) E) (ι : Matrix (Fin d) (Fin d₁) E)
    (x₀ : Fin d → E) (h : ∀ m, ∑ j, ∑ l, ι j m * J j l * σ (x₀ l) = 0) (a : Fin n → AE F E)
    (z : Matrix (Fin n) (Fin d₁) (AE F E)) (i k : Fin n) :
    ∑ j, ∑ l, (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F ι)ᵀ) i j * incM F J j l *
      cA σ (Matrix.vecMulVec a (incV F x₀) k l) = 0 := by
  have h' : ∀ m, ∑ j, ∑ l, inclR (F := F) (AF F) (ι j m) * inclR (F := F) (AF F) (J j l) *
      inclR (F := F) (AF F) (σ (x₀ l)) = 0 := by
    intro m
    have := congrArg (inclR (F := F) (AF F)) (h m)
    simpa only [map_sum, map_mul, map_zero] using this
  rw [incM_one, Matrix.one_mul]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, incM, Matrix.map_apply, Matrix.vecMulVec_apply, incV,
    map_mul, cA_inclR, Finset.sum_mul]
  rw [sum_three_comm]
  refine Finset.sum_eq_zero fun m _ => ?_
  rw [← mul_zero (z i m * cA σ (a k)), ← h' m, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

theorem inner_right {σ : E →ₐ[F] E} {n d d₁ : ℕ} (J : Matrix (Fin d) (Fin d) E) (ι : Matrix (Fin d) (Fin d₁) E)
    (x₀ : Fin d → E) (h : ∀ m, ∑ j, ∑ l, x₀ j * J j l * σ (ι l m) = 0) (a : Fin n → AE F E)
    (z : Matrix (Fin n) (Fin d₁) (AE F E)) (i k : Fin n) :
    ∑ j, ∑ l, Matrix.vecMulVec a (incV F x₀) i j * incM F J j l *
      cA σ ((incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F ι)ᵀ) k l) = 0 := by
  have h' : ∀ m, ∑ j, ∑ l, inclR (F := F) (AF F) (x₀ j) * inclR (F := F) (AF F) (J j l) *
      inclR (F := F) (AF F) (σ (ι l m)) = 0 := by
    intro m
    have := congrArg (inclR (F := F) (AF F)) (h m)
    simpa only [map_sum, map_mul, map_zero] using this
  rw [incM_one, Matrix.one_mul]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, incM, Matrix.map_apply, Matrix.vecMulVec_apply, incV,
    map_mul, map_sum, cA_inclR, Finset.mul_sum]
  rw [sum_three_comm]
  refine Finset.sum_eq_zero fun m _ => ?_
  rw [← mul_zero (a i * cA σ (z k m)), ← h' m, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

theorem symp_tens_orth : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} (B : Base F E)
    {n d d₁ : ℕ} (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (r' s' i₀ i₁ : ℕ) (JX : Matrix (Fin n) (Fin n) E),
    B.IsGood σ → W.IsSkew σ B r' s' → H'.IsAdapted σ B W W₁ i₀ i₁ → ∀ (a : Fin n → AE F E) (z : Matrix (Fin n) (Fin d₁) (AE F E)),
    symp (R := AF F) (cA σ) (-1) (incM F JX) (incM F W.J) (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ)
      (Matrix.vecMulVec a (incV F H'.x)) = 0 ∧
    symp (R := AF F) (cA σ) (-1) (incM F JX) (incM F W.J) (Matrix.vecMulVec a (incV F H'.x))
      (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ) = 0 ∧
    symp (R := AF F) (cA σ) (-1) (incM F JX) (incM F W.J) (Matrix.vecMulVec a (incV F H'.y))
      (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ) = 0 := by
  intro F E _ _ _ _ _ σ B n d d₁ W W₁ H' r' s' i₀ i₁ JX hB hW hA a z
  have hinv : ∀ t, σ (σ t) = t := fun t => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star]
  have hF : ∀ u v : Fin d → E, ∑ j, ∑ l, u j * W.J j l * σ (v l) = form σ W.J u v := by
    intro u v
    simp only [form, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  have hcol : ∀ m, H'.ι *ᵥ Pi.single m 1 = fun j => H'.ι j m := by
    intro m; ext j; simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have h1 : ∀ m, ∑ j, ∑ l, H'.ι j m * W.J j l * σ (H'.x l) = 0 := by
    intro m; rw [hF (fun j => H'.ι j m), ← hcol]; exact (hA.orth _).1
  have h2 : ∀ v : Fin d → E, (∀ u, form σ W.J (H'.ι *ᵥ u) v = 0) →
      ∀ m, ∑ j, ∑ l, v j * W.J j l * σ (H'.ι l m) = 0 := by
    intro v hv m
    rw [hF v (fun l => H'.ι l m), form_swap hinv hW.skew, ← hcol, hv, map_zero, neg_zero]
  refine ⟨?_, ?_, ?_⟩
  · unfold symp
    rw [hTens_eq_sum]
    rw [Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun k _ => by
      rw [inner_left (σ := σ) W.J H'.ι H'.x h1 a z i k, mul_zero]]
    simp
  · unfold symp
    rw [hTens_eq_sum]
    rw [Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun k _ => by
      rw [inner_right (σ := σ) W.J H'.ι H'.x (h2 _ fun u => (hA.orth u).1) a z i k, mul_zero]]
    simp
  · unfold symp
    rw [hTens_eq_sum]
    rw [Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun k _ => by
      rw [inner_right (σ := σ) W.J H'.ι H'.y (h2 _ fun u => (hA.orth u).2) a z i k, mul_zero]]
    simp

end GlobalTheory.ArchSch.OrthPlane
