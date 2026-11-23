import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqISupFockDeg
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.LeviCommute

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine

theorem form_swap {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (hσ : ∀ z, σ (σ z) = z) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (hJ : ∀ i j, σ (J j i) = -J i j) (x y : Fin n → E) :
    form σ J y x = -σ (form σ J x y) := by
  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, hJ, Finset.mul_sum, mul_neg, neg_mul,
    Finset.sum_neg_distrib, neg_neg]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem form_add_smul {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (a : E) (z w c : Fin n → E) :
    form σ J (a • z + w) c = a * form σ J z c + form σ J w c := by
  simp only [form, add_dotProduct, smul_dotProduct, smul_eq_mul]

def cols {E : Type} [Field E] {n₁ : ℕ} (H : Plane E (n₁ + 2) n₁) : Fin (n₁ + 2) → Fin (n₁ + 2) → E :=
  Fin.cons H.x (Fin.cons H.y fun j r => H.ι r j : Fin (n₁ + 1) → Fin (n₁ + 2) → E)

@[simp] theorem cols_zero {E : Type} [Field E] {n₁ : ℕ} (H : Plane E (n₁ + 2) n₁) : cols H 0 = H.x := rfl
@[simp] theorem cols_one {E : Type} [Field E] {n₁ : ℕ} (H : Plane E (n₁ + 2) n₁) : cols H (Fin.succ 0) = H.y := rfl
@[simp] theorem cols_succ_succ {E : Type} [Field E] {n₁ : ℕ} (H : Plane E (n₁ + 2) n₁) (j : Fin n₁) :
    cols H j.succ.succ = fun r => H.ι r j := rfl

theorem cols_linearIndependent {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) {d₁ i₀ i₁ r₁ s₁ : ℕ} (W : Spc F E (d₁ + 2)) (W₁ : Spc F E d₁) (H' : Plane E (d₁ + 2) d₁)
    (hσ : ∀ z, σ (σ z) = z) (hJ : ∀ i j, σ (W.J j i) = -W.J i j) (hW₁ : W₁.IsSkew σ B r₁ s₁)
    (hH : H'.IsAdapted σ B W W₁ i₀ i₁) : LinearIndependent E (cols H') := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  simp only [Fin.sum_univ_succ, cols_zero, cols_one, cols_succ_succ] at hg
  set u : Fin d₁ → E := fun j => g j.succ.succ with hu
  have hιu : (∑ j : Fin d₁, g j.succ.succ • fun r => H'.ι r j) = H'.ι *ᵥ u := by
    funext r; simp [Matrix.mulVec, dotProduct, u, mul_comm]
  rw [hιu] at hg
  have hy := congrArg (fun z => form σ W.J z H'.y) hg
  have hx := congrArg (fun z => form σ W.J z H'.x) hg
  simp only [form_add_smul] at hy hx
  have h0y : form σ W.J 0 H'.y = 0 := by simp [form]
  have h0x : form σ W.J 0 H'.x = 0 := by simp [form]
  have hyx : form σ W.J H'.y H'.x = -1 := by rw [form_swap σ hσ W.J hJ, hH.xy, map_one]
  rw [hH.xy, hH.yy, (hH.orth u).2, h0y] at hy
  rw [hH.xx, hyx, (hH.orth u).1, h0x] at hx
  have hg0 : g 0 = 0 := by simpa using hy
  have hg1 : g (Fin.succ 0) = 0 := by simpa using hx
  rw [hg0, hg1, zero_smul, zero_smul, zero_add, zero_add] at hg

  have h1 : W₁.J *ᵥ (fun j => σ (u j)) = 0 := by
    rw [← hH.gram, ← Matrix.mulVec_mulVec]
    have e : H'.ι.map σ *ᵥ (fun j => σ (u j)) = fun i => σ ((H'.ι *ᵥ u) i) := by
      funext i; simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
    rw [e, hg]; simp only [Pi.zero_apply, map_zero]; exact Matrix.mulVec_zero _

  obtain ⟨w₀⟩ := (inferInstance : Nonempty (InfinitePlace F))
  set τ := (B.emb w₀).1 with hτ
  have hz0 : (Complex.I • W₁.J.map τ) *ᵥ (fun j => τ (σ (u j))) = 0 := by
    rw [Matrix.smul_mulVec]
    have : W₁.J.map τ *ᵥ (fun j => τ (σ (u j))) = 0 := by
      funext i
      have := RingHom.map_mulVec τ W₁.J (fun j => σ (u j)) i
      rw [h1] at this
      simpa [Function.comp_def] using this.symm
    rw [this, smul_zero]
  have hz : (fun j => τ (σ (u j))) = 0 := by
    by_contra hne
    have hpos := (hW₁.cartan w₀).2.2 (star fun j => τ (σ (u j))) (by simpa using hne)
    rw [star_star, hz0] at hpos
    simp at hpos
  have hu0 : ∀ j, u j = 0 := fun j => by
    have := congrFun hz j
    exact (map_eq_zero σ).1 ((map_eq_zero τ).1 this)
  intro i
  refine Fin.cases hg0 (Fin.cases hg1 (fun j => hu0 j)) i

def leviDiag {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n₁ : ℕ}
    (t : (AE F E)ˣ) : Fin (n₁ + 2) → AE F E :=
  Fin.cons t.1 (Fin.cons (cA σ (t⁻¹).1) fun _ => 1 : Fin (n₁ + 1) → AE F E)

theorem levi_mul_cols {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {d₁ : ℕ} {W : Spc F E (d₁ + 2)} {W₁ : Spc F E d₁} (H' : Plane E (d₁ + 2) d₁) (t : (AE F E)ˣ)
    (h : UA σ W.J) (hh : IsLevi H' t (1 : UA σ W₁.J) h) :
    mat h * incM F (Matrix.of fun r c => cols H' c r) =
      incM F (Matrix.of fun r c => cols H' c r) * Matrix.diagonal (leviDiag σ t) := by
  obtain ⟨h1, h2, h3⟩ := hh
  have h3' : mat h * incM F H'.ι = incM F H'.ι := h3.trans (Matrix.mul_one _)
  ext r c
  rw [Matrix.mul_diagonal]
  have key : ∀ c, (mat h * incM F (Matrix.of fun r c => cols H' c r)) r c = (mat h *ᵥ incV F (cols H' c)) r := by
    intro c; simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, incM, incV]
  rw [key]
  refine Fin.cases ?_ (Fin.cases ?_ (fun j => ?_)) c
  · rw [cols_zero, h1]; simp [leviDiag, incM, incV, mul_comm]
  · rw [cols_one, h2]; simp [leviDiag, incM, incV, mul_comm]; rfl
  · have := congrFun (congrFun h3' r) j
    simp only [Matrix.mul_apply] at this
    simp [leviDiag, incM, incV, Matrix.mulVec, dotProduct]
    simpa [incM] using this

theorem levi_commute : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (d d₁ : ℕ) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ r s r₁ s₁ : ℕ),
    B.IsGood σ → W.IsSkew σ B r s → W₁.IsSkew σ B r₁ s₁ → H'.IsAdapted σ B W W₁ i₀ i₁ →
    ∀ (t t' : (AE F E)ˣ) (k k' : UA σ W.J), IsLevi H' t (1 : UA σ W₁.J) k → IsLevi H' t' (1 : UA σ W₁.J) k' →
      k * k' = k' * k := by
  intro F E _ _ _ _ _ σ B d d₁ W W₁ H' i₀ i₁ r s r₁ s₁ hB hW hW₁ hH t t' k k' hk hk'
  obtain rfl := hH.rank
  obtain ⟨w₀⟩ := (inferInstance : Nonempty (InfinitePlace F))
  have hσ : ∀ z, σ (σ z) = z := fun z => by
    apply (B.emb w₀).1.injective
    rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star]
  have hli := cols_linearIndependent σ B W W₁ H' hσ hW.skew hW₁ hH
  have hC : IsUnit (Matrix.of fun r c => cols H' c r) := Matrix.linearIndependent_cols_iff_isUnit.1 hli
  have hP : IsUnit (incM F (Matrix.of fun r c => cols H' c r)) := by
    have := hC.map (RingHom.mapMatrix (inclR (F := F) (E := E) (AF F)) :
      Matrix (Fin (d₁ + 2)) (Fin (d₁ + 2)) E →+* Matrix (Fin (d₁ + 2)) (Fin (d₁ + 2)) (AE F E))
    simpa [incM] using this
  have hA := levi_mul_cols H' t k hk
  have hA' := levi_mul_cols H' t' k' hk'
  have hDD : Matrix.diagonal (leviDiag σ (n₁ := d₁) t) * Matrix.diagonal (leviDiag σ t') =
      Matrix.diagonal (leviDiag σ t') * Matrix.diagonal (leviDiag σ t) := by
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1; funext i; exact mul_comm _ _
  apply Subtype.ext; apply Units.ext
  show mat k * mat k' = mat k' * mat k
  refine hP.mul_right_cancel ?_
  set P := incM F (Matrix.of fun r c => cols H' c r)
  calc mat k * mat k' * P = mat k * (mat k' * P) := mul_assoc _ _ _
    _ = mat k * P * Matrix.diagonal (leviDiag σ t') := by rw [hA', mul_assoc]
    _ = P * (Matrix.diagonal (leviDiag σ t) * Matrix.diagonal (leviDiag σ t')) := by rw [hA, mul_assoc]
    _ = P * Matrix.diagonal (leviDiag σ t') * Matrix.diagonal (leviDiag σ t) := by rw [hDD, mul_assoc]
    _ = mat k' * P * Matrix.diagonal (leviDiag σ t) := by rw [hA']
    _ = mat k' * mat k * P := by rw [mul_assoc (mat k'), mul_assoc (mat k'), hA]

end GlobalTheory.LeviCommute
