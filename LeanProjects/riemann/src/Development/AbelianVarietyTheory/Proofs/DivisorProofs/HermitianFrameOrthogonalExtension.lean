import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
open scoped Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift Formalism.BasicNotions.TH Matrix

namespace GlobalTheory.FrameAssemble

lemma entry_eq {m α β : Type} [Fintype m] (A : Matrix m α ℂ) (M : Matrix m m ℂ) (B : Matrix m β ℂ) (a : α) (b : β) :
    (Aᵀ * M * B.map star) a b = (fun i => A i a) ⬝ᵥ M *ᵥ star (fun i => B i b) := by
  simp only [Matrix.mul_apply, transpose_apply, map_apply, dotProduct, mulVec, Pi.star_apply,
    Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]

lemma map_star_mul {m k l : Type} [Fintype k] (A : Matrix m k ℂ) (B : Matrix k l ℂ) :
    (A * B).map star = A.map star * B.map star := by
  ext i j; simp [Matrix.mul_apply, star_sum]

lemma Jm_apply (p q : ℕ) (a b : Ix p q) : Jm p q a b =
    match a, b with
    | .inl i, .inl j => if i = j then 1 else 0
    | .inr i, .inr j => if i = j then -1 else 0
    | _, _ => 0 := by
  rcases a with a | a <;> rcases b with b | b <;> simp [Jm, Formalism.UG.Jpq, one_apply] <;> split_ifs <;> simp

lemma Jm_mul_Jm (p q : ℕ) : Jm p q * Jm p q = 1 := by
  simp [Jm, Formalism.UG.Jpq, fromBlocks_multiply, fromBlocks_one]

lemma mul_Jm_apply {m : Type} {p q : ℕ} (D : Matrix m (Ix p q) ℂ) (i : m) (a : Ix p q) :
    (D * Jm p q) i a = match a with
      | .inl _ => D i a
      | .inr _ => - D i a := by
  rcases a with a | a <;>
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Jm, Formalism.UG.Jpq, one_apply]

def col {n n₁ r₁ s₁ : ℕ} (ι : Matrix (Fin n) (Fin n₁) ℂ) (C₁ : Matrix (Fin n₁) (Ix r₁ s₁) ℂ) (e f : Fin n → ℂ) :
    Ix (r₁ + 1) (s₁ + 1) → Fin n → ℂ
  | .inl a => Fin.cases e (fun j => ι *ᵥ C₁ᵀ (.inl j)) a
  | .inr b => Fin.cases f (fun j => ι *ᵥ C₁ᵀ (.inr j)) b

def frame {n n₁ r₁ s₁ : ℕ} (ι : Matrix (Fin n) (Fin n₁) ℂ) (C₁ : Matrix (Fin n₁) (Ix r₁ s₁) ℂ) (e f : Fin n → ℂ) :
    Matrix (Fin n) (Ix (r₁ + 1) (s₁ + 1)) ℂ :=
  Matrix.of fun i a => col ι C₁ e f a i

theorem assemble : ∀ {n n₁ r₁ s₁ : ℕ} (M θ : Matrix (Fin n) (Fin n) ℂ) (θ₁ : Matrix (Fin n₁) (Fin n₁) ℂ)
    (ι : Matrix (Fin n) (Fin n₁) ℂ) (C₁ : Matrix (Fin n₁) (Ix r₁ s₁) ℂ) (e f : Fin n → ℂ),
    (r₁ + 1) + (s₁ + 1) = n → IsFrame (ιᵀ * M * ι.map star) C₁ → θ₁ * C₁ = C₁ * Jm r₁ s₁ →
    θ * ι = ι * θ₁ → θ *ᵥ e = e → θ *ᵥ f = -f → e ⬝ᵥ M *ᵥ star e = 1 →
    f ⬝ᵥ M *ᵥ star f = -1 → e ⬝ᵥ M *ᵥ star f = 0 → f ⬝ᵥ M *ᵥ star e = 0 →
    (∀ u : Fin n₁ → ℂ, (ι *ᵥ u) ⬝ᵥ M *ᵥ star e = 0 ∧ (ι *ᵥ u) ⬝ᵥ M *ᵥ star f = 0 ∧
      e ⬝ᵥ M *ᵥ star (ι *ᵥ u) = 0 ∧ f ⬝ᵥ M *ᵥ star (ι *ᵥ u) = 0) →
    ∃ C : Matrix (Fin n) (Ix (r₁ + 1) (s₁ + 1)) ℂ, IsFrame M C ∧ θ * C = C * Jm (r₁ + 1) (s₁ + 1) ∧
      (∀ i, C i (.inl 0) = e i) ∧ (∀ i, C i (.inr 0) = f i) ∧
      ∀ a, a ≠ .inl 0 → a ≠ .inr 0 → ∃ z : Fin n₁ → ℂ, ∀ i, C i a = (ι *ᵥ z) i := by
  intro n n₁ r₁ s₁ M θ θ₁ ι C₁ e f hn hF hθ₁ hθι he hf hee hff hef hfe horth
  have hD : ∀ a b, (ι *ᵥ C₁ᵀ a) ⬝ᵥ M *ᵥ star (ι *ᵥ C₁ᵀ b) = Jm r₁ s₁ a b := by
    intro a b
    have h1 := entry_eq (ι * C₁) M (ι * C₁) a b
    have h2 : (fun i => (ι * C₁) i a) = ι *ᵥ C₁ᵀ a := by
      ext i; simp [Matrix.mul_apply, mulVec, dotProduct]
    have h3 : (fun i => (ι * C₁) i b) = ι *ᵥ C₁ᵀ b := by
      ext i; simp [Matrix.mul_apply, mulVec, dotProduct]
    rw [h2, h3] at h1
    rw [← h1, ← hF.1]
    simp only [Matrix.transpose_mul, map_star_mul, Matrix.mul_assoc]
  have hgram : (frame ι C₁ e f)ᵀ * M * (frame ι C₁ e f).map star = Jm (r₁ + 1) (s₁ + 1) := by
    ext a b
    rw [entry_eq]
    change col ι C₁ e f a ⬝ᵥ M *ᵥ star (col ι C₁ e f b) = _
    rcases a with a | a <;> rcases b with b | b <;> refine Fin.cases ?_ (fun j => ?_) a <;>
      refine Fin.cases ?_ (fun k => ?_) b <;>
      simp only [col, Fin.cases_zero, Fin.cases_succ, hD, Jm_apply, hee, hff, hef, hfe, (horth _).1,
        (horth _).2.1, (horth _).2.2.1, (horth _).2.2.2, Fin.succ_inj] <;> simp [Fin.succ_ne_zero, (Fin.succ_ne_zero _).symm]
  have hcolθ : ∀ a, θ *ᵥ col ι C₁ e f a = match a with
      | .inl _ => col ι C₁ e f a
      | .inr _ => - col ι C₁ e f a := by
    have hc : ∀ b, θ₁ *ᵥ C₁ᵀ b = (C₁ * Jm r₁ s₁)ᵀ b := by
      intro b; ext j; rw [← hθ₁]; simp [Matrix.mul_apply, mulVec, dotProduct]
    have hι : ∀ b, θ *ᵥ (ι *ᵥ C₁ᵀ b) = ι *ᵥ (C₁ * Jm r₁ s₁)ᵀ b := by
      intro b; rw [mulVec_mulVec, hθι, ← mulVec_mulVec, hc]
    have hl : ∀ j, (C₁ * Jm r₁ s₁)ᵀ (.inl j) = C₁ᵀ (.inl j) := by
      intro j; ext k; simp [transpose_apply, mul_Jm_apply]
    have hr : ∀ j, (C₁ * Jm r₁ s₁)ᵀ (.inr j) = - C₁ᵀ (.inr j) := by
      intro j; ext k; simp [transpose_apply, mul_Jm_apply]
    intro a
    rcases a with a | a <;> refine Fin.cases ?_ (fun j => ?_) a <;>
      simp only [col, Fin.cases_zero, Fin.cases_succ, he, hf, hι, hl, hr, mulVec_neg]
  refine ⟨frame ι C₁ e f, ⟨hgram, ?_⟩, ?_, fun i => rfl, fun i => rfl, ?_⟩
  ·
    have hL : (frame ι C₁ e f)ᵀ * (M * (frame ι C₁ e f).map star * Jm (r₁ + 1) (s₁ + 1)) = 1 := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hgram, Jm_mul_Jm]
    have hcard : Fintype.card (Ix (r₁ + 1) (s₁ + 1)) = Fintype.card (Fin n) := by
      simp [hn]
    have hR := (Matrix.mul_eq_one_comm_of_equiv (Fintype.equivOfCardEq hcard)).1 hL
    refine ⟨(M * (frame ι C₁ e f).map star * Jm (r₁ + 1) (s₁ + 1))ᵀ, ?_⟩
    have := congrArg Matrix.transpose hR
    simpa [Matrix.transpose_mul] using this
  · ext i a
    have h1 : (θ * frame ι C₁ e f) i a = (θ *ᵥ col ι C₁ e f a) i := by
      simp [frame, Matrix.mul_apply, mulVec, dotProduct]
    rw [h1, hcolθ, mul_Jm_apply]
    rcases a with a | a <;> simp [frame]
  · intro a h0 h0'
    rcases a with a | a
    · refine Fin.cases (fun h => absurd rfl h) (fun j _ => ⟨C₁ᵀ (.inl j), fun i => ?_⟩) a h0
      simp [frame, col]
    · refine Fin.cases (fun h => absurd rfl h) (fun j _ => ⟨C₁ᵀ (.inr j), fun i => ?_⟩) a h0'
      simp [frame, col]

end GlobalTheory.FrameAssemble
