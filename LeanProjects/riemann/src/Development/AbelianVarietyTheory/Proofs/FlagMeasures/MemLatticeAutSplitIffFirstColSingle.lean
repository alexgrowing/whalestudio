import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsLatMeasurableConst
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolEqOfAedisjoint

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.OrbitTerm

namespace GlobalTheory.OrbitTerm.SplitStab

variable {E : Type} [Field E] {k : ℕ}

theorem det_of_col (M : Matrix (Fin (k + 1)) (Fin (k + 1)) E)
    (h : ∀ a, M a 0 = if a = 0 then 1 else 0) : M.det = (M.submatrix Fin.succ Fin.succ).det := by
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  simp [h, Fin.succ_ne_zero]

theorem mulVec_zero_of_col (M : Matrix (Fin (k + 1)) (Fin (k + 1)) E)
    (h : ∀ a, M a 0 = if a = 0 then 1 else 0) (y : Fin (k + 1) → E) :
    (M *ᵥ y) 0 = y 0 + (fun b => M 0 (Fin.succ b)) ⬝ᵥ Fin.tail y := by
  have h0 : M 0 0 = 1 := by simpa using h 0
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, h0, Fin.tail]

theorem tail_mulVec_of_col (M : Matrix (Fin (k + 1)) (Fin (k + 1)) E)
    (h : ∀ a, M a 0 = if a = 0 then 1 else 0) (y : Fin (k + 1) → E) :
    Fin.tail (M *ᵥ y) = M.submatrix Fin.succ Fin.succ *ᵥ Fin.tail y := by
  funext b
  have hb : M b.succ 0 = 0 := by simpa [Fin.succ_ne_zero] using h b.succ
  simp [Fin.tail, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, hb, Matrix.submatrix]

theorem preserves_iff [NumberField E] (Λ : Submodule (𝓞 E) (Fin (k + 1) → E)) (Λ₀ : Submodule (𝓞 E) (Fin 1 → E))
    (Λ' : Submodule (𝓞 E) (Fin k → E)) (hΛ : ∀ y, y ∈ Λ ↔ (fun _ => y 0) ∈ Λ₀ ∧ Fin.tail y ∈ Λ')
    (M : Matrix (Fin (k + 1)) (Fin (k + 1)) E) (h : ∀ a, M a 0 = if a = 0 then 1 else 0) :
    (∀ y, M *ᵥ y ∈ Λ ↔ y ∈ Λ) ↔ (∀ y, M.submatrix Fin.succ Fin.succ *ᵥ y ∈ Λ' ↔ y ∈ Λ') ∧
      ∀ y ∈ Λ', (fun _ => (fun b => M 0 (Fin.succ b)) ⬝ᵥ y) ∈ Λ₀ := by
  have key : ∀ y : Fin (k + 1) → E, M *ᵥ y ∈ Λ ↔
      ((fun _ => y 0) + (fun _ => (fun b => M 0 (Fin.succ b)) ⬝ᵥ Fin.tail y) : Fin 1 → E) ∈ Λ₀ ∧
        M.submatrix Fin.succ Fin.succ *ᵥ Fin.tail y ∈ Λ' := by
    intro y
    rw [hΛ, mulVec_zero_of_col M h y, tail_mulVec_of_col M h y]
    exact Iff.rfl
  have hcons : ∀ (c : E) (z : Fin k → E),
      (Fin.cons c z : Fin (k + 1) → E) 0 = c ∧ Fin.tail (Fin.cons c z : Fin (k + 1) → E) = z :=
    fun c z => ⟨Fin.cons_zero _ _, Fin.tail_cons _ _⟩
  constructor
  · intro hM
    refine ⟨fun z => ⟨fun hz => ?_, fun hz => ?_⟩, fun z hz => ?_⟩
    ·
      set c : E := -((fun b => M 0 (Fin.succ b)) ⬝ᵥ z)
      have h1 : M *ᵥ (Fin.cons c z : Fin (k + 1) → E) ∈ Λ := by
        rw [key, (hcons c z).1, (hcons c z).2]
        refine ⟨?_, hz⟩
        have hz0 : ((fun _ => c) + (fun _ => (fun b => M 0 (Fin.succ b)) ⬝ᵥ z) : Fin 1 → E) = 0 := by
          funext i; simp [c]
        rw [hz0]; exact Λ₀.zero_mem
      have h2 := (hΛ _).1 ((hM _).1 h1)
      rw [(hcons c z).2] at h2
      exact h2.2
    · have h1 : (Fin.cons 0 z : Fin (k + 1) → E) ∈ Λ := by
        rw [hΛ, (hcons 0 z).1, (hcons 0 z).2]; exact ⟨Λ₀.zero_mem, hz⟩
      have h2 := (key _).1 ((hM _).2 h1)
      rw [(hcons 0 z).2] at h2
      exact h2.2
    · have h1 : (Fin.cons 0 z : Fin (k + 1) → E) ∈ Λ := by
        rw [hΛ, (hcons 0 z).1, (hcons 0 z).2]; exact ⟨Λ₀.zero_mem, hz⟩
      have h2 := ((key _).1 ((hM _).2 h1)).1
      rw [(hcons 0 z).1, (hcons 0 z).2] at h2
      have he : ((fun _ => (0 : E)) + (fun _ => (fun b => M 0 (Fin.succ b)) ⬝ᵥ z) : Fin 1 → E) =
          fun _ => (fun b => M 0 (Fin.succ b)) ⬝ᵥ z := by
        funext i; simp
      rwa [he] at h2
  · rintro ⟨hA, hr⟩ y
    rw [key, hΛ, hA]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨(add_mem_cancel_right (hr _ h2)).1 h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨Λ₀.add_mem h1 (hr _ h2), h2⟩

end GlobalTheory.OrbitTerm.SplitStab

namespace GlobalTheory.OrbitTerm

open SplitStab in

theorem mem_autGL_split_iff : ∀ (E : Type) [Field E] [NumberField E] (k : ℕ) (Λ : Submodule (𝓞 E) (Fin (k + 1) → E)) (Λ₀ : Submodule (𝓞 E) (Fin 1 → E)) (Λ' : Submodule (𝓞 E) (Fin k → E)), (∀ y, y ∈ Λ ↔ (fun _ => y 0) ∈ Λ₀ ∧ Fin.tail y ∈ Λ') → ∀ x : MatInf E (k + 1), (∀ w a, x w a 0 = if a = 0 then 1 else 0) → (x ∈ autGL E (k + 1) Λ ↔ (fun w a b => x w a.succ b.succ) ∈ autGL E k Λ' ∧ ∃ τ : Fin k → E, (∀ y ∈ Λ', (fun _ => τ ⬝ᵥ y) ∈ Λ₀) ∧ ∀ w b, x w 0 b.succ = w.embedding (τ b)) := by
  intro E _ _ k Λ Λ₀ Λ' hΛ x hx
  obtain ⟨w₀⟩ : Nonempty (InfinitePlace E) := inferInstance
  simp only [autGL, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨γ, hγ, hxγ⟩
    have hcol : ∀ a, (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) E) a 0 = if a = 0 then 1 else 0 := by
      intro a
      apply w₀.embedding.injective
      rw [← hxγ w₀ a 0, hx w₀ a]
      split_ifs <;> simp
    have hdet : (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) E).det ≠ 0 := (Matrix.isUnits_det_units γ).ne_zero
    rw [det_of_col _ hcol] at hdet
    obtain ⟨hA, hr⟩ := (preserves_iff Λ Λ₀ Λ' hΛ _ hcol).1 hγ
    exact ⟨⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet, hA, fun w a b => hxγ w a.succ b.succ⟩,
      fun b => (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) E) 0 b.succ, hr, fun w b => hxγ w 0 b.succ⟩
  · rintro ⟨⟨γ', hγ', hxγ'⟩, τ, hτ, hxτ⟩

    obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin (k + 1)) (Fin (k + 1)) E,
        M = Matrix.of (Fin.cons (Fin.cons 1 τ : Fin (k + 1) → E)
          (fun a => (Fin.cons 0 ((γ' : Matrix (Fin k) (Fin k) E) a) : Fin (k + 1) → E)) :
            Fin (k + 1) → Fin (k + 1) → E) := ⟨_, rfl⟩
    have hcol : ∀ a, M a 0 = if a = 0 then 1 else 0 := by
      intro a
      rcases Fin.eq_zero_or_eq_succ a with rfl | ⟨a, rfl⟩ <;> simp [hM, Fin.succ_ne_zero]
    have hsub : M.submatrix Fin.succ Fin.succ = (γ' : Matrix (Fin k) (Fin k) E) := by
      ext a b; simp [hM]
    have hrow : (fun b => M 0 (Fin.succ b)) = τ := by
      funext b; simp [hM]
    have hdet : M.det ≠ 0 := by
      rw [det_of_col M hcol, hsub]; exact (Matrix.isUnits_det_units γ').ne_zero
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero M hdet, ?_, ?_⟩
    · show ∀ y, M *ᵥ y ∈ Λ ↔ y ∈ Λ
      refine (preserves_iff Λ Λ₀ Λ' hΛ M hcol).2 ⟨?_, ?_⟩
      · rw [hsub]; exact hγ'
      · rw [hrow]; exact hτ
    · intro w a b
      show x w a b = w.embedding (M a b)
      rcases Fin.eq_zero_or_eq_succ a with rfl | ⟨a, rfl⟩ <;>
        rcases Fin.eq_zero_or_eq_succ b with rfl | ⟨b, rfl⟩
      · rw [hx]; simp [hM]
      · rw [hxτ]; simp [hM]
      · rw [hx]; simp [hM, Fin.succ_ne_zero]
      · refine (hxγ' w a b).trans ?_
        simp [hM]

end GlobalTheory.OrbitTerm
