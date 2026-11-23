import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RootExchangeStatement

open ReciprocityTheory.Ty.Fin

namespace GlobalTheory.CompanionTheory.TyFin

def chainUnion (m k t : ℕ) : Fin m ⊕ Fin k → Fin m ⊕ Fin k → Prop
  | .inl a, .inl a' => a < a'
  | .inr w, .inr w' => w < w'
  | .inl a, .inr _ => (a : ℕ) ≤ t
  | .inr _, .inl a => t + 1 ≤ (a : ℕ)

theorem chainUnion_isPat (m k t : ℕ) : IsPat (chainUnion m k t) := by
  constructor
  · rintro (a | w) <;> simp [chainUnion]
  · rintro (a | w) (b | v) (c | u) <;> simp only [chainUnion, Fin.lt_def] <;> omega

theorem chainUnion_remove_right (m k t : ℕ) (q : Fin m) (hq : (q : ℕ) = t + 1) :
    (fun i j => chainUnion m k t i j ∧ ¬ (Sum.isRight i = true ∧ j = Sum.inl q)) =
      chainPat m k (t + 1) := by
  funext i j
  apply propext
  rcases i with a | w <;> rcases j with b | v <;>
    simp only [chainUnion, chainPat, Fin.lt_def, Sum.isRight_inl, Sum.isRight_inr, Sum.inl.injEq,
      Sum.inr.injEq, reduceCtorEq, Bool.false_eq_true, false_and, and_false, true_and, and_true,
      not_false_eq_true, Fin.ext_iff] <;> omega

theorem chainUnion_remove_left (m k t : ℕ) (p : Fin m) (hp : (p : ℕ) = t) :
    (fun i j => chainUnion m k t i j ∧ ¬ (i = Sum.inl p ∧ Sum.isRight j = true)) =
      chainPat m k t := by
  funext i j
  apply propext
  rcases i with a | w <;> rcases j with b | v <;>
    simp only [chainUnion, chainPat, Fin.lt_def, Sum.isRight_inl, Sum.isRight_inr, Sum.inl.injEq,
      Sum.inr.injEq, reduceCtorEq, Bool.false_eq_true, false_and, and_false, true_and, and_true,
      not_false_eq_true, Fin.ext_iff] <;> omega

theorem chain_step (K : Type) [Field K] [Fintype K] [DecidableEq K] (m k t : ℕ) (ψ₀ : AddChar K ℂ)
    (χ : GL (Fin m ⊕ Fin k) K → ℂ) (hψ : ψ₀ ≠ 1) (hχ : ∀ x g, χ (x * g * x⁻¹) = χ g)
    (ht : t + 1 < m) :
    wh (chainPat m k (t + 1)) (chainE K m k) ψ₀ χ = wh (chainPat m k t) (chainE K m k) ψ₀ χ := by
  have hE : ∀ i j, chainE K m k i j ≠ 0 →
      (∃ a b : Fin m, i = Sum.inl a ∧ j = Sum.inl b ∧ (b : ℕ) = a + 1) ∨
      (∃ w v : Fin k, i = Sum.inr w ∧ j = Sum.inr v ∧ (v : ℕ) = w + 1) := by
    rintro (a | w) (b | v) h
    · left
      by_cases hab : (b : ℕ) = a + 1
      · exact ⟨a, b, rfl, rfl, hab⟩
      · simp [chainE, hab] at h
    · simp [chainE] at h
    · simp [chainE] at h
    · right
      by_cases hab : (v : ℕ) = w + 1
      · exact ⟨w, v, rfl, rfl, hab⟩
      · simp [chainE, hab] at h
  have h := GlobalTheory.T.root_exchange' K (Fin m ⊕ Fin k) (chainUnion m k t) (chainE K m k) ψ₀
    (fun x => Sum.isRight x = true) (Sum.inl ⟨t, by omega⟩) (Sum.inl ⟨t + 1, ht⟩) χ
    (chainUnion_isPat m k t) hψ hχ
    (by
      rintro (a | w) hw
      · simp at hw
      · simp [chainUnion])
    (by simp [chainE])
    (by
      intro i j hij
      rcases hE i j hij with ⟨a, b, rfl, rfl, hab⟩ | ⟨w, v, rfl, rfl, hab⟩ <;>
        simp only [chainUnion, Fin.lt_def] <;> omega)
    (by
      rintro (a | w) hw
      · simp at hw
      · simp [chainE])
    (by
      rintro (a | w) (b | v) hw h1 h2
      · simp at hw
      · simp at hw
      · simp only [chainUnion, Fin.lt_def] at h1 h2
        omega
      · rfl)
    (by
      rintro (a | w) (b | v) hw h1 h2
      · simp at hw
      · simp at hw
      · simp only [chainUnion, Fin.lt_def] at h1 h2
        omega
      · rfl)
    (by
      intro i j l hij hjl hil
      rcases hE i l hil with ⟨a, b, rfl, rfl, hab⟩ | ⟨w, v, rfl, rfl, hab⟩
      · rcases j with c | u
        · simp only [chainUnion, Fin.lt_def] at hij hjl
          omega
        · simp only [chainUnion] at hij hjl
          have h1 : (a : ℕ) = t := by omega
          refine ⟨?_, ?_, by simp⟩
          · simp [Fin.ext_iff, h1]
          · simp [Fin.ext_iff]; omega
      · rcases j with c | u
        · simp only [chainUnion] at hij hjl
          omega
        · simp only [chainUnion, Fin.lt_def] at hij hjl
          omega)
  rw [chainUnion_remove_right m k t ⟨t + 1, ht⟩ rfl,
    chainUnion_remove_left m k t ⟨t, by omega⟩ rfl] at h
  exact h

theorem chainIndep : ReciprocityTheory.Ty.Fin.St.ChainIndep := by
  intro K _ _ _ m k t ψ₀ χ hψ hχ ht
  induction t with
  | zero => rfl
  | succ t ih => rw [chain_step K m k t ψ₀ χ hψ hχ ht, ih (by omega)]

end GlobalTheory.CompanionTheory.TyFin
