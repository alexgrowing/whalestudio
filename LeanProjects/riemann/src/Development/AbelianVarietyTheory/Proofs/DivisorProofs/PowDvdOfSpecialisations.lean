import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

set_option autoImplicit false

namespace GlobalTheory.HSShortDiv

variable {F : Type} [Field F] {D N : ℕ}

noncomputable def lastSubst (l₀ : Fin N → F) : Fin (D + 1) × Fin N → MvPolynomial (Fin (D + 1) × Fin N) F :=
  fun p => if p.1 = Fin.last D then C (l₀ p.2) else X p

theorem eval_aeval_lastSubst (l₀ : Fin N → F) (x : Fin (D + 1) × Fin N → F)
    (f : MvPolynomial (Fin (D + 1) × Fin N) F) :
    eval x (aeval (lastSubst l₀) f) = eval (fun p => if p.1 = Fin.last D then l₀ p.2 else x p) f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add]
  | mul_X p q hp =>
    simp only [map_mul, hp, aeval_X, eval_X, lastSubst]
    split_ifs <;> simp

theorem replace_eq_join (l : Fin N → F) (x : Fin (D + 1) × Fin N → F) :
    (fun p : Fin (D + 1) × Fin N => if p.1 = Fin.last D then l p.2 else x p) =
      join (fun i j => x (i.castSucc, j)) l := by
  funext ⟨i, j⟩
  induction i using Fin.lastCases with
  | last => simp [join]
  | cast i => simp [join, Fin.castSucc_ne_last]

theorem eval_last_zero {δ : ℕ} (hδ : 1 ≤ δ) (f : MvPolynomial (Fin (D + 1) × Fin N) F)
    (hf : IsMultiHomogeneous (fun _ => δ) f) (x : Fin (D + 1) × Fin N → F) :
    eval (fun p => if p.1 = Fin.last D then 0 else x p) f = 0 := by
  rw [eval_eq']
  refine Finset.sum_eq_zero fun d hd => ?_
  have hs := hf d hd (Fin.last D)
  have hne : (∑ j : Fin N, d (Fin.last D, j)) ≠ 0 := by simp only at hs; omega
  obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  refine mul_eq_zero_of_right _ (Finset.prod_eq_zero (i := (Fin.last D, j)) (Finset.mem_univ _) ?_)
  simp [zero_pow hj]

theorem pow_dvd_of_specialisations (F : Type) [Field F] [CharZero F] (D N δ b : ℕ) (f G : MvPolynomial (Fin (D + 1) × Fin N) F)
    (Q : MvPolynomial (Fin D × Fin N) F) (hδ : 1 ≤ δ) (hf : IsMultiHomogeneous (fun _ => δ) f)
    (hirr : Irreducible f) (hQ : Q ≠ 0)
    (hG : ∀ s : Fin D → Fin N → F, eval (fun p => s p.1 p.2) Q ≠ 0 → ∃ (E : Type) (_ : Field E)
      (_ : Algebra F E) (γ : E), ∀ l : Fin N → F,
        algebraMap F E (eval (join s l) G) = γ * algebraMap F E (eval (join s l) f) ^ b) :
    f ^ b ∣ G := by
  haveI : Infinite F := Infinite.of_injective Nat.cast Nat.cast_injective
  have hf0 : f ≠ 0 := hirr.ne_zero

  obtain ⟨x₀, hx₀⟩ : ∃ x₀, eval x₀ f ≠ 0 := by
    by_contra h
    push_neg at h
    exact hf0 (MvPolynomial.funext fun x => by simp [h x])
  set l₀ : Fin N → F := fun j => x₀ (Fin.last D, j) with hl₀
  set g := aeval (lastSubst l₀) f with hg
  set G₀ := aeval (lastSubst l₀) G with hG₀
  set Q' : MvPolynomial (Fin (D + 1) × Fin N) F :=
    rename (fun p : Fin D × Fin N => (p.1.castSucc, p.2)) Q with hQ'
  have hQ'0 : Q' ≠ 0 := by
    intro h
    apply hQ
    apply rename_injective _ _ (h.trans (map_zero _).symm)
    intro p q hpq
    simp only [Prod.mk.injEq, Fin.castSucc_inj] at hpq
    exact Prod.ext hpq.1 hpq.2

  have key : Q' * (G * g ^ b - f ^ b * G₀) = 0 := by
    apply MvPolynomial.funext
    intro x
    set s : Fin D → Fin N → F := fun i j => x (i.castSucc, j) with hs
    have hx : x = join s (fun j => x (Fin.last D, j)) := by
      rw [← replace_eq_join]
      funext p
      split_ifs with h
      · rw [← h]
      · rfl
    have hQx : eval x Q' = eval (fun p => s p.1 p.2) Q := by
      rw [hQ', eval_rename]; rfl
    simp only [map_mul, map_sub, map_pow, map_zero]
    by_cases hq : eval (fun p => s p.1 p.2) Q = 0
    · rw [hQx, hq, zero_mul]
    · obtain ⟨E, _, _, γ, hγ⟩ := hG s hq
      have h1 := hγ (fun j => x (Fin.last D, j))
      have h2 := hγ l₀
      rw [← hx] at h1
      have hgx : eval x g = eval (join s l₀) f := by rw [hg, eval_aeval_lastSubst, replace_eq_join]
      have hGx : eval x G₀ = eval (join s l₀) G := by rw [hG₀, eval_aeval_lastSubst, replace_eq_join]
      rw [hgx, hGx]
      have : eval x G * eval (join s l₀) f ^ b - eval x f ^ b * eval (join s l₀) G = 0 := by
        apply (algebraMap F E).injective
        simp only [map_sub, map_mul, map_pow, map_zero, h1, h2]
        ring
      rw [this, mul_zero]
  have heq : G * g ^ b = f ^ b * G₀ := by
    have := (mul_eq_zero.mp key).resolve_left hQ'0
    exact sub_eq_zero.mp this
  have hp : Prime f := hirr.prime

  have hndvd : ¬ f ∣ g := by
    rintro ⟨h, hh⟩
    have hg0 : g ≠ 0 := by
      intro h0
      have := congrArg (eval x₀) h0
      rw [hg, eval_aeval_lastSubst, map_zero] at this
      apply hx₀
      have hpt : (fun p : Fin (D + 1) × Fin N => if p.1 = Fin.last D then l₀ p.2 else x₀ p) = x₀ := by
        funext p
        split_ifs with hp1
        · rw [hl₀]; simp only; rw [← hp1]
        · rfl
      rw [hpt] at this
      exact this
    apply hg0
    apply MvPolynomial.funext
    intro x
    have e1 : eval x g = eval (fun p => if p.1 = Fin.last D then 0 else x p) g := by
      rw [hg, eval_aeval_lastSubst, eval_aeval_lastSubst]
      have hpt : (fun p : Fin (D + 1) × Fin N => if p.1 = Fin.last D then l₀ p.2 else x p) =
          (fun p => if p.1 = Fin.last D then l₀ p.2 else if p.1 = Fin.last D then 0 else x p) := by
        funext p
        split_ifs <;> rfl
      rw [hpt]
    rw [e1, hh, map_mul, eval_last_zero hδ f hf, zero_mul, map_zero]
  have hndvd' : ¬ f ∣ g ^ b := fun h => hndvd (hp.dvd_of_dvd_pow h)
  exact hp.pow_dvd_of_dvd_mul_right b hndvd' ⟨G₀, heq⟩

end GlobalTheory.HSShortDiv
