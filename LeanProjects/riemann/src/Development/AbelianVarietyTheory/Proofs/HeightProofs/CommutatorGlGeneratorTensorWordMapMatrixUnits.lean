import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsLieDataCircle
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology

namespace GlobalTheory.SmoothForms

theorem commutator_prod_ofFn {A : Type} [Ring A] (x : A) :
    ∀ (d : ℕ) (f : Fin d → A), x * (List.ofFn f).prod - (List.ofFn f).prod * x =
      ∑ p, (List.ofFn (Function.update f p (x * f p - f p * x))).prod
  | 0, f => by simp
  | d + 1, f => by
    have ih := commutator_prod_ofFn x d (fun i => f i.succ)
    have h : ∀ (p : Fin d) (y : A), (fun i : Fin d => Function.update f p.succ y i.succ) =
        Function.update (fun i => f i.succ) p y := fun p y => by
      funext i
      by_cases h : i = p
      · subst h; simp
      · simp [Function.update_of_ne h, Function.update_of_ne (fun h' => h (Fin.succ_injective _ h'))]
    rw [Fin.sum_univ_succ]
    simp only [List.ofFn_succ, List.prod_cons, Function.update_self, h,
      Function.update_of_ne (Fin.succ_ne_zero _), Function.update_of_ne (Fin.succ_ne_zero _).symm]
    rw [← Finset.mul_sum, ← ih]
    noncomm_ring

theorem sum_polar_left {A : Type} [AddCommGroup A] [Module ℂ A] {n d : ℕ} (a b : Fin n) (I : Fin d → Fin n)
    (g : (Fin d → Fin n) → A) :
    ∑ J, polar n d a b J I • g J = ∑ p, if b = I p then g (Function.update I p a) else 0 := by
  simp only [polar, Matrix.of_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  have h : ∀ J : Fin d → Fin n, (J p = a ∧ I p = b ∧ ∀ q, q ≠ p → J q = I q) ↔
      (b = I p ∧ J = Function.update I p a) := fun J => by
    rw [Function.eq_update_iff]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨h2.symm, h1, h3⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨h2, h1.symm, h3⟩
  simp only [h]
  by_cases hb : b = I p <;> simp [hb]

theorem sum_polar_right {A : Type} [AddCommGroup A] [Module ℂ A] {n d : ℕ} (a b : Fin n) (K : Fin d → Fin n)
    (g : (Fin d → Fin n) → A) :
    ∑ J, polar n d a b K J • g J = ∑ p, if K p = a then g (Function.update K p b) else 0 := by
  simp only [polar, Matrix.of_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  have h : ∀ J : Fin d → Fin n, (K p = a ∧ J p = b ∧ ∀ q, q ≠ p → K q = J q) ↔
      (K p = a ∧ J = Function.update K p b) := fun J => by
    rw [Function.eq_update_iff]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, fun q hq => (h3 q hq).symm⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, fun q hq => (h3 q hq).symm⟩
  simp only [h]
  by_cases hb : K p = a <;> simp [hb]

theorem commutator_word {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} {E : Fin n → Fin n → A} (hE : Formalism.REAL.GlRel E)
    {d : ℕ} (a b : Fin n) (I K : Fin d → Fin n) :
    E a b * (List.ofFn fun q => E (I q) (K q)).prod - (List.ofFn fun q => E (I q) (K q)).prod * E a b =
      ∑ J, polar n d a b J I • (List.ofFn fun q => E (J q) (K q)).prod -
        ∑ J, polar n d a b K J • (List.ofFn fun q => E (I q) (J q)).prod := by
  rw [commutator_prod_ofFn, sum_polar_left, sum_polar_right, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  have h1 : (fun q => E (Function.update I p a q) (K q)) =
      Function.update (fun q => E (I q) (K q)) p (E a (K p)) := by
    funext q
    by_cases h : q = p
    · subst h; simp
    · simp [Function.update_of_ne h]
  have h2 : (fun q => E (I q) (Function.update K p b q)) =
      Function.update (fun q => E (I q) (K q)) p (E (I p) b) := by
    funext q
    by_cases h : q = p
    · subst h; simp
    · simp [Function.update_of_ne h]
  rw [h1, h2, hE a b (I p) (K p)]
  simp only [← MultilinearMap.mkPiAlgebraFin_apply (R := ℂ), MultilinearMap.map_update_sub]
  congr 1 <;> split_ifs <;> simp only [MultilinearMap.map_update_zero]

theorem commutator_wordMap : ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (E : Fin n → Fin n → A),
    Formalism.REAL.GlRel E → ∀ (d : ℕ) (a b : Fin n) (M : Matrix (Fin d → Fin n) (Fin d → Fin n) ℂ),
    E a b * wordMap E d M - wordMap E d M * E a b =
      wordMap E d (polar n d a b * M - M * polar n d a b) := by
  intro A _ _ n E hE d a b M
  have hw : ∀ N, wordMap E d N = ∑ I, ∑ K, N I K • (List.ofFn fun q : Fin d => E (I q) (K q)).prod := fun _ => rfl
  have hl : wordMap E d (polar n d a b * M) =
      ∑ I, ∑ K, M I K • ∑ J, polar n d a b J I • (List.ofFn fun q => E (J q) (K q)).prod := by
    simp only [hw, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun K _ => ?_
    rw [Finset.sum_comm]
    simp only [mul_comm]
  have hr : wordMap E d (M * polar n d a b) =
      ∑ I, ∑ K, M I K • ∑ J, polar n d a b K J • (List.ofFn fun q => E (I q) (J q)).prod := by
    simp only [hw, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [Finset.sum_comm]
  rw [map_sub, hl, hr, hw, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun K _ => ?_
  rw [← smul_sub, ← commutator_word hE, smul_sub, mul_smul_comm, smul_mul_assoc]

end GlobalTheory.SmoothForms
