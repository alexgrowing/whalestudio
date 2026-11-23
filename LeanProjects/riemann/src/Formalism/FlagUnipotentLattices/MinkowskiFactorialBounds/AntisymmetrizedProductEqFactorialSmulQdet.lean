import Formalism.FlagUnipotentLattices.QDetNegTranspose
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.LanglandsParameterEquivariant
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ShiftedGeneratorEqIteSmulAdd

open Formalism.HermitianLatticeCounting.S8 Formalism.REAL TensorProduct Finset

set_option linter.all false

noncomputable section

namespace Formalism.HermitianLatticeCounting.P

def orderedTermProduct {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (arg : Fin n → ℂ)
    (σ τ : Equiv.Perm (Fin n)) : A :=
  (List.ofFn fun k : Fin n => Tm E (arg k) (σ k) (τ k)).prod

def doublyAntisymmetrizedProduct {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (arg : Fin n → ℂ) : A :=
  ∑ τ : Equiv.Perm (Fin n), ∑ σ : Equiv.Perm (Fin n),
    ((Equiv.Perm.sign τ : ℤ) : A) * (((Equiv.Perm.sign σ : ℤ) : A) * orderedTermProduct E arg σ τ)

theorem term_two_by_two_exchange {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (x y : ℂ) (p q c d : Fin n) :
    Tm E x p c * Tm E y q d - Tm E x q c * Tm E y p d - Tm E x p d * Tm E y q c + Tm E x q d * Tm E y p c =
    Tm E y p c * Tm E x q d - Tm E y q c * Tm E x p d - Tm E y p d * Tm E x q c + Tm E y q d * Tm E x p c := by
  simp only [Tm, Algebra.algebraMap_eq_smul_one]
  split_ifs <;>
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, zero_add, zero_mul,
      mul_zero, add_zero, smul_smul, smul_zero, zero_smul] <;>
    module

theorem list_prod_ofFn_update_adjacent {A : Type} [Ring A] {t : ℕ} (f g : Fin t → A) (i : ℕ) (hi : i + 1 < t)
    (h : ∀ k : Fin t, (k : ℕ) ≠ i → (k : ℕ) ≠ i + 1 → g k = f k) :
    (List.ofFn g).prod = ((List.ofFn f).take i).prod * (g ⟨i, by omega⟩ * g ⟨i + 1, hi⟩) *
      ((List.ofFn f).drop (i + 2)).prod := by
  have hg : ∀ k : Fin t, (k : ℕ) ≠ i → (k : ℕ) ≠ i + 1 → g k = f k := h
  have htake : (List.ofFn g).take i = (List.ofFn f).take i := by
    apply List.ext_getElem
    · simp
    · intro j h1 h2
      simp only [List.getElem_take, List.getElem_ofFn]
      simp only [List.length_take, List.length_ofFn] at h1
      exact hg _ (by simp; omega) (by simp; omega)
  have hdrop : (List.ofFn g).drop (i + 2) = (List.ofFn f).drop (i + 2) := by
    apply List.ext_getElem
    · simp
    · intro j h1 h2
      simp only [List.getElem_drop, List.getElem_ofFn]
      exact hg _ (by simp; omega) (by simp; omega)
  rw [← List.take_append_drop i (List.ofFn g), List.drop_eq_getElem_cons (by simp; omega),
    List.drop_eq_getElem_cons (by simp; omega), htake, List.getElem_ofFn, List.getElem_ofFn,
    show i + 1 + 1 = i + 2 from rfl, hdrop]
  simp only [List.prod_append, List.prod_cons, mul_assoc]

theorem mul_signed_four_sum_mul_eq {A : Type} [Ring A] (L R a1 a2 a3 a4 : A) :
    L * a1 * R - L * a2 * R - L * a3 * R + L * a4 * R = L * (a1 - a2 - a3 + a4) * R := by
  noncomm_ring

theorem orderedProduct_adjacent_swap_identity {A : Type} [Ring A] [Algebra ℂ A] {m : ℕ} (E : Fin (m + 1) → Fin (m + 1) → A) (i : Fin m)
    (arg : Fin (m + 1) → ℂ) (σ τ : Equiv.Perm (Fin (m + 1))) :
    orderedTermProduct E arg σ τ - orderedTermProduct E arg (σ * Equiv.swap i.castSucc i.succ) τ - orderedTermProduct E arg σ (τ * Equiv.swap i.castSucc i.succ)
        + orderedTermProduct E arg (σ * Equiv.swap i.castSucc i.succ) (τ * Equiv.swap i.castSucc i.succ) =
    orderedTermProduct E (arg ∘ Equiv.swap i.castSucc i.succ) σ τ
        - orderedTermProduct E (arg ∘ Equiv.swap i.castSucc i.succ) (σ * Equiv.swap i.castSucc i.succ) τ
        - orderedTermProduct E (arg ∘ Equiv.swap i.castSucc i.succ) σ (τ * Equiv.swap i.castSucc i.succ)
        + orderedTermProduct E (arg ∘ Equiv.swap i.castSucc i.succ) (σ * Equiv.swap i.castSucc i.succ)
            (τ * Equiv.swap i.castSucc i.succ) := by
  have hi : (i : ℕ) + 1 < m + 1 := by omega
  have hfix : ∀ k : Fin (m + 1), (k : ℕ) ≠ i → (k : ℕ) ≠ i + 1 → Equiv.swap i.castSucc i.succ k = k := by
    intro k h1 h2
    refine Equiv.swap_apply_of_ne_of_ne (fun h => h1 ?_) (fun h => h2 ?_)
    · subst h
      simp
    · subst h
      simp

  have hM : ∀ (a : Fin (m + 1) → ℂ) (σ' τ' : Equiv.Perm (Fin (m + 1))),
      (∀ k : Fin (m + 1), (k : ℕ) ≠ i → (k : ℕ) ≠ i + 1 → a k = arg k ∧ σ' k = σ k ∧ τ' k = τ k) →
      orderedTermProduct E a σ' τ' = ((List.ofFn fun k => Tm E (arg k) (σ k) (τ k)).take i).prod *
        (Tm E (a ⟨i, by omega⟩) (σ' ⟨i, by omega⟩) (τ' ⟨i, by omega⟩) *
          Tm E (a ⟨i + 1, hi⟩) (σ' ⟨i + 1, hi⟩) (τ' ⟨i + 1, hi⟩)) *
        ((List.ofFn fun k => Tm E (arg k) (σ k) (τ k)).drop (i + 2)).prod := by
    intro a σ' τ' hk
    unfold orderedTermProduct
    exact list_prod_ofFn_update_adjacent (fun k => Tm E (arg k) (σ k) (τ k)) (fun k => Tm E (a k) (σ' k) (τ' k)) i hi
      (fun k h1 h2 => by obtain ⟨e1, e2, e3⟩ := hk k h1 h2; rw [e1, e2, e3])
  have hc : ∀ k : Fin (m + 1), (k : ℕ) ≠ i → (k : ℕ) ≠ i + 1 →
      (arg ∘ Equiv.swap i.castSucc i.succ) k = arg k ∧ (σ * Equiv.swap i.castSucc i.succ) k = σ k ∧
        (τ * Equiv.swap i.castSucc i.succ) k = τ k := by
    intro k h1 h2
    simp [Equiv.Perm.mul_apply, hfix k h1 h2]
  rw [hM arg σ τ (fun k _ _ => ⟨rfl, rfl, rfl⟩),
    hM arg (σ * Equiv.swap i.castSucc i.succ) τ (fun k h1 h2 => ⟨rfl, (hc k h1 h2).2.1, rfl⟩),
    hM arg σ (τ * Equiv.swap i.castSucc i.succ) (fun k h1 h2 => ⟨rfl, rfl, (hc k h1 h2).2.2⟩),
    hM arg (σ * Equiv.swap i.castSucc i.succ) (τ * Equiv.swap i.castSucc i.succ)
      (fun k h1 h2 => ⟨rfl, (hc k h1 h2).2.1, (hc k h1 h2).2.2⟩),
    hM (arg ∘ Equiv.swap i.castSucc i.succ) σ τ (fun k h1 h2 => ⟨(hc k h1 h2).1, rfl, rfl⟩),
    hM (arg ∘ Equiv.swap i.castSucc i.succ) (σ * Equiv.swap i.castSucc i.succ) τ
      (fun k h1 h2 => ⟨(hc k h1 h2).1, (hc k h1 h2).2.1, rfl⟩),
    hM (arg ∘ Equiv.swap i.castSucc i.succ) σ (τ * Equiv.swap i.castSucc i.succ)
      (fun k h1 h2 => ⟨(hc k h1 h2).1, rfl, (hc k h1 h2).2.2⟩),
    hM (arg ∘ Equiv.swap i.castSucc i.succ) (σ * Equiv.swap i.castSucc i.succ)
      (τ * Equiv.swap i.castSucc i.succ) (fun k h1 h2 => hc k h1 h2)]
  have e0 : (⟨i, by omega⟩ : Fin (m + 1)) = i.castSucc := Fin.ext rfl
  have e1 : (⟨i + 1, hi⟩ : Fin (m + 1)) = i.succ := Fin.ext rfl
  simp only [e0, e1, Equiv.Perm.mul_apply, Function.comp_apply, Equiv.swap_apply_left,
    Equiv.swap_apply_right]
  rw [mul_signed_four_sum_mul_eq, mul_signed_four_sum_mul_eq, term_two_by_two_exchange]

theorem antisymmetrizedProduct_adjacent_swap {A : Type} [Ring A] [Algebra ℂ A] {m : ℕ} (E : Fin (m + 1) → Fin (m + 1) → A) (i : Fin m)
    (arg : Fin (m + 1) → ℂ) : doublyAntisymmetrizedProduct E (arg ∘ Equiv.swap i.castSucc i.succ) = doublyAntisymmetrizedProduct E arg := by
  have hne : i.castSucc ≠ i.succ := (Fin.castSucc_lt_succ (i := i)).ne
  have key := orderedProduct_adjacent_swap_identity E i arg
  generalize hs : Equiv.swap i.castSucc i.succ = s at key ⊢
  have hsg : Equiv.Perm.sign s = -1 := by rw [← hs]; exact Equiv.Perm.sign_swap hne

  have hre : ∀ F : Equiv.Perm (Fin (m + 1)) → A,
      ∑ σ, ((Equiv.Perm.sign σ : ℤ) : A) * F (σ * s) = -∑ σ, ((Equiv.Perm.sign σ : ℤ) : A) * F σ := by
    intro F
    rw [← Equiv.sum_comp (Equiv.mulRight s) (fun σ => ((Equiv.Perm.sign σ : ℤ) : A) * F σ)]
    simp [Equiv.Perm.sign_mul, hsg]
  have q1 : ∀ a : Fin (m + 1) → ℂ, ∑ τ, ∑ σ, ((Equiv.Perm.sign τ : ℤ) : A) *
      (((Equiv.Perm.sign σ : ℤ) : A) * orderedTermProduct E a (σ * s) τ) = -doublyAntisymmetrizedProduct E a := by
    intro a
    simp only [doublyAntisymmetrizedProduct, ← Finset.mul_sum]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun τ _ => ?_
    have h := hre (fun σ => orderedTermProduct E a σ τ)
    rw [h, mul_neg]
  have q2 : ∀ a : Fin (m + 1) → ℂ, ∑ τ, ∑ σ, ((Equiv.Perm.sign τ : ℤ) : A) *
      (((Equiv.Perm.sign σ : ℤ) : A) * orderedTermProduct E a σ (τ * s)) = -doublyAntisymmetrizedProduct E a := by
    intro a
    simp only [doublyAntisymmetrizedProduct, ← Finset.mul_sum]
    have h := hre (fun τ => ∑ σ, ((Equiv.Perm.sign σ : ℤ) : A) * orderedTermProduct E a σ τ)
    exact h
  have q3 : ∀ a : Fin (m + 1) → ℂ, ∑ τ, ∑ σ, ((Equiv.Perm.sign τ : ℤ) : A) *
      (((Equiv.Perm.sign σ : ℤ) : A) * orderedTermProduct E a (σ * s) (τ * s)) = doublyAntisymmetrizedProduct E a := by
    intro a
    simp only [← Finset.mul_sum]
    have h1 : ∀ τ, ∑ σ, ((Equiv.Perm.sign σ : ℤ) : A) * orderedTermProduct E a (σ * s) (τ * s) =
        -∑ σ, ((Equiv.Perm.sign σ : ℤ) : A) * orderedTermProduct E a σ (τ * s) := by
      intro τ
      have h := hre (fun σ => orderedTermProduct E a σ (τ * s))
      exact h
    simp only [h1, mul_neg, Finset.sum_neg_distrib]
    have h := hre (fun τ => ∑ σ, ((Equiv.Perm.sign σ : ℤ) : A) * orderedTermProduct E a σ τ)
    rw [h, neg_neg]
    simp only [doublyAntisymmetrizedProduct, Finset.mul_sum]
  have T_eq : ∀ a : Fin (m + 1) → ℂ, ∑ τ, ∑ σ, ((Equiv.Perm.sign τ : ℤ) : A) *
      (((Equiv.Perm.sign σ : ℤ) : A) * (orderedTermProduct E a σ τ - orderedTermProduct E a (σ * s) τ - orderedTermProduct E a σ (τ * s) +
        orderedTermProduct E a (σ * s) (τ * s))) = 4 • doublyAntisymmetrizedProduct E a := by
    intro a
    simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [q1 a, q2 a, q3 a]
    simp only [doublyAntisymmetrizedProduct]
    abel
  have h4 : 4 • doublyAntisymmetrizedProduct E arg = 4 • doublyAntisymmetrizedProduct E (arg ∘ s) := by
    rw [← T_eq arg, ← T_eq (arg ∘ s)]
    exact Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun σ _ => by rw [key σ τ]
  have h4' : (4 : ℂ) • doublyAntisymmetrizedProduct E arg = (4 : ℂ) • doublyAntisymmetrizedProduct E (arg ∘ s) := by
    rw [show (4 : ℂ) = ((4 : ℕ) : ℂ) by norm_num, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
    exact h4
  exact (smul_right_injective A (by norm_num : (4 : ℂ) ≠ 0) h4').symm

theorem antisymmetrizedProduct_perm_invariant {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (π : Equiv.Perm (Fin n))
    (arg : Fin n → ℂ) : doublyAntisymmetrizedProduct E (arg ∘ π) = doublyAntisymmetrizedProduct E arg := by
  cases n with
  | zero =>
    have h : arg ∘ π = arg := funext fun k => k.elim0
    rw [h]
  | succ m =>
    have hπ : π ∈ Submonoid.closure (Set.range fun i : Fin m => Equiv.swap i.castSucc i.succ) := by
      rw [Equiv.Perm.mclosure_swap_castSucc_succ]
      trivial
    revert arg
    induction hπ using Submonoid.closure_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      intro arg
      exact antisymmetrizedProduct_adjacent_swap E i arg
    | one =>
      intro arg
      rfl
    | mul x y _ _ hx hy =>
      intro arg
      show doublyAntisymmetrizedProduct E ((arg ∘ x) ∘ y) = _
      rw [hy (arg ∘ x), hx arg]

theorem antisymmetrizedProduct_eq_factorial_smul_qdet {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (hE : GlRel E) (u : ℂ) :
    doublyAntisymmetrizedProduct E (fun k => u - (k : ℂ)) = (n.factorial : ℂ) • qdet E u := by

  have hcol : ∀ (b : Fin n → Fin n) (τ : Equiv.Perm (Fin n)),
      qminor E id (b ∘ τ) u = ((Equiv.Perm.sign τ : ℤ) : A) * qminor E id b u := by
    cases n with
    | zero =>
      intro b τ
      rw [Subsingleton.elim τ 1]
      simp
    | succ m =>
      intro b τ
      have hτ : τ ∈ Submonoid.closure (Set.range fun i : Fin m => Equiv.swap i.castSucc i.succ) := by
        rw [Equiv.Perm.mclosure_swap_castSucc_succ]
        trivial
      revert b
      induction hτ using Submonoid.closure_induction with
      | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        intro b
        rw [quantumMinor_adjacent_col_swap E hE id b i u, Equiv.Perm.sign_swap (Fin.castSucc_lt_succ (i := i)).ne]
        simp
      | one =>
        intro b
        simp
      | mul x y _ _ hx hy =>
        intro b
        show qminor E id ((b ∘ x) ∘ y) u = _
        rw [hy (b ∘ x), hx b]
        simp only [Equiv.Perm.sign_mul, Units.val_mul, Int.cast_mul, ← mul_assoc]
        congr 1
        exact (Int.cast_commute _ _).eq
  simp only [doublyAntisymmetrizedProduct, ← Finset.mul_sum]
  have hin : ∀ τ : Equiv.Perm (Fin n), ∑ σ, ((Equiv.Perm.sign σ : ℤ) : A) *
      orderedTermProduct E (fun k => u - (k : ℂ)) σ τ = qminor E id (id ∘ τ) u := fun τ => rfl
  have hsq : ∀ τ : Equiv.Perm (Fin n), ((Equiv.Perm.sign τ : ℤ) : A) *
      (((Equiv.Perm.sign τ : ℤ) : A) * qminor E id id u) = qminor E id id u := by
    intro τ
    rw [← mul_assoc, ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one,
      one_mul]
  simp only [hin, hcol, hsq, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℂ]
  rfl

theorem term_neg_transpose {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (y : ℂ) (a b : Fin n) :
    Tm (fun a b => -E b a) y a b = -Tm E (-y) b a := by
  simp only [Tm]
  by_cases h : a = b
  · subst h
    rw [if_pos rfl, if_pos rfl, map_neg]
    abel
  · rw [if_neg h, if_neg (Ne.symm h)]
    simp

theorem orderedTermProduct_neg_transpose {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (arg : Fin n → ℂ)
    (σ τ : Equiv.Perm (Fin n)) :
    orderedTermProduct (fun a b => -E b a) arg σ τ = (-1) ^ n * orderedTermProduct E (fun k => -arg k) τ σ := by
  simp only [orderedTermProduct]
  have h : (fun k : Fin n => Tm (fun a b => -E b a) (arg k) (σ k) (τ k)) =
      fun k => -(Tm E (-arg k) (τ k) (σ k)) := funext fun k => term_neg_transpose E (arg k) (σ k) (τ k)
  rw [h, show (List.ofFn fun k => -(Tm E (-arg k) (τ k) (σ k))) =
      (List.ofFn fun k => Tm E (-arg k) (τ k) (σ k)).map Neg.neg by rw [List.map_ofFn]; rfl,
    List.prod_map_neg, List.length_ofFn]

theorem antisymmetrizedProduct_neg_transpose {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (arg : Fin n → ℂ) :
    doublyAntisymmetrizedProduct (fun a b => -E b a) arg = (-1) ^ n * doublyAntisymmetrizedProduct E (fun k => -arg k) := by
  simp only [doublyAntisymmetrizedProduct, orderedTermProduct_neg_transpose]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun κ _ => ?_

  rw [show ((-1 : A)) ^ n = (((-1 : ℤ) ^ n : ℤ) : A) by push_cast; rfl]
  simp only [← zsmul_eq_mul, smul_smul]
  congr 1
  ring

theorem quantumDet_neg_transpose {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (hE : GlRel E) (x : ℂ) :
    qdet (fun a b => -E b a) x = ((-1 : ℂ) ^ n) • qdet E ((n : ℂ) - 1 - x) := by
  have hE' : GlRel (fun a b => -E b a) := by
    intro a b c d
    have h := hE b a d c
    simp only [neg_mul_neg]
    rw [h]
    by_cases h1 : a = d <;> by_cases h2 : c = b
    · subst h1 h2
      simp
      abel
    · subst h1
      simp [h2, Ne.symm h2]
    · subst h2
      simp [h1, Ne.symm h1]
    · simp [h1, h2, Ne.symm h1, Ne.symm h2]
  have h1 := antisymmetrizedProduct_eq_factorial_smul_qdet (fun a b => -E b a) hE' x
  have h2 := antisymmetrizedProduct_neg_transpose E (fun k => x - (k : ℂ))
  have h3 : (fun k : Fin n => -(x - (k : ℂ))) = (fun k : Fin n => ((n : ℂ) - 1 - x) - (k : ℂ)) ∘ Fin.revPerm := by
    funext k
    simp only [Function.comp_apply, Fin.revPerm_apply, Fin.val_rev]
    rw [Nat.cast_sub (Nat.succ_le_of_lt k.isLt)]
    push_cast
    ring
  have h4 := antisymmetrizedProduct_perm_invariant E Fin.revPerm (fun k : Fin n => ((n : ℂ) - 1 - x) - (k : ℂ))
  have h5 := antisymmetrizedProduct_eq_factorial_smul_qdet E hE ((n : ℂ) - 1 - x)
  refine smul_right_injective A (by exact_mod_cast n.factorial_ne_zero : ((n.factorial : ℕ) : ℂ) ≠ 0) ?_
  show ((n.factorial : ℕ) : ℂ) • qdet (fun a b => -E b a) x = ((n.factorial : ℕ) : ℂ) • (((-1 : ℂ) ^ n) • qdet E ((n : ℂ) - 1 - x))
  rw [← h1, h2, h3, h4, h5, smul_comm, Algebra.smul_def ((-1 : ℂ) ^ n)]
  simp

end Formalism.HermitianLatticeCounting.P
