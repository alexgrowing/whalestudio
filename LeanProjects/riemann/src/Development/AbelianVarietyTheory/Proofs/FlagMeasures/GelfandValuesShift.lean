import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsIsHaarMeasureSUJ
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.DSSU
open scoped InnerProductSpace

noncomputable section
namespace GlobalTheory.GelfValSym

theorem tot_eq {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    ∑ a, ∑ b, M a b = (fun _ => (1 : ℂ)) ⬝ᵥ (M *ᵥ fun _ => (1 : ℂ)) := by
  simp [dotProduct, mulVec]

theorem amat_add_const {n : ℕ} (l : Fin n → ℂ) (t : ℂ) :
    Formalism.REAL.Amat (fun a => l a + t) = Formalism.REAL.Amat l + t • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  ext a b
  by_cases h : a = b
  · subst h; simp [Formalism.REAL.Amat]
  · simp [Formalism.REAL.Amat, h, Matrix.one_apply_ne h]

theorem rowdiff {n : ℕ} (l : Fin n → ℂ) (p q : Fin n) (hpq : q.val = p.val + 1) (b : Fin n) :
    Formalism.REAL.Amat l p b - Formalism.REAL.Amat l q b =
      if b = p then l p else if b = q then -1 - l q else 0 := by
  simp only [Formalism.REAL.Amat, Matrix.of_apply]
  by_cases hbp : b = p
  · subst hbp
    have h1 : q ≠ b := by intro h; rw [h] at hpq; omega
    have h2 : ¬ q < b := by rw [Fin.lt_def]; omega
    simp [h1, h2]
  · by_cases hbq : b = q
    · subst hbq
      have h2 : p < b := by rw [Fin.lt_def]; omega
      have h3 : p ≠ b := Ne.symm hbp
      simp [hbp, h2, h3]
    · have e1 : p ≠ b := Ne.symm hbp
      have e2 : q ≠ b := Ne.symm hbq
      simp only [e1, e2, hbp, hbq, if_false]
      have : (p < b ↔ q < b) := by
        rw [Fin.lt_def, Fin.lt_def]
        have : b.val ≠ p.val := fun h => hbp (Fin.ext h)
        have : b.val ≠ q.val := fun h => hbq (Fin.ext h)
        omega
      by_cases h : q < b
      · simp [h, this.mpr h]
      · simp [h, mt this.mp h]

theorem coldiff {n : ℕ} (l : Fin n → ℂ) (p q : Fin n) (hpq : q.val = p.val + 1) (a : Fin n) :
    Formalism.REAL.Amat (l ∘ Equiv.swap p q) a p - Formalism.REAL.Amat (l ∘ Equiv.swap p q) a q =
      if a = p then l q + 1 else if a = q then - l p else 0 := by
  have hne : p ≠ q := by intro h; rw [h] at hpq; omega
  simp only [Formalism.REAL.Amat, Matrix.of_apply, Function.comp_apply]
  by_cases hap : a = p
  · subst hap
    have h2 : a < q := by rw [Fin.lt_def]; omega
    simp [hne, h2]
  · by_cases haq : a = q
    · subst haq
      have h1 : ¬ a < p := by rw [Fin.lt_def]; omega
      simp [hap, h1, Equiv.swap_apply_right]
    · simp only [hap, haq, if_false]
      have : (a < p ↔ a < q) := by
        rw [Fin.lt_def, Fin.lt_def]
        have : a.val ≠ p.val := fun h => hap (Fin.ext h)
        have : a.val ≠ q.val := fun h => haq (Fin.ext h)
        omega
      by_cases h : a < p
      · simp [h, this.mp h]
      · simp [h, mt this.mpr h]

theorem amat_sub_swap {n : ℕ} (l : Fin n → ℂ) (p q : Fin n) (a b : Fin n) :
    Formalism.REAL.Amat l a b - Formalism.REAL.Amat (l ∘ Equiv.swap p q) a b =
      if a = b then l a - l (Equiv.swap p q a) else 0 := by
  simp only [Formalism.REAL.Amat, Matrix.of_apply, Function.comp_apply]
  split_ifs <;> ring

theorem w_vecMul {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (p q : Fin n) (b : Fin n) :
    ((Pi.single p 1 - Pi.single q 1 : Fin n → ℂ) ᵥ* M) b = M p b - M q b := by
  simp [vecMul, dotProduct, Pi.single_apply, sub_mul, Finset.sum_sub_distrib]

theorem w_mulVec {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (p q : Fin n) (a : Fin n) :
    (M *ᵥ (Pi.single p 1 - Pi.single q 1 : Fin n → ℂ)) a = M a p - M a q := by
  simp [mulVec, dotProduct, Pi.single_apply, mul_sub, Finset.sum_sub_distrib]

theorem amat_swap_semiconj {n : ℕ} (l : Fin n → ℂ) (p q : Fin n) (hpq : q.val = p.val + 1)
    (t : ℂ) (ht : t * (l p - l q - 1) = l p - l q) :
    (1 - t • vecMulVec (Pi.single p 1 - Pi.single q 1) (Pi.single p 1 - Pi.single q 1)) * Formalism.REAL.Amat l =
      Formalism.REAL.Amat (l ∘ Equiv.swap p q) *
        (1 - t • vecMulVec (Pi.single p 1 - Pi.single q 1) (Pi.single p 1 - Pi.single q 1)) := by
  have hne : p ≠ q := by intro h; rw [h] at hpq; omega
  rw [sub_mul, mul_sub, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul, vecMulVec_mul, mul_vecMulVec]
  ext a b
  simp only [Matrix.sub_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul]
  rw [w_vecMul, w_mulVec, rowdiff l p q hpq, coldiff l p q hpq]
  have hd := amat_sub_swap l p q a b
  rw [← sub_eq_zero]
  have key : (if a = b then l a - l (Equiv.swap p q a) else 0) -
      t * ((Pi.single p 1 - Pi.single q 1 : Fin n → ℂ) a *
        (if b = p then l p else if b = q then -1 - l q else 0)) +
      t * ((if a = p then l q + 1 else if a = q then - l p else 0) *
        (Pi.single p 1 - Pi.single q 1 : Fin n → ℂ) b) = 0 := by
    simp only [Pi.sub_apply, Pi.single_apply]
    have hqp : q ≠ p := Ne.symm hne
    by_cases hab : a = b
    · subst hab
      by_cases hap : a = p
      · subst hap; simp [hne]; linear_combination -ht
      · by_cases haq : a = q
        · subst haq; simp [hqp, Equiv.swap_apply_right]; linear_combination ht
        · simp [hap, haq, Equiv.swap_apply_of_ne_of_ne hap haq]
    · by_cases hap : a = p <;> by_cases haq : a = q <;> by_cases hbp : b = p <;> by_cases hbq : b = q <;>
        (try subst hap) <;> (try subst haq) <;> (try subst hbp) <;> (try subst hbq) <;>
        simp_all <;> first | ring | linear_combination ht | linear_combination -ht | linear_combination (2 : ℂ) * ht | linear_combination (-2 : ℂ) * ht
  linear_combination key + hd

theorem tot_swap_of {n : ℕ} (l : Fin n → ℂ) (p q : Fin n) (hpq : q.val = p.val + 1)
    (hd : l p - l q - 1 ≠ 0) (k : ℕ) :
    ∑ a, ∑ b, (Formalism.REAL.Amat (l ∘ Equiv.swap p q) ^ k) a b = ∑ a, ∑ b, (Formalism.REAL.Amat l ^ k) a b := by
  set t : ℂ := (l p - l q) / (l p - l q - 1) with ht_def
  have ht : t * (l p - l q - 1) = l p - l q := by rw [ht_def]; field_simp
  set w : Fin n → ℂ := Pi.single p 1 - Pi.single q 1 with hw
  have hne : p ≠ q := by intro h; rw [h] at hpq; omega
  have hsum : ∑ c, w c = 0 := by simp [hw, Finset.sum_sub_distrib]
  set Q : Matrix (Fin n) (Fin n) ℂ := 1 - t • vecMulVec w w with hQ_def
  have hQ : SemiconjBy Q (Formalism.REAL.Amat l) (Formalism.REAL.Amat (l ∘ Equiv.swap p q)) :=
    amat_swap_semiconj l p q hpq t ht
  have hk := hQ.pow_right k
  have hl : (fun _ => (1 : ℂ)) ᵥ* Q = fun _ => 1 := by
    funext b
    simp only [hQ_def, vecMul_sub, vecMul_one, vecMul_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    have : ((fun _ => (1 : ℂ)) ᵥ* vecMulVec w w) b = 0 := by
      simp [vecMul, dotProduct, vecMulVec_apply, ← Finset.sum_mul, hsum]
    rw [this, mul_zero, sub_zero]
  have hr : Q *ᵥ (fun _ => (1 : ℂ)) = fun _ => 1 := by
    funext a
    simp only [hQ_def, sub_mulVec, one_mulVec, Pi.sub_apply]
    have : ((t • vecMulVec w w) *ᵥ (fun _ => (1 : ℂ))) a = 0 := by
      simp [mulVec, dotProduct, vecMulVec_apply, ← Finset.mul_sum, hsum]
    rw [this, sub_zero]
  rw [tot_eq, tot_eq]
  calc (fun _ => (1 : ℂ)) ⬝ᵥ (Formalism.REAL.Amat (l ∘ Equiv.swap p q) ^ k *ᵥ fun _ => 1)
      = (fun _ => (1 : ℂ)) ⬝ᵥ (Formalism.REAL.Amat (l ∘ Equiv.swap p q) ^ k *ᵥ (Q *ᵥ fun _ => 1)) := by rw [hr]
    _ = (fun _ => (1 : ℂ)) ⬝ᵥ ((Formalism.REAL.Amat (l ∘ Equiv.swap p q) ^ k * Q) *ᵥ fun _ => 1) := by
        rw [mulVec_mulVec]
    _ = (fun _ => (1 : ℂ)) ⬝ᵥ ((Q * Formalism.REAL.Amat l ^ k) *ᵥ fun _ => 1) := by rw [hk.eq]
    _ = (fun _ => (1 : ℂ)) ⬝ᵥ (Q *ᵥ (Formalism.REAL.Amat l ^ k *ᵥ fun _ => 1)) := by rw [mulVec_mulVec]
    _ = ((fun _ => (1 : ℂ)) ᵥ* Q) ⬝ᵥ (Formalism.REAL.Amat l ^ k *ᵥ fun _ => 1) := dotProduct_mulVec _ _ _
    _ = _ := by rw [hl]

theorem tot_swap {n : ℕ} (l : Fin n → ℂ) (p q : Fin n) (hpq : q.val = p.val + 1) (k : ℕ) :
    ∑ a, ∑ b, (Formalism.REAL.Amat (l ∘ Equiv.swap p q) ^ k) a b = ∑ a, ∑ b, (Formalism.REAL.Amat l ^ k) a b := by
  by_cases hd : l p - l q - 1 = 0
  · have hne : p ≠ q := by intro h; rw [h] at hpq; omega
    have hd' : (l ∘ Equiv.swap p q) p - (l ∘ Equiv.swap p q) q - 1 ≠ 0 := by
      simp only [Function.comp_apply, Equiv.swap_apply_left, Equiv.swap_apply_right]
      intro h; apply two_ne_zero (α := ℂ); linear_combination -h - hd
    have := tot_swap_of (l ∘ Equiv.swap p q) p q hpq hd' k
    have hinv : (l ∘ Equiv.swap p q) ∘ Equiv.swap p q = l := by
      funext a; simp [Equiv.swap_apply_self]
    rw [hinv] at this
    exact this.symm
  · exact tot_swap_of l p q hpq hd k

theorem tot_perm {n : ℕ} (s : Equiv.Perm (Fin n)) : ∀ (l : Fin n → ℂ) (k : ℕ),
    ∑ a, ∑ b, (Formalism.REAL.Amat (l ∘ s) ^ k) a b = ∑ a, ∑ b, (Formalism.REAL.Amat l ^ k) a b := by
  cases n with
  | zero =>
    have : s = 1 := Subsingleton.elim _ _
    subst this; intro l k; rfl
  | succ m =>
    have hs : s ∈ Submonoid.closure (Set.range fun i : Fin m => Equiv.swap i.castSucc i.succ) := by
      rw [Equiv.Perm.mclosure_swap_castSucc_succ m]; trivial
    induction hs using Submonoid.closure_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      intro l k
      exact tot_swap l i.castSucc i.succ (by simp) k
    | one => intro l k; rfl
    | mul x y _ _ hx hy =>
      intro l k
      have hc : l ∘ ⇑(x * y) = (l ∘ ⇑x) ∘ ⇑y := by ext c; simp
      rw [hc, hy (l ∘ ⇑x) k, hx l k]

theorem gelfVal_shift_symm : ∀ (n : ℕ) (χ : Fin n → ℂ), (∀ (t : ℂ) (k : ℕ), gelfVal (fun a => χ a + t) k = ∑ j ∈ range (k + 1), (k.choose j : ℂ) * t ^ (k - j) * gelfVal χ j) ∧ gelfVal χ 0 = n ∧ ∀ (s : Equiv.Perm (Fin n)) (k : ℕ), gelfVal (χ ∘ s) k = gelfVal χ k := by
  intro n χ
  refine ⟨?_, ?_, ?_⟩
  · intro t k
    unfold gelfVal
    have e : (fun c => χ c + t + ((n : ℂ) - 1) / 2) = fun c => (χ c + ((n : ℂ) - 1) / 2) + t := by
      funext c; ring
    set A := Formalism.REAL.Amat (fun c => χ c + ((n : ℂ) - 1) / 2)
    have hM : (A + t • (1 : Matrix (Fin n) (Fin n) ℂ)) ^ k =
        ∑ j ∈ range (k + 1), ((k.choose j : ℂ) * t ^ (k - j)) • A ^ j := by
      rw [(Commute.smul_right (Commute.one_right A) t).add_pow]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [smul_pow, one_pow, Matrix.mul_smul, mul_one, ← Nat.cast_comm, ← nsmul_eq_mul,
        ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
    rw [e, amat_add_const, hM]
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm (s := range (k + 1))]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    exact Finset.sum_comm
  · simp [gelfVal, Matrix.one_apply]
  · intro s k
    unfold gelfVal
    have e : (fun c => (χ ∘ s) c + ((n : ℂ) - 1) / 2) = (fun c => χ c + ((n : ℂ) - 1) / 2) ∘ s := rfl
    rw [e, tot_perm]

end GlobalTheory.GelfValSym
