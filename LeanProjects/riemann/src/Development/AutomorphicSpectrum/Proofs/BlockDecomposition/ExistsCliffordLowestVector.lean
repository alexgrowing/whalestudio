import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCliff

noncomputable section

open Matrix Finset
open scoped InnerProductSpace Kronecker

namespace GlobalTheory.CompanionTheory.CliffModel

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount

def IsCAR {M ι : Type} [DecidableEq M] [Fintype ι] [DecidableEq ι] (A : M → Matrix ι ι ℂ) : Prop :=
  (∀ p r, A p * A r + A r * A p = 0) ∧
    ∀ p r, A p * (A r)ᴴ + (A r)ᴴ * A p = if p = r then 1 else 0

def annM : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 0, 0]

def parM : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

def vacM : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 0]

theorem annM_sq : annM * annM = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [annM, Matrix.mul_apply, Fin.sum_univ_two]

theorem annM_conj : annMᴴ = !![0, 0; 1, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [annM, Matrix.conjTranspose_apply]

theorem annM_car : annM * annMᴴ + annMᴴ * annM = 1 := by
  rw [annM_conj]
  ext i j; fin_cases i <;> fin_cases j <;> simp [annM, Matrix.mul_apply, Fin.sum_univ_two]

theorem parM_sq : parM * parM = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [parM, Matrix.mul_apply, Fin.sum_univ_two]

theorem parM_herm : parMᴴ = parM := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [parM, Matrix.conjTranspose_apply]

theorem parM_annM : parM * annM + annM * parM = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [parM, annM, Matrix.mul_apply, Fin.sum_univ_two]

theorem annM_vacM : annM * vacM = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [annM, vacM, Matrix.mul_apply, Fin.sum_univ_two]

theorem vacM_ne : vacM ≠ 0 := by
  intro h
  have := congrFun (congrFun h 0) 0
  simp [vacM] at this

theorem exists_fock (m : ℕ) : ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι)
    (A : Fin m → Matrix ι ι ℂ) (G Q : Matrix ι ι ℂ),
    IsCAR A ∧ G * G = 1 ∧ Gᴴ = G ∧ (∀ p, G * A p + A p * G = 0) ∧ Q ≠ 0 ∧ ∀ p, A p * Q = 0 := by
  induction m with
  | zero =>
    refine ⟨Unit, inferInstance, inferInstance, fun p => p.elim0, 1, 1, ⟨fun p => p.elim0, fun p => p.elim0⟩,
      by simp, by simp, fun p => p.elim0, one_ne_zero, fun p => p.elim0⟩
  | succ m ih =>
    obtain ⟨ι, _, _, A, G, Q, ⟨h1, h2⟩, hG, hGh, hGA, hQ, hv⟩ := ih
    have hGAh : ∀ i, G * (A i)ᴴ + (A i)ᴴ * G = 0 := by
      intro i
      have := congrArg conjTranspose (hGA i)
      simpa [conjTranspose_add, conjTranspose_mul, hGh, add_comm] using this
    refine ⟨ι × Fin 2, inferInstance, inferInstance,
      Fin.cases (G ⊗ₖ annM) (fun i => A i ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)),
      G ⊗ₖ parM, Q ⊗ₖ vacM, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
    · intro p r
      induction p using Fin.cases with
      | zero =>
        induction r using Fin.cases with
        | zero =>
          simp only [Fin.cases_zero, ← mul_kronecker_mul, annM_sq, kronecker_zero, add_zero]
        | succ r =>
          simp only [Fin.cases_zero, Fin.cases_succ, ← mul_kronecker_mul, mul_one, one_mul,
            ← add_kronecker, hGA, zero_kronecker]
      | succ p =>
        induction r using Fin.cases with
        | zero =>
          simp only [Fin.cases_zero, Fin.cases_succ, ← mul_kronecker_mul, mul_one, one_mul,
            ← add_kronecker]
          rw [add_comm, hGA, zero_kronecker]
        | succ r =>
          simp only [Fin.cases_succ, ← mul_kronecker_mul, mul_one, ← add_kronecker, h1,
            zero_kronecker]
    · intro p r
      induction p using Fin.cases with
      | zero =>
        induction r using Fin.cases with
        | zero =>
          simp only [Fin.cases_zero, conjTranspose_kronecker, hGh, ← mul_kronecker_mul, hG,
            ← kronecker_add, annM_car, if_true, one_kronecker_one]
        | succ r =>
          have hne : (0 : Fin (m + 1)) ≠ r.succ := (Fin.succ_ne_zero r).symm
          simp only [Fin.cases_zero, Fin.cases_succ, conjTranspose_kronecker, conjTranspose_one,
            ← mul_kronecker_mul, mul_one, one_mul, ← add_kronecker, hGAh, zero_kronecker, if_neg hne]
      | succ p =>
        induction r using Fin.cases with
        | zero =>
          have hne : p.succ ≠ (0 : Fin (m + 1)) := Fin.succ_ne_zero p
          simp only [Fin.cases_zero, Fin.cases_succ, conjTranspose_kronecker, hGh,
            ← mul_kronecker_mul, mul_one, one_mul, ← add_kronecker, if_neg hne]
          rw [add_comm, hGA, zero_kronecker]
        | succ r =>
          simp only [Fin.cases_succ, conjTranspose_kronecker, conjTranspose_one,
            ← mul_kronecker_mul, mul_one, ← add_kronecker, h2, Fin.succ_inj]
          split_ifs <;> simp
    · rw [← mul_kronecker_mul, hG, parM_sq, one_kronecker_one]
    · rw [conjTranspose_kronecker, hGh, parM_herm]
    · intro p
      induction p using Fin.cases with
      | zero =>
        simp only [Fin.cases_zero, ← mul_kronecker_mul, hG, ← kronecker_add, parM_annM, kronecker_zero]
      | succ p =>
        simp only [Fin.cases_succ, ← mul_kronecker_mul, mul_one, one_mul, ← add_kronecker, hGA,
          zero_kronecker]
    · intro h
      apply hQ
      ext i j
      have := congrFun (congrFun h (i, 0)) (j, 0)
      simpa [vacM, kroneckerMap_apply] using this
    · intro p
      induction p using Fin.cases with
      | zero => simp only [Fin.cases_zero, ← mul_kronecker_mul, annM_vacM, kronecker_zero]
      | succ p => simp only [Fin.cases_succ, ← mul_kronecker_mul, hv, zero_kronecker]

theorem car_lin {M ι : Type} [DecidableEq M] [Fintype ι] [DecidableEq ι] {A : M → Matrix ι ι ℂ}
    (hA : IsCAR A) (x y u v : ℂ) (p r : M) :
    (x • A p + y • (A p)ᴴ) * (u • A r + v • (A r)ᴴ) + (u • A r + v • (A r)ᴴ) * (x • A p + y • (A p)ᴴ) =
      (if p = r then x * v + y * u else 0) • (1 : Matrix ι ι ℂ) := by
  obtain ⟨h1, h2⟩ := hA
  have h3 : (A p)ᴴ * (A r)ᴴ + (A r)ᴴ * (A p)ᴴ = 0 := by
    have := congrArg conjTranspose (h1 p r)
    simpa [conjTranspose_add, conjTranspose_mul, add_comm] using this
  have key : (x • A p + y • (A p)ᴴ) * (u • A r + v • (A r)ᴴ) + (u • A r + v • (A r)ᴴ) * (x • A p + y • (A p)ᴴ) =
      (x * u) • (A p * A r + A r * A p) + (x * v) • (A p * (A r)ᴴ + (A r)ᴴ * A p) +
        (y * u) • (A r * (A p)ᴴ + (A p)ᴴ * A r) + (y * v) • ((A p)ᴴ * (A r)ᴴ + (A r)ᴴ * (A p)ᴴ) := by
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_add, smul_smul]
    module
  rw [key, h1, h2, h2, h3]
  by_cases h : p = r
  · subst h
    simp [add_smul]
  · simp [h, Ne.symm h]

def coefA {n : ℕ} (s : ℂ) (a b : Fin n) : ℂ := if a < b then 0 else if b < a then s else 1

def coefC {n : ℕ} (s : ℂ) (a b : Fin n) : ℂ := if a < b then s else if b < a then 0 else 1

def modeOf {n : ℕ} (a b : Fin n) : Fin n × Fin n := (min a b, max a b)

theorem modeOf_comm {n : ℕ} (a b : Fin n) : modeOf a b = modeOf b a := by
  simp [modeOf, min_comm, max_comm]

theorem modeOf_lt {n : ℕ} {a b : Fin n} (h : a < b) : modeOf a b = (a, b) := by
  simp [modeOf, min_eq_left h.le, max_eq_right h.le]

theorem modeOf_gt {n : ℕ} {a b : Fin n} (h : b < a) : modeOf a b = (b, a) := by
  simp [modeOf, min_eq_right h.le, max_eq_left h.le]

theorem modeOf_self {n : ℕ} (a : Fin n) : modeOf a a = (a, a) := by
  simp [modeOf]

theorem coef_rel {n : ℕ} {s : ℂ} (hs : s * s = 2) (a b d e : Fin n) :
    (if modeOf a b = modeOf d e then coefA s a b * coefC s d e + coefC s a b * coefA s d e else 0) =
      if a = e ∧ b = d then 2 else 0 := by
  rcases lt_trichotomy a b with hab | rfl | hab <;> rcases lt_trichotomy d e with hde | rfl | hde
  · have : ¬ (a = e ∧ b = d) := by rintro ⟨rfl, rfl⟩; exact lt_asymm hab hde
    simp [coefA, coefC, hab, hde, lt_asymm hab, lt_asymm hde, this]
  · have h1 : ¬ (a = d ∧ b = d) := by rintro ⟨rfl, rfl⟩; exact lt_irrefl _ hab
    simp [modeOf_lt hab, modeOf_self, h1]
  · simp only [modeOf_lt hab, modeOf_gt hde, Prod.mk.injEq, coefA, coefC, hab, hde, lt_asymm hab,
      lt_asymm hde, if_true, if_false]
    simp [hs]
  · have h1 : ¬ (a = e ∧ a = d) := by rintro ⟨rfl, rfl⟩; exact lt_irrefl _ hde
    have h2 : ¬ (a = d ∧ a = e) := fun h => h1 ⟨h.2, h.1⟩
    simp [modeOf_lt hde, modeOf_self, h1, h2]
  · simp only [modeOf_self, Prod.mk.injEq, coefA, coefC, lt_irrefl, if_false, and_self]
    split_ifs <;> norm_num
  · have h1 : ¬ (a = e ∧ a = d) := by rintro ⟨rfl, rfl⟩; exact lt_irrefl _ hde
    have h3 : ¬ (a = d ∧ a = e) := fun h => h1 ⟨h.2, h.1⟩
    simp [modeOf_gt hde, modeOf_self, h1, h3]
  · simp only [modeOf_gt hab, modeOf_lt hde, Prod.mk.injEq, coefA, coefC, hab, hde, lt_asymm hab,
      lt_asymm hde, if_true, if_false]
    by_cases h : b = d ∧ a = e
    · simp [h, hs]
    · have h' : ¬ (a = e ∧ b = d) := fun g => h ⟨g.2, g.1⟩
      simp [h, h']
  · have h1 : ¬ (a = d ∧ b = d) := by rintro ⟨rfl, rfl⟩; exact lt_irrefl _ hab
    have h2 : ¬ (b = d ∧ a = d) := fun h => h1 ⟨h.2, h.1⟩
    simp [modeOf_gt hab, modeOf_self, h1, h2]
  · have : ¬ (a = e ∧ b = d) := by rintro ⟨rfl, rfl⟩; exact lt_asymm hab hde
    simp [coefA, coefC, hab, hde, lt_asymm hab, lt_asymm hde, this]

theorem star_coefC {n : ℕ} {s : ℂ} (hs : star s = s) (a b : Fin n) :
    star (coefC s a b) = coefA s b a := by
  rcases lt_trichotomy a b with h | rfl | h
  · simp [coefA, coefC, h, lt_asymm h, hs]
  · simp [coefA, coefC]
  · simp [coefA, coefC, h, lt_asymm h]

theorem star_coefA {n : ℕ} {s : ℂ} (hs : star s = s) (a b : Fin n) :
    star (coefA s a b) = coefC s b a := by
  rcases lt_trichotomy a b with h | rfl | h
  · simp [coefA, coefC, h, lt_asymm h]
  · simp [coefA, coefC]
  · simp [coefA, coefC, h, lt_asymm h, hs]

theorem exists_cliff_model : ∀ n : ℕ, ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι)
    (c : Fin n → Fin n → Matrix ι ι ℂ),
    IsCliff c ∧ ∃ q : ι → ℂ, q ≠ 0 ∧ ∀ a b, a < b → c b a *ᵥ q = 0 := by
  intro n
  obtain ⟨ι, _, _, A0, G, Q, ⟨h1, h2⟩, -, -, -, hQ, hv⟩ :=
    exists_fock (Fintype.card (Fin n × Fin n))
  let e := Fintype.equivFin (Fin n × Fin n)
  let A : Fin n × Fin n → Matrix ι ι ℂ := fun p => A0 (e p)
  have hA : IsCAR A := ⟨fun p r => h1 _ _, fun p r => by simp [A, h2, e.injective.eq_iff]⟩
  let s : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)
  have hs : s * s = 2 := by
    simp only [s, ← Complex.ofReal_mul]
    rw [Real.mul_self_sqrt (by norm_num)]
    norm_num
  have hs' : star s = s := Complex.conj_ofReal _
  refine ⟨ι, inferInstance, inferInstance,
    fun a b => coefA s a b • A (modeOf a b) + coefC s a b • (A (modeOf a b))ᴴ, ⟨?_, ?_⟩, ?_⟩
  · intro a b d e'
    rw [car_lin hA, coef_rel hs]
    split_ifs
    · simp [two_smul, one_add_one_eq_two]
    · simp
  · intro a b
    simp only [conjTranspose_add, conjTranspose_smul, conjTranspose_conjTranspose, star_coefA hs',
      star_coefC hs', modeOf_comm a b]
    rw [add_comm]
  · obtain ⟨i, j, hij⟩ : ∃ i j, Q i j ≠ 0 := by
      by_contra h
      push_neg at h
      exact hQ (by ext i j; exact h i j)
    refine ⟨fun i => Q i j, fun h => hij (congrFun h i), ?_⟩
    intro a b hab
    have hcol : ∀ M : Matrix ι ι ℂ, M * Q = 0 → M *ᵥ (fun i => Q i j) = 0 := by
      intro M hM
      funext k
      have := congrFun (congrFun hM k) j
      simpa [Matrix.mul_apply, mulVec, dotProduct] using this
    apply hcol
    simp only [coefA, coefC, hab, lt_asymm hab, if_true, if_false, zero_smul, add_zero,
      smul_mul_assoc]
    simp [A, hv]

end GlobalTheory.CompanionTheory.CliffModel
