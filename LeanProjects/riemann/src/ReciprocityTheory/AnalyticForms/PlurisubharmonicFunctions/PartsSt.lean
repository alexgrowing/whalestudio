import Mathlib
import ReciprocityTheory.AnalyticForms.MaIntEmpty

namespace ReciprocityTheory.AnForm.A

open MeasureTheory ReciprocityTheory.AnForm

noncomputable section

section Partials

variable {D : ℕ}

def dz (j : Fin D) (f : (Fin D → ℂ) → ℂ) (z : Fin D → ℂ) : ℂ :=
  (fderiv ℝ f z (Pi.single j 1) - Complex.I * fderiv ℝ f z (Complex.I • Pi.single j 1)) / 2

def dzb (j : Fin D) (f : (Fin D → ℂ) → ℂ) (z : Fin D → ℂ) : ℂ :=
  (fderiv ℝ f z (Pi.single j 1) + Complex.I * fderiv ℝ f z (Complex.I • Pi.single j 1)) / 2

def cplx (v : (Fin D → ℂ) → ℝ) : (Fin D → ℂ) → ℂ := fun z => (v z : ℂ)

def gradMat (v w : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) : Matrix (Fin D) (Fin D) ℂ :=
  fun j k => dz j (cplx v) z * dzb k (cplx w) z

end Partials

section Densities

variable {n : ℕ}

def gradDens (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ) (v w : (Fin (n + 1) → ℂ) → ℝ)
    (z : Fin (n + 1) → ℂ) : ℝ :=
  ((n + 1).factorial : ℝ) * (2 / Real.pi) ^ (n + 1) *
    (mdisc (Fin.cons (gradMat v w z) fun i => hessC (φ i) z)).re

def gradInt (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ) (v w : (Fin (n + 1) → ℂ) → ℝ)
    (U : Set (Fin (n + 1) → ℂ)) : ℝ :=
  ∫ z in U, gradDens φ v w z

def mixedCof (B : Fin n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  fun j k => mdisc (Fin.cons (Matrix.single j k 1) B)

def hessCof (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ) (z : Fin (n + 1) → ℂ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  mixedCof fun i => hessC (φ i) z

end Densities

section MdiscLinear

theorem det_finsetSum_eq_sum_fun {D : ℕ} (A : Fin D → Matrix (Fin D) (Fin D) ℂ)
    (S : Finset (Fin D)) :
    (∑ k ∈ S, A k).det = ∑ r : Fin D → Fin D,
      if (∀ i, r i ∈ S) then (Matrix.of fun i => A (r i) i).det else 0 := by
  classical
  have h1 : (∑ k ∈ S, A k) = fun i => ∑ k ∈ S, A k i := by
    ext i j; simp [Matrix.sum_apply]
  have h2 := (Matrix.detRowAlternating : (Fin D → ℂ) [⋀^Fin D]→ₗ[ℂ] ℂ).toMultilinearMap.map_sum_finset
    (fun i k => A k i) (fun _ => S)
  rw [h1]
  refine h2.trans ?_
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext r; simp [Fintype.mem_piFinset]
  · intro r _; rfl

def polCoef {D : ℕ} (r : Fin D → Fin D) : ℂ :=
  ∑ S : Finset (Fin D), (-1 : ℂ) ^ (D - S.card) * if (∀ i, r i ∈ S) then 1 else 0

theorem mdisc_eq_sum_polCoef {D : ℕ} (A : Fin D → Matrix (Fin D) (Fin D) ℂ) :
    mdisc A = (1 / (D.factorial : ℂ)) *
      ∑ r : Fin D → Fin D, polCoef r * (Matrix.of fun i => A (r i) i).det := by
  classical
  unfold mdisc polCoef
  congr 1
  simp_rw [det_finsetSum_eq_sum_fun, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun S _ => ?_
  split_ifs <;> ring

theorem polCoef_eq_zero {D : ℕ} (r : Fin D → Fin D) (h : ¬ Function.Surjective r) :
    polCoef r = 0 := by
  classical
  obtain ⟨a, ha⟩ : ∃ a, ∀ i, r i ≠ a := by
    simp only [Function.Surjective, not_forall, not_exists] at h
    obtain ⟨a, ha⟩ := h
    exact ⟨a, fun i hi => ha i hi⟩
  let t : Finset (Fin D) → Finset (Fin D) := fun S => if a ∈ S then S.erase a else insert a S
  have ht : Function.Involutive t := by
    intro S; by_cases hS : a ∈ S <;> simp [t, hS]
  let f : Finset (Fin D) → ℂ := fun S =>
    (-1 : ℂ) ^ (D - S.card) * if (∀ i, r i ∈ S) then 1 else 0
  have hmem : ∀ S, (∀ i, r i ∈ t S) ↔ ∀ i, r i ∈ S := by
    intro S
    by_cases hS : a ∈ S <;> simp [t, hS, ha]
  have key : ∀ S, f (t S) = - f S := by
    intro S
    simp only [f, hmem]
    by_cases hS : a ∈ S
    · have h1 : 1 ≤ S.card := Finset.card_pos.mpr ⟨a, hS⟩
      have h2 : S.card ≤ D := by simpa using Finset.card_le_univ S
      have hc : (t S).card = S.card - 1 := by simp [t, hS, Finset.card_erase_of_mem]
      rw [hc, show D - (S.card - 1) = (D - S.card) + 1 by omega, pow_succ]
      ring
    · have h2 : (t S).card ≤ D := by simpa using Finset.card_le_univ (t S)
      have hc : (t S).card = S.card + 1 := by simp [t, hS]
      rw [hc] at h2
      rw [hc]
      rw [show D - S.card = (D - (S.card + 1)) + 1 by omega, pow_succ]
      ring
  have hsum : ∑ S, f S = ∑ S, f (ht.toPerm t S) := (Equiv.sum_comp (ht.toPerm t) f).symm
  simp only [Function.Involutive.coe_toPerm, key, Finset.sum_neg_distrib] at hsum
  have : ∑ S, f S = 0 := by linear_combination hsum / 2
  exact this

theorem mdisc_cons_eq_sum' {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (B : Fin n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    mdisc (Fin.cons A B) = ∑ j, ∑ k, A j k *
      mdisc (Fin.cons (Matrix.single j k 1) B : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) := by
  classical
  have key : ∀ r : Fin (n + 1) → Fin (n + 1),
      polCoef r * (Matrix.of fun i =>
        (Fin.cons A B : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (r i) i).det =
      ∑ j, ∑ k, A j k * (polCoef r * (Matrix.of fun i =>
        (Fin.cons (Matrix.single j k 1) B : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
          (r i) i).det) := by
    intro r
    by_cases hs : Function.Surjective r
    · have hinj := Finite.injective_iff_surjective.mpr hs
      obtain ⟨i0, hi0⟩ := hs 0
      let M : Fin (n + 1) → Fin (n + 1) → ℂ := fun i =>
        (Fin.cons A B : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (r i) i
      have hg : ∀ X : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
          (Matrix.of fun i =>
            (Fin.cons X B : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (r i) i) =
          Function.update M i0 (X i0) := by
        intro X
        funext i
        by_cases hi : i = i0
        · subst hi
          show (Fin.cons X B : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (r i) i = _
          simp [hi0]
        · have hr : r i ≠ 0 := fun h => hi (hinj (h.trans hi0.symm))
          obtain ⟨m, hm⟩ := Fin.exists_succ_eq.mpr hr
          show (Fin.cons X B : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (r i) i = _
          simp [M, hi, ← hm]
      let Lm := (Matrix.detRowAlternating :
        (Fin (n + 1) → ℂ) [⋀^Fin (n + 1)]→ₗ[ℂ] ℂ).toMultilinearMap.toLinearMap M i0
      have hL : ∀ X : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
          (Matrix.of fun i =>
            (Fin.cons X B : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (r i) i).det =
          Lm (X i0) := by
        intro X
        rw [hg]
        rfl
      have hA : A i0 = ∑ j, ∑ k, A j k • (Matrix.single j k (1 : ℂ)) i0 := by
        ext c
        simp only [Finset.sum_apply, Pi.smul_apply, Matrix.single_apply, smul_eq_mul]
        rw [Finset.sum_eq_single i0 (by intro b _ hb; simp [hb]) (by simp),
          Finset.sum_eq_single c (by intro b _ hb; simp [hb]) (by simp)]
        simp
      simp_rw [hL]
      rw [hA, map_sum]
      simp_rw [map_sum, map_smul, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
    · simp [polCoef_eq_zero r hs]
  rw [mdisc_eq_sum_polCoef]
  simp_rw [mdisc_eq_sum_polCoef, key, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun r _ => by ring

theorem sum_finset_fin_succ {β : Type*} [AddCommMonoid β] {n : ℕ} (g : Finset (Fin (n + 1)) → β) :
    ∑ S, g S = ∑ S : Finset (Fin n),
      (g (S.map (Fin.succEmb n)) + g (insert 0 (S.map (Fin.succEmb n)))) := by
  classical
  have hu : (Finset.univ : Finset (Fin (n + 1))) =
      insert 0 (Finset.univ.map (Fin.succEmb n)) := by
    ext x; cases x using Fin.cases <;> simp
  have h0 : (0 : Fin (n + 1)) ∉ Finset.univ.map (Fin.succEmb n) := by
    simp [Fin.succ_ne_zero]
  have hp : (Finset.univ.map (Fin.succEmb n)).powerset =
      (Finset.univ : Finset (Finset (Fin n))).map (Finset.mapEmbedding (Fin.succEmb n)).toEmbedding := by
    ext t; simp [Finset.subset_map_iff, eq_comm]
  rw [← Finset.powerset_univ, hu, Finset.sum_powerset_insert h0, hp,
    Finset.sum_map, Finset.sum_map, ← Finset.sum_add_distrib]
  rfl

theorem det_single_add {n : ℕ} (j : Fin (n + 1)) (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    (Matrix.single j j 1 + M).det = M.det + (M.submatrix j.succAbove j.succAbove).det := by
  classical
  have h1 : Matrix.single j j 1 + M = M.updateRow j (Pi.single j 1 + M j) := by
    ext a b
    by_cases ha : a = j
    · subst ha
      by_cases hb : b = a
      · simp [hb]
      · simp [hb, Ne.symm hb]
    · simp [ha, Ne.symm ha]
  rw [h1, Matrix.det_updateRow_add, Matrix.updateRow_eq_self, add_comm]
  congr 1
  rw [Matrix.det_succ_row _ j, Finset.sum_eq_single j]
  · have hs : ((M.updateRow j (Pi.single j 1)).submatrix j.succAbove j.succAbove) =
        M.submatrix j.succAbove j.succAbove := by
      ext a b; simp
    rw [hs]
    simp [Even.neg_one_pow ⟨(j : ℕ), rfl⟩]
  · intro k _ hk; simp [hk]
  · simp

theorem submatrix_finsetSum {ι : Type*} {n m : ℕ} (f : Fin m → Fin n)
    (B : ι → Matrix (Fin n) (Fin n) ℂ) (S : Finset ι) :
    (∑ k ∈ S, B k).submatrix f f = ∑ k ∈ S, (B k).submatrix f f := by
  ext a b; simp [Matrix.sum_apply]

theorem mixedCof_diag' {n : ℕ} (B : Fin n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (j : Fin (n + 1)) :
    mdisc (Fin.cons (Matrix.single j j 1) B : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) =
      (1 / ((n + 1 : ℕ) : ℂ)) * mdisc (fun i => (B i).submatrix j.succAbove j.succAbove) := by
  classical
  set X : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := Fin.cons (Matrix.single j j 1) B
    with hX
  have hX0 : X 0 = Matrix.single j j 1 := by simp [X]
  have hXs : ∀ k : Fin n, X k.succ = B k := fun k => by simp [X]
  have core : ∑ S : Finset (Fin (n + 1)), (-1 : ℂ) ^ (n + 1 - S.card) * (∑ k ∈ S, X k).det =
      ∑ S : Finset (Fin n), (-1 : ℂ) ^ (n - S.card) *
        (∑ k ∈ S, (B k).submatrix j.succAbove j.succAbove).det := by
    rw [sum_finset_fin_succ]
    refine Finset.sum_congr rfl fun S _ => ?_
    have h0 : (0 : Fin (n + 1)) ∉ S.map (Fin.succEmb n) := by simp [Fin.succ_ne_zero]
    have hsum : ∑ k ∈ S.map (Fin.succEmb n), X k = ∑ k ∈ S, B k := by
      rw [Finset.sum_map]; exact Finset.sum_congr rfl fun k _ => hXs k
    have hS : S.card ≤ n := by simpa using Finset.card_le_univ S
    have hc : (insert 0 (S.map (Fin.succEmb n))).card = S.card + 1 := by
      rw [Finset.card_insert_of_notMem h0, Finset.card_map]
    rw [Finset.sum_insert h0, hsum, hc, Finset.card_map, hX0, det_single_add,
      submatrix_finsetSum, show n + 1 - S.card = (n - S.card) + 1 by omega,
      show n + 1 - (S.card + 1) = n - S.card by omega, pow_succ]
    ring
  unfold mdisc
  rw [core, Nat.factorial_succ]
  push_cast
  field_simp

end MdiscLinear

section Statements

variable {n : ℕ}

theorem mdisc_cons_eq_sum (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (B : Fin n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    mdisc (Fin.cons A B) = ∑ j, ∑ k, A j k * mixedCof B j k := by
  exact mdisc_cons_eq_sum' A B

def IntegralDzStatement : Prop :=
  ∀ (D : ℕ) (j : Fin D) (g : (Fin D → ℂ) → ℂ), ContDiff ℝ 1 g → HasCompactSupport g →
    (∫ z, dz j g z) = 0 ∧ (∫ z, dzb j g z) = 0

def PiolaStatement : Prop :=
  ∀ (n : ℕ) (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ) (U : Set (Fin (n + 1) → ℂ)),
    IsOpen U → (∀ i, ContDiffOn ℝ 3 (φ i) U) → ∀ z ∈ U,
      (∀ k, ∑ j, dz j (fun y => hessCof φ y j k) z = 0) ∧
      (∀ j, ∑ k, dzb k (fun y => hessCof φ y j k) z = 0)

def PartsHyp (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ) (v w : (Fin (n + 1) → ℂ) → ℝ)
    (U : Set (Fin (n + 1) → ℂ)) : Prop :=
  IsOpen U ∧ ContDiffOn ℝ 3 v U ∧ HasCompactSupport v ∧ tsupport v ⊆ U ∧
    ContDiffOn ℝ 3 w U ∧ ∀ i, ContDiffOn ℝ 3 (φ i) U

def PartsStatement : Prop :=
  ∀ (n : ℕ) (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ) (v w : (Fin (n + 1) → ℂ) → ℝ)
    (U : Set (Fin (n + 1) → ℂ)), PartsHyp φ v w U →
      IntegrableOn (fun z => v z * maDens (Fin.cons w φ) z) U ∧
      IntegrableOn (fun z => w z * maDens (Fin.cons v φ) z) U ∧
      IntegrableOn (gradDens φ v w) U ∧
      maInt (Fin.cons w φ) v U = - gradInt φ v w U ∧
      maInt (Fin.cons v φ) w U = maInt (Fin.cons w φ) v U

def MassZeroStatement : Prop :=
  ∀ (n : ℕ) (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ) (v : (Fin (n + 1) → ℂ) → ℝ)
    (U : Set (Fin (n + 1) → ℂ)), PartsHyp φ v (fun _ => 1) U →
      (∫ z in U, maDens (Fin.cons v φ) z) = 0

def GradDensSymmStatement : Prop :=
  ∀ (n : ℕ) (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ) (v w : (Fin (n + 1) → ℂ) → ℝ)
    (U : Set (Fin (n + 1) → ℂ)), IsOpen U → (∀ i, ContDiffOn ℝ 2 (φ i) U) →
      ∀ z ∈ U, gradDens φ v w z = gradDens φ w v z

def GradDensNonnegStatement : Prop :=
  ∀ (n : ℕ) (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ) (v : (Fin (n + 1) → ℂ) → ℝ)
    (U : Set (Fin (n + 1) → ℂ)), IsOpen U → (∀ i, ContDiffOn ℝ 2 (φ i) U) →
      (∀ i, ∀ z ∈ U, ∀ ξ, 0 ≤ levi (φ i) z ξ) →
      ∀ z ∈ U, 0 ≤ gradDens φ v v z

def HessCDzStatement : Prop :=
  ∀ (D : ℕ) (v : (Fin D → ℂ) → ℝ) (U : Set (Fin D → ℂ)), IsOpen U → ContDiffOn ℝ 2 v U →
    ∀ z ∈ U, ∀ j k, hessC v z j k = dz j (dzb k (cplx v)) z

def DoubleDivStatement : Prop :=
  ∀ (n : ℕ) (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ) (v : (Fin (n + 1) → ℂ) → ℝ)
    (U : Set (Fin (n + 1) → ℂ)), IsOpen U → ContDiffOn ℝ 2 v U →
      (∀ i, ContDiffOn ℝ 4 (φ i) U) → ∀ z ∈ U,
        ∑ j, ∑ k, dz j (dzb k (fun y => cplx v y * hessCof φ y j k)) z =
          ∑ j, ∑ k, hessCof φ z j k * dz j (dzb k (cplx v)) z

def GradDensCauchySchwarzStatement : Prop :=
  ∀ (n : ℕ) (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ) (v w : (Fin (n + 1) → ℂ) → ℝ)
    (U : Set (Fin (n + 1) → ℂ)), IsOpen U → (∀ i, ContDiffOn ℝ 2 (φ i) U) →
      (∀ i, ∀ z ∈ U, ∀ ξ, 0 ≤ levi (φ i) z ξ) →
      ∀ z ∈ U, gradDens φ v w z ^ 2 ≤ gradDens φ v v z * gradDens φ w w z

def MaDensCofStatement : Prop :=
  ∀ (n : ℕ) (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ) (v : (Fin (n + 1) → ℂ) → ℝ)
    (U : Set (Fin (n + 1) → ℂ)), IsOpen U → ContDiffOn ℝ 2 v U → ∀ z ∈ U,
      maDens (Fin.cons v φ) z = ((n + 1).factorial : ℝ) * (2 / Real.pi) ^ (n + 1) *
        (∑ j, ∑ k, hessCof φ z j k * dz j (dzb k (cplx v)) z).re

theorem mixedCof_diag (B : Fin n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (j : Fin (n + 1)) :
    mixedCof B j j = (1 / ((n + 1 : ℕ) : ℂ)) *
      mdisc (fun i => (B i).submatrix j.succAbove j.succAbove) := by
  exact mixedCof_diag' B j

def HessCRestrictStatement : Prop :=
  ∀ (n : ℕ) (φ : (Fin (n + 1) → ℂ) → ℝ) (U : Set (Fin (n + 1) → ℂ)) (j : Fin (n + 1)),
    IsOpen U → ContDiffOn ℝ 2 φ U → ∀ y : Fin n → ℂ,
      (Fin.insertNth (α := fun _ => ℂ) j 0 y) ∈ U →
        hessC (fun y' => φ (Fin.insertNth (α := fun _ => ℂ) j 0 y')) y =
          (hessC φ (Fin.insertNth (α := fun _ => ℂ) j 0 y)).submatrix j.succAbove j.succAbove

def GradDensLeibnizStatement : Prop :=
  ∀ (n : ℕ) (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ) (f g w : (Fin (n + 1) → ℂ) → ℝ)
    (z : Fin (n + 1) → ℂ), DifferentiableAt ℝ f z → DifferentiableAt ℝ g z →
      gradDens φ (fun y => f y * g y) w z = f z * gradDens φ g w z + g z * gradDens φ f w z ∧
      gradDens φ g (fun y => g y ^ 2 / 2) z = g z * gradDens φ g g z

def PartsHypInhabitStatement : Prop :=
  ∀ (n : ℕ) (U : Set (Fin (n + 1) → ℂ)), IsOpen U → ∀ z ∈ U,
    ∀ φ : Fin n → (Fin (n + 1) → ℂ) → ℝ, (∀ i, ContDiffOn ℝ 3 (φ i) U) →
      ∃ v : (Fin (n + 1) → ℂ) → ℝ, PartsHyp φ v v U ∧ v z = 1

def PartsInhabitStatement : Prop :=
  ∃ v : (Fin 1 → ℂ) → ℝ,
    PartsHyp (n := 0) Fin.elim0 v v Set.univ ∧ 0 < gradInt (n := 0) Fin.elim0 v v Set.univ

end Statements

end

end ReciprocityTheory.AnForm.A
