import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.NormsAndPolarizations.CjApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.NormsAndPolarizations.SmithGen
open IsLocalRing Matrix NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th UpperTheory.V.Th.Nm GlobalTheory.GalOfCusp

private theorem intM_mul' {l : ℕ} [Fact l.Prime] {n : ℕ} {A B : Matrix (Fin n) (Fin n) (Qbar l)}
    (hA : IntM A) (hB : IntM B) : IntM (A * B) := by
  intro i j
  rw [Matrix.mul_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun k _ => ?_
  rw [norm_mul]
  exact mul_le_one₀ (hA i k) (norm_nonneg _) (hB k j)

private theorem intM_transpose' {l : ℕ} [Fact l.Prime] {n : ℕ} {A : Matrix (Fin n) (Fin n) (Qbar l)}
    (hA : IntM A) : IntM Aᵀ := fun i j => hA j i

private theorem le_one_of_mul_self {x : ℝ} (h : x * x ≤ 1) : x ≤ 1 := by nlinarith

private theorem intM_of_symm {l : ℕ} [Fact l.Prime] {n : ℕ} {A : Matrix (Fin n) (Fin n) (Qbar l)}
    (e : Fin n → Qbar l) (he : ∀ i, e i ≠ 0) (hA : IntM A)
    (hs : (diagonal (fun i => (e i)⁻¹) * A * diagonal e)ᵀ = diagonal (fun i => (e i)⁻¹) * A * diagonal e ∨
      (diagonal (fun i => (e i)⁻¹) * A * diagonal e)ᵀ = -(diagonal (fun i => (e i)⁻¹) * A * diagonal e)) :
    IntM (diagonal (fun i => (e i)⁻¹) * A * diagonal e) := by
  intro i j
  set M := diagonal (fun i => (e i)⁻¹) * A * diagonal e with hM
  have hent : ∀ a b, M a b = (e a)⁻¹ * A a b * e b := by
    intro a b
    rw [hM, Matrix.mul_diagonal, Matrix.diagonal_mul]
  have hn : ‖M j i‖ = ‖M i j‖ := by
    rcases hs with h | h
    · have := congrFun (congrFun h i) j
      rw [Matrix.transpose_apply] at this
      rw [this]
    · have := congrFun (congrFun h i) j
      rw [Matrix.transpose_apply, Matrix.neg_apply] at this
      rw [this, norm_neg]
  have hp : M i j * M j i = A i j * A j i := by
    rw [hent, hent]
    have := he i
    have := he j
    field_simp
  apply le_one_of_mul_self
  calc ‖M i j‖ * ‖M i j‖ = ‖M i j * M j i‖ := by rw [norm_mul, hn]
    _ = ‖A i j‖ * ‖A j i‖ := by rw [hp, norm_mul]
    _ ≤ 1 := mul_le_one₀ (hA i j) (norm_nonneg _) (hA j i)

private theorem intM_mid {l : ℕ} [Fact l.Prime] {n : ℕ} {A : Matrix (Fin n) (Fin n) (Qbar l)}
    (e : Fin n → Qbar l) (he : ∀ i, e i ≠ 0) (hA : IntM A)
    (hB : IntM (diagonal e * diagonal e * A * diagonal (fun i => (e i)⁻¹) * diagonal (fun i => (e i)⁻¹))) :
    IntM (diagonal e * A * diagonal (fun i => (e i)⁻¹)) := by
  intro i j
  have h1 := hB i j
  rw [Matrix.mul_assoc (diagonal e) (diagonal e), Matrix.mul_diagonal, Matrix.mul_diagonal,
    Matrix.diagonal_mul, Matrix.diagonal_mul] at h1
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  apply le_one_of_mul_self
  have hp : (e i * A i j * (e j)⁻¹) * (e i * A i j * (e j)⁻¹)
      = (e i * (e i * A i j) * (e j)⁻¹ * (e j)⁻¹) * A i j := by ring
  rw [← norm_mul, hp, norm_mul]
  exact mul_le_one₀ h1 (norm_nonneg _) (hA i j)

private theorem inv_symm {K : Type} [CommRing K] {n : ℕ} (M : GL (Fin n) K)
    (h : (M : Matrix (Fin n) (Fin n) K)ᵀ = M ∨ (M : Matrix (Fin n) (Fin n) K)ᵀ = -M) :
    ((M⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ = (M⁻¹ : GL (Fin n) K) ∨
      ((M⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ = -((M⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  have h1 : (M : Matrix (Fin n) (Fin n) K) * (M⁻¹ : GL (Fin n) K) = 1 := M.mul_inv
  generalize ((M⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = N at h1 ⊢
  generalize (M : Matrix (Fin n) (Fin n) K) = A at h h1
  have h2 : Nᵀ * Aᵀ = 1 := by rw [← Matrix.transpose_mul, h1, Matrix.transpose_one]
  rcases h with h | h
  · left
    rw [h] at h2
    calc Nᵀ = Nᵀ * (A * N) := by rw [h1, Matrix.mul_one]
      _ = N := by rw [← Matrix.mul_assoc, h2, Matrix.one_mul]
  · right
    rw [h, Matrix.mul_neg, neg_eq_iff_eq_neg] at h2
    calc Nᵀ = Nᵀ * (A * N) := by rw [h1, Matrix.mul_one]
      _ = -N := by rw [← Matrix.mul_assoc, h2, Matrix.neg_mul, Matrix.one_mul]

theorem UpperTheory.V.Th.Nm.midpoint :
    ∀ {l : ℕ} [Fact l.Prime] {n : ℕ} (S : Set (GL (Fin n) (Qbar l))) (P : GL (Fin n) (Qbar l)), ((P : Matrix (Fin n) (Fin n) (Qbar l))ᵀ = P ∨ (P : Matrix (Fin n) (Fin n) (Qbar l))ᵀ = -P) → (∀ g ∈ S, IntM (g : Matrix (Fin n) (Fin n) (Qbar l)) ∧ IntM ((P * g * P⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l))) → ∃ Q P' : GL (Fin n) (Qbar l), (P' : Matrix (Fin n) (Fin n) (Qbar l)) = (Q : Matrix (Fin n) (Fin n) (Qbar l))ᵀ * P * Q ∧ IntM (P' : Matrix (Fin n) (Fin n) (Qbar l)) ∧ IntM ((P'⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) ∧ ∀ g ∈ S, IntM ((Q⁻¹ * g * Q : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) := by
  intro l _ n S P hP hS
  obtain ⟨U, V, d, hU, hU', hV, hV', hd, hPe⟩ := smith P
  have hsq : ∀ i, ∃ z : Qbar l, d i = z * z := fun i => IsAlgClosed.exists_eq_mul_self (d i)
  choose e hee using hsq
  have he : ∀ i, e i ≠ 0 := fun i h => hd i (by rw [hee i, h, mul_zero])
  obtain ⟨E, hE, hE'⟩ : ∃ E : GL (Fin n) (Qbar l), (E : Matrix (Fin n) (Fin n) (Qbar l)) = diagonal e ∧
      ((E⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) = diagonal (fun i => (e i)⁻¹) := by
    refine ⟨⟨diagonal e, diagonal (fun i => (e i)⁻¹), ?_, ?_⟩, rfl, rfl⟩
    · rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1; funext i; exact mul_inv_cancel₀ (he i)
    · rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1; funext i; exact inv_mul_cancel₀ (he i)
  obtain ⟨T, hT, hT'⟩ : ∃ T : GL (Fin n) (Qbar l),
      (T : Matrix (Fin n) (Fin n) (Qbar l)) = (V : Matrix (Fin n) (Fin n) (Qbar l))ᵀ ∧
      ((T⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) =
        ((V⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l))ᵀ := by
    refine ⟨⟨(V : Matrix (Fin n) (Fin n) (Qbar l))ᵀ,
      ((V⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l))ᵀ, ?_, ?_⟩, rfl, rfl⟩
    · rw [← Matrix.transpose_mul, V.inv_mul, Matrix.transpose_one]
    · rw [← Matrix.transpose_mul, V.mul_inv, Matrix.transpose_one]
  have hPG : P = U * (E * E) * V := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, Units.val_mul, hE, Matrix.diagonal_mul_diagonal, hPe]
    congr 3; funext i; exact hee i
  have hQt : ((V⁻¹ * E⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l))ᵀ
      = ((E⁻¹ * T⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) := by
    rw [Units.val_mul, Units.val_mul, Matrix.transpose_mul, hT', hE', Matrix.diagonal_transpose]
  have hP' : ((E⁻¹ * (T⁻¹ * U) * E : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) =
      ((V⁻¹ * E⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l))ᵀ * P *
        ((V⁻¹ * E⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) := by
    rw [hQt, ← Units.val_mul, ← Units.val_mul, hPG]
    congr 1
    group
  have hsym : ((E⁻¹ * (T⁻¹ * U) * E : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l))ᵀ =
        ((E⁻¹ * (T⁻¹ * U) * E : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) ∨
      ((E⁻¹ * (T⁻¹ * U) * E : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l))ᵀ =
        -((E⁻¹ * (T⁻¹ * U) * E : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) := by
    rw [hP', Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mul_assoc]
    rcases hP with h | h
    · left; rw [h]
    · right; rw [h, Matrix.mul_neg, Matrix.neg_mul]
  refine ⟨V⁻¹ * E⁻¹, E⁻¹ * (T⁻¹ * U) * E, hP', ?_, ?_, ?_⟩
  · rw [Units.val_mul, Units.val_mul, hE, hE'] at hsym ⊢
    refine intM_of_symm e he ?_ hsym
    rw [Units.val_mul, hT']
    exact intM_mul' (intM_transpose' hV') hU
  · have hi := inv_symm _ hsym
    have hinv : (E⁻¹ * (T⁻¹ * U) * E)⁻¹ = E⁻¹ * (U⁻¹ * T) * E := by group
    rw [hinv, Units.val_mul, Units.val_mul, hE, hE'] at hi ⊢
    refine intM_of_symm e he ?_ hi
    rw [Units.val_mul, hT]
    exact intM_mul' hU' (intM_transpose' hV)
  · intro g hg
    obtain ⟨h1, h2⟩ := hS g hg
    have e1 : (V⁻¹ * E⁻¹)⁻¹ * g * (V⁻¹ * E⁻¹) = E * (V * g * V⁻¹) * E⁻¹ := by group
    have e2 : E * E * (V * g * V⁻¹) * E⁻¹ * E⁻¹ = U⁻¹ * (P * g * P⁻¹) * U := by
      rw [hPG]; group
    rw [e1, Units.val_mul, Units.val_mul, hE, hE']
    refine intM_mid e he ?_ ?_
    · rw [Units.val_mul, Units.val_mul]
      exact intM_mul' (intM_mul' hV h1) hV'
    · rw [← hE, ← hE', ← Units.val_mul, ← Units.val_mul, ← Units.val_mul, ← Units.val_mul, e2,
        Units.val_mul, Units.val_mul]
      exact intM_mul' (intM_mul' hU' h2) hU
