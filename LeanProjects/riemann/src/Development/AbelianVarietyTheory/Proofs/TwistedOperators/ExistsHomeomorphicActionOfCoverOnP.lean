import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousExptPY

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory

namespace GlobalTheory.PolarU

private theorem jpq_eq_diagonal' (p q : ℕ) : Formalism.UG.Jpq p q =
    Matrix.diagonal (Sum.elim (fun _ : Fin p => (1 : ℂ)) (fun _ : Fin q => (-1 : ℂ))) := by
  ext a b
  rcases a with a | a <;> rcases b with b | b <;>
    simp [Formalism.UG.Jpq, Matrix.diagonal_apply, Matrix.one_apply] <;> split_ifs <;> simp

private theorem mul_jpq_comm_of_isKC {p q : ℕ} (X : Mat p q) (hX : IsKC X) :
    X * Formalism.UG.Jpq p q = Formalism.UG.Jpq p q * X := by
  rw [jpq_eq_diagonal']
  ext a b
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  rcases a with a | a <;> rcases b with b | b
  · simp
  · simp [hX (Sum.inl a) (Sum.inr b) (by simp [sameBlock])]
  · simp [hX (Sum.inr a) (Sum.inl b) (by simp [sameBlock])]
  · simp

private theorem Jpq_mul_Jpq_mul (p q : ℕ) : Formalism.UG.Jpq p q * Formalism.UG.Jpq p q = 1 := by
  rw [jpq_eq_diagonal', Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  rcases i with i | i <;> simp

private theorem exists_UJ_umat_eq_of_inUJ {p q : ℕ} (g : Mat p q) (hg : gᴴ * Formalism.UG.Jpq p q * g = Formalism.UG.Jpq p q)
    (hK : IsKC g) : gᴴ * g = 1 := by
  calc gᴴ * g = gᴴ * g * (Formalism.UG.Jpq p q * Formalism.UG.Jpq p q) := by rw [Jpq_mul_Jpq_mul, Matrix.mul_one]
    _ = gᴴ * (g * Formalism.UG.Jpq p q) * Formalism.UG.Jpq p q := by simp only [Matrix.mul_assoc]
    _ = gᴴ * Formalism.UG.Jpq p q * g * Formalism.UG.Jpq p q := by rw [mul_jpq_comm_of_isKC g hK]; simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hg, Jpq_mul_Jpq_mul]

private theorem unitary_inv_of_unitary {n : Type} [Fintype n] [DecidableEq n] (u : GL n ℂ)
    (hu : (u : Matrix n n ℂ)ᴴ * (u : Matrix n n ℂ) = 1) :
    ((u⁻¹ : GL n ℂ) : Matrix n n ℂ)ᴴ * ((u⁻¹ : GL n ℂ) : Matrix n n ℂ) = 1 := by
  have h1 : ((u⁻¹ : GL n ℂ) : Matrix n n ℂ) = (u : Matrix n n ℂ)ᴴ := by
    calc ((u⁻¹ : GL n ℂ) : Matrix n n ℂ)
        = (u : Matrix n n ℂ)ᴴ * (u : Matrix n n ℂ) * ((u⁻¹ : GL n ℂ) : Matrix n n ℂ) := by
          rw [hu, Matrix.one_mul]
      _ = (u : Matrix n n ℂ)ᴴ := by rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  rw [h1, Matrix.conjTranspose_conjTranspose, ← h1]
  exact Units.mul_inv u

private theorem conjTranspose_mul_self_mul_eq_one {n : Type} [Fintype n] [DecidableEq n] (A B : Matrix n n ℂ)
    (hA : Aᴴ * A = 1) (hB : Bᴴ * B = 1) : (A * B)ᴴ * (A * B) = 1 := by
  rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Aᴴ, hA, Matrix.one_mul, hB]

private theorem pY_mem_upq {p q : ℕ} (B : Fin p → Fin q → ℂ) : pY B ∈ upq p q := by
  show (pY B)ᴴ * Jm p q + Jm p q * pY B = 0
  rw [show Jm p q = Formalism.UG.Jpq p q from rfl, jpq_eq_diagonal']
  ext a b
  rcases a with i | i <;> rcases b with j | j <;>
    simp [pY, pOf, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply]

private theorem eq_pY_of_mem_pR {p q : ℕ} (Y : Mat p q) (hYm : Y ∈ pR p q) :
    Y = pY (fun i j => Y (Sum.inl i) (Sum.inr j)) := by
  have h2 : Y ∈ upq p q ∧ IsPC Y := hYm
  have hY : Yᴴ * Formalism.UG.Jpq p q + Formalism.UG.Jpq p q * Y = 0 := h2.1
  have hP : ∀ a b, sameBlock a b → Y a b = 0 := h2.2
  rw [jpq_eq_diagonal'] at hY
  ext a b
  rcases a with i | i <;> rcases b with j | j
  · rw [hP _ _ (by simp [sameBlock])]
    simp [pY, pOf]
  · simp [pY, pOf]
  · have h := congrArg (fun M : Mat p q => M (Sum.inr i) (Sum.inl j)) hY
    simp only [Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply,
      Sum.elim_inl, Sum.elim_inr, Matrix.zero_apply] at h
    simp only [pY, pOf, Matrix.fromBlocks_apply₂₁, Matrix.conjTranspose_apply, Matrix.of_apply]
    linear_combination -h
  · rw [hP _ _ (by simp [sameBlock])]
    simp [pY, pOf]

theorem exists_action_on_p : ∀ (p q : ℕ) (T : GrpData p q) (L : Mat p q → (Fin p → Fin q → ℂ)), ContinuousOn L {g | IsUnit g} → (∀ (k : Mat p q) (B : Fin p → Fin q → ℂ), kᴴ * k = 1 → L (k * NormedSpace.exp (pY B)) = B) → (∀ g : T.G, ∃ k ∈ T.Kset, ∃ Y ∈ pR p q, g = k * T.expt Y) → ∀ g : T.G, ∃ ψ : (Fin p → Fin q → ℂ) → (Fin p → Fin q → ℂ), Continuous ψ ∧ Function.Bijective ψ ∧ ∀ B, ∃ κ ∈ T.Kset, T.expt (pY B) * g = κ * T.expt (pY (ψ B)) := by
  intro p q T L hLc hL hdec g
  have hexp : ∀ X ∈ upq p q, ((T.cov (T.expt X) : GL _ ℂ) : Mat p q) = NormedSpace.exp X := T.16
  have hec : ContinuousOn T.expt (upq p q) := T.17
  have hcov : Continuous fun x : T.G => ((T.cov x : GL _ ℂ) : Mat p q) :=
    Units.continuous_val.comp (continuous_fst.comp T.emb.continuous)
  have hKu : ∀ k ∈ T.Kset, ((T.cov k : GL _ ℂ) : Mat p q)ᴴ * ((T.cov k : GL _ ℂ) : Mat p q) = 1 := by
    intro k hk
    exact exists_UJ_umat_eq_of_inUJ ((T.cov k : GL _ ℂ) : Mat p q) (T.cov_mem k) hk
  have hKinv : ∀ k ∈ T.Kset,
      ((T.cov k⁻¹ : GL _ ℂ) : Mat p q)ᴴ * ((T.cov k⁻¹ : GL _ ℂ) : Mat p q) = 1 := by
    intro k hk
    rw [map_inv]
    exact unitary_inv_of_unitary _ (hKu k hk)
  have hev : ∀ u : T.G, ((T.cov u : GL _ ℂ) : Mat p q)ᴴ * ((T.cov u : GL _ ℂ) : Mat p q) = 1 →
      ∀ C, L ((T.cov (u * T.expt (pY C)) : GL _ ℂ) : Mat p q) = C := by
    intro u hu C
    rw [map_mul, Units.val_mul, hexp _ (pY_mem_upq C)]
    exact hL _ C hu
  have hkey : ∀ h : T.G, ∃ k ∈ T.Kset,
      h = k * T.expt (pY (L ((T.cov h : GL _ ℂ) : Mat p q))) := by
    intro h
    obtain ⟨k, hk, Y, hY, rfl⟩ := hdec h
    obtain ⟨C, hC⟩ : ∃ C, Y = pY C := ⟨_, eq_pY_of_mem_pR Y hY⟩
    subst hC
    exact ⟨k, hk, by rw [hev k (hKu k hk) C]⟩
  refine ⟨fun B => L ((T.cov (T.expt (pY B) * g) : GL _ ℂ) : Mat p q), ?_, ?_, ?_⟩
  · have hof : Continuous fun B : Fin p → Fin q → ℂ => (Matrix.of B : Matrix (Fin p) (Fin q) ℂ) :=
      continuous_matrix fun i j => by simp only [Matrix.of_apply]; fun_prop
    have hpY : Continuous fun B : Fin p → Fin q → ℂ => pY B := by
      simp only [pY, pOf]
      exact Continuous.matrix_fromBlocks continuous_const hof hof.matrix_conjTranspose continuous_const
    have hE : Continuous fun B : Fin p → Fin q → ℂ => T.expt (pY B) :=
      hec.comp_continuous hpY pY_mem_upq
    have hM : Continuous fun B : Fin p → Fin q → ℂ =>
        ((T.cov (T.expt (pY B) * g) : GL _ ℂ) : Mat p q) :=
      hcov.comp (hE.mul continuous_const)
    exact hLc.comp_continuous hM (fun B => (T.cov _).isUnit)
  · constructor
    · intro B1 B2 h12
      dsimp only at h12
      obtain ⟨k1, hk1, e1⟩ := hkey (T.expt (pY B1) * g)
      obtain ⟨k2, hk2, e2⟩ := hkey (T.expt (pY B2) * g)
      rw [← h12] at e2
      generalize L ((T.cov (T.expt (pY B1) * g) : GL _ ℂ) : Mat p q) = C at e1 e2
      have f1 := eq_mul_inv_of_mul_eq e1
      have f2 := eq_mul_inv_of_mul_eq e2
      have e3 : T.expt (pY B1) = (k1 * k2⁻¹) * T.expt (pY B2) := by
        rw [f1, f2]
        group
      have hB1 : L ((T.cov (1 * T.expt (pY B1)) : GL _ ℂ) : Mat p q) = B1 := hev 1 (by simp) B1
      have hB2 : L ((T.cov ((k1 * k2⁻¹) * T.expt (pY B2)) : GL _ ℂ) : Mat p q) = B2 :=
        hev _ (by rw [map_mul, Units.val_mul]; exact conjTranspose_mul_self_mul_eq_one _ _ (hKu k1 hk1) (hKinv k2 hk2)) B2
      rw [one_mul, e3] at hB1
      exact hB1.symm.trans hB2
    · intro C
      obtain ⟨k, hk, e⟩ := hkey (T.expt (pY C) * g⁻¹)
      refine ⟨L ((T.cov (T.expt (pY C) * g⁻¹) : GL _ ℂ) : Mat p q), ?_⟩
      dsimp only
      generalize L ((T.cov (T.expt (pY C) * g⁻¹) : GL _ ℂ) : Mat p q) = B at e ⊢
      have f := eq_inv_mul_of_mul_eq e.symm
      have e' : T.expt (pY B) * g = k⁻¹ * T.expt (pY C) := by
        rw [f]
        group
      rw [e']
      exact hev _ (hKinv k hk) C
  · intro B
    exact hkey (T.expt (pY B) * g)

end GlobalTheory.PolarU
