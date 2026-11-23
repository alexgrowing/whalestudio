import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSmoothDetPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCentralScalarDistinctGeometricLemmaCells

noncomputable section

namespace GlobalTheory.IndLineGL.CellTorus

open GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.IndLineGL
open scoped TensorProduct

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem scalar_apply {n : Type} [Fintype n] [DecidableEq n] (t : kˣ) (p q : n) :
    ((Matrix.GeneralLinearGroup.scalar n t : GL n k) : Matrix n n k) p q = if p = q then (t : k) else 0 := by
  simp [Matrix.GeneralLinearGroup.scalar, Matrix.diagonal_apply]

theorem scalar_comm {n : Type} [Fintype n] [DecidableEq n] (t : kˣ) (x : GL n k) :
    x * Matrix.GeneralLinearGroup.scalar n t = Matrix.GeneralLinearGroup.scalar n t * x := by
  ext i j
  simp [Matrix.GeneralLinearGroup.scalar, Matrix.mul_diagonal, Matrix.diagonal_mul, mul_comm]

theorem modExp_three_zero (d : Fin 3 → ℕ) :
    modExp (fun j : Fin 3 => Fin (d j)) 0 = ((d 1 + d 2 : ℕ) : ℤ) := by
  simp [modExp, Finset.sum_filter, Fin.sum_univ_three]

theorem modExp_three_two (d : Fin 3 → ℕ) :
    modExp (fun j : Fin 3 => Fin (d j)) 2 = -((d 0 + d 1 : ℕ) : ℤ) := by
  simp [modExp, Finset.sum_filter, Fin.sum_univ_three]

theorem extTensor_detRep_apply {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
    (χ ψ : kˣ →* ℂˣ) (x : GL n k × GL n' k) (v : ℂ ⊗[ℂ] ℂ) :
    extTensor (detRep n χ) (detRep n' ψ) x v =
      ((χ (Matrix.GeneralLinearGroup.det x.1) * ψ (Matrix.GeneralLinearGroup.det x.2) : ℂˣ) : ℂ) • v := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul u w =>
    rw [extTensor_tmul]
    simp only [detRep, ofChar_apply, detChar_apply, Units.val_mul]
    rw [← smul_eq_mul, ← smul_eq_mul (a := ((ψ _ : ℂˣ) : ℂ)), TensorProduct.smul_tmul_smul]
  | add u w hu hw => rw [map_add, hu, hw, smul_add]

theorem row_scalar (χ : kˣ →* ℂˣ) (n b0 b1 b2 : ℕ) (hn : b0 + b1 + b2 = n) (h0 : b0 ≤ 1) (h2 : b2 ≤ 1)
    (e0 e1 e2 : ℤ) (he0 : e0 = ((b1 + b2 : ℕ) : ℤ)) (he2 : e2 = -((b0 + b1 : ℕ) : ℤ)) (t₁ t₂ : kˣ) :
    (absPow k ((e0 : ℂ) / 2) (t₁ ^ b0) * absPow k ((e1 : ℂ) / 2) 1 * absPow k ((e2 : ℂ) / 2) (t₂ ^ b2))⁻¹ *
        χ (t₁ ^ b0 * 1 * t₂ ^ b2) =
      ((χ * absPow k ((1 - (n : ℂ)) / 2)) t₁) ^ b0 * ((χ * absPow k (((n : ℂ) - 1) / 2)) t₂) ^ b2 := by
  have k0 : b0 = 1 → absPow k ((1 - (n : ℂ)) / 2) = (absPow k ((e0 : ℂ) / 2))⁻¹ := by
    intro h
    rw [← absPow_neg]
    congr 1
    subst he0
    rw [← hn, h]
    push_cast
    ring
  have k2 : b2 = 1 → absPow k (((n : ℂ) - 1) / 2) = (absPow k ((e2 : ℂ) / 2))⁻¹ := by
    intro h
    rw [← absPow_neg]
    congr 1
    subst he2
    rw [← hn, h]
    push_cast
    ring
  interval_cases b0 <;> interval_cases b2
  · simp
  · rw [k2 rfl]; simp [mul_comm]
  · rw [k0 rfl]; simp [mul_comm]
  · rw [k0 rfl, k2 rfl]; simp [mul_comm, mul_left_comm, mul_assoc]

end GlobalTheory.IndLineGL.CellTorus

namespace GlobalTheory.IndLineGL.CellTorus

open GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.IndLineGL
open scoped TensorProduct

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {m : ℕ} {b : Bool → Fin 3 → ℕ}

theorem torusPt_mem (g : ∀ j, (Σ i, Fin (b i j)) ≃ Fin (blk3 m j)) (t₁ t₂ : kˣ) :
    torusPt k m t₁ t₂ ∈ relParab k g := by
  refine (Subgroup.mem_pi _).2 fun j _ => ?_
  by_cases hj : j = 1
  · subst hj; rw [torusPt_one]; exact one_mem _
  · have : Subsingleton (Fin (blk3 m j)) := by
      fin_cases j
      · exact show Subsingleton (Fin 1) from inferInstance
      · exact absurd rfl hj
      · exact show Subsingleton (Fin 1) from inferInstance
    exact mem_parab.2 fun p q hpq => by rw [Subsingleton.elim p q] at hpq; exact absurd hpq (lt_irrefl _)

theorem torusPt_central (t₁ t₂ : kˣ) (x : Levi k fun i : Fin 3 => Fin (blk3 m i)) :
    x * torusPt k m t₁ t₂ = torusPt k m t₁ t₂ * x := by
  funext j
  simp only [Pi.mul_apply]
  fin_cases j
  · exact (torusPt_zero m t₁ t₂).symm ▸ scalar_comm t₁ (x 0)
  · show x 1 * torusPt k m t₁ t₂ 1 = torusPt k m t₁ t₂ 1 * x 1
    rw [torusPt_one, mul_one, one_mul]
  · exact (torusPt_two m t₁ t₂).symm ▸ scalar_comm t₂ (x 2)

end GlobalTheory.IndLineGL.CellTorus

namespace GlobalTheory.IndLineGL.CellTorus

open GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.IndLineGL
open scoped TensorProduct

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {m : ℕ} {b : Bool → Fin 3 → ℕ}

theorem relProj_torusPt_zero (g : ∀ j, (Σ i, Fin (b i j)) ≃ Fin (blk3 m j)) (t₁ t₂ : kˣ) (i : Bool) :
    relProj k g ⟨torusPt k m t₁ t₂, torusPt_mem g t₁ t₂⟩ 0 i =
      Matrix.GeneralLinearGroup.scalar (Fin (b i 0)) t₁ := by
  ext p q
  show ((torusPt k m t₁ t₂ 0 : GL _ k) : Matrix _ _ k) (g 0 ⟨i, p⟩) (g 0 ⟨i, q⟩) = _
  have hs : Subsingleton (Fin (blk3 m 0)) := show Subsingleton (Fin 1) from inferInstance
  have hpq : p = q := by
    have h := (g 0).injective (Subsingleton.elim (g 0 ⟨i, p⟩) (g 0 ⟨i, q⟩))
    exact eq_of_heq (Sigma.mk.inj_iff.1 h).2
  subst hpq
  rw [torusPt_zero, scalar_apply, scalar_apply]
  simp

theorem relProj_torusPt_one (g : ∀ j, (Σ i, Fin (b i j)) ≃ Fin (blk3 m j)) (t₁ t₂ : kˣ) :
    relProj k g ⟨torusPt k m t₁ t₂, torusPt_mem g t₁ t₂⟩ 1 = 1 := by
  funext i
  ext p q
  show ((torusPt k m t₁ t₂ 1 : GL _ k) : Matrix _ _ k) (g 1 ⟨i, p⟩) (g 1 ⟨i, q⟩) = _
  rw [torusPt_one]
  simp only [Units.val_one, Matrix.one_apply, (g 1).injective.eq_iff, Sigma.mk.inj_iff, heq_eq_eq, true_and,
    Pi.one_apply]

theorem relProj_torusPt_two (g : ∀ j, (Σ i, Fin (b i j)) ≃ Fin (blk3 m j)) (t₁ t₂ : kˣ) (i : Bool) :
    relProj k g ⟨torusPt k m t₁ t₂, torusPt_mem g t₁ t₂⟩ 2 i =
      Matrix.GeneralLinearGroup.scalar (Fin (b i 2)) t₂ := by
  ext p q
  show ((torusPt k m t₁ t₂ 2 : GL _ k) : Matrix _ _ k) (g 2 ⟨i, p⟩) (g 2 ⟨i, q⟩) = _
  have hs : Subsingleton (Fin (blk3 m 2)) := show Subsingleton (Fin 1) from inferInstance
  have hpq : p = q := by
    have h := (g 2).injective (Subsingleton.elim (g 2 ⟨i, p⟩) (g 2 ⟨i, q⟩))
    exact eq_of_heq (Sigma.mk.inj_iff.1 h).2
  subst hpq
  rw [torusPt_two, scalar_apply, scalar_apply]
  simp

theorem isEmpty_of_sum_one {x y : ℕ} (h : x + y = 1) (i i' : Bool) (hii : i ≠ i') :
    IsEmpty (Fin (cond i y x)) ∨ IsEmpty (Fin (cond i' y x)) := by
  rcases Nat.eq_zero_or_pos x with hx | hx
  · cases i <;> cases i'
    · exact absurd rfl hii
    · exact Or.inl (by simp [hx]; infer_instance)
    · exact Or.inr (by simp [hx]; infer_instance)
    · exact absurd rfl hii
  · have hy : y = 0 := by omega
    cases i <;> cases i'
    · exact absurd rfl hii
    · exact Or.inr (by simp [hy]; infer_instance)
    · exact Or.inl (by simp [hy]; infer_instance)
    · exact absurd rfl hii

theorem relDeltaHalf_cols_torusPt (g : ∀ j, (Σ i, Fin (b i j)) ≃ Fin (blk3 m j)) (t₁ t₂ : kˣ)
    (h0 : b false 0 + b true 0 = 1) (h2 : b false 2 + b true 2 = 1) :
    relDeltaHalf k (fun j i => Fin (b i j)) (relProj k g ⟨torusPt k m t₁ t₂, torusPt_mem g t₁ t₂⟩) = 1 := by
  rw [relDeltaHalf_apply, Fin.prod_univ_three, relProj_torusPt_one, map_one, mul_one]
  rw [GlobalTheory.CellCentral.deltaHalf_eq_one _ (fun i i' hii => ?_) _, GlobalTheory.CellCentral.deltaHalf_eq_one _ (fun i i' hii => ?_) _,
    mul_one]
  · have := isEmpty_of_sum_one h2 i i' hii
    cases i <;> cases i' <;> simpa using this
  · have := isEmpty_of_sum_one h0 i i' hii
    cases i <;> cases i' <;> simpa using this

end GlobalTheory.IndLineGL.CellTorus

namespace GlobalTheory.IndLineGL.CellTorus

open GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.IndLineGL
open scoped TensorProduct

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem row_block (χ : kˣ →* ℂˣ) (n : ℕ) (d : Fin 3 → ℕ) {X : Type} [Fintype X] [DecidableEq X]
    (e : (Σ j, Fin (d j)) ≃ X) (t₁ t₂ : kˣ) (Q : Levi k fun j : Fin 3 => Fin (d j))
    (hQ0 : Q 0 = Matrix.GeneralLinearGroup.scalar (Fin (d 0)) t₁) (hQ1 : Q 1 = 1)
    (hQ2 : Q 2 = Matrix.GeneralLinearGroup.scalar (Fin (d 2)) t₂)
    (hn : d 0 + d 1 + d 2 = n) (h0 : d 0 ≤ 1) (h2 : d 2 ≤ 1) :
    (deltaHalf k (fun j => Fin (d j)) Q)⁻¹ * χ (Matrix.GeneralLinearGroup.det (leviEmb k e Q)) =
      ((χ * absPow k ((1 - (n : ℂ)) / 2)) t₁) ^ d 0 * ((χ * absPow k (((n : ℂ) - 1) / 2)) t₂) ^ d 2 := by
  rw [deltaHalf_apply, det_leviEmb, Fin.prod_univ_three, Fin.prod_univ_three, hQ0, hQ1, hQ2,
    Matrix.GeneralLinearGroup.det_scalar, Matrix.GeneralLinearGroup.det_scalar, map_one, Fintype.card_fin,
    Fintype.card_fin]
  exact row_scalar χ n (d 0) (d 1) (d 2) hn h0 h2 _ _ _ (modExp_three_zero d) (modExp_three_two d) t₁ t₂

end GlobalTheory.IndLineGL.CellTorus

namespace GlobalTheory.IndLineGL.CellTorus

open GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.IndLineGL
open scoped TensorProduct

theorem cellFunctor_torusPt : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (a a' m : ℕ) (α₀ β₀ : kˣ →* ℂˣ) (b : SizeMatrix (Two (Fin a) (Fin a')) fun j : Fin 3 => Fin (blk3 m j))
    (f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ Two (Fin a) (Fin a') i) (g : ∀ j, (Σ i, Fin (b.1 i j)) ≃ Fin (blk3 m j))
    (t₁ t₂ : kˣ) y,
    cellFunctor f g (detPair k a a' α₀ β₀) (torusPt k m t₁ t₂) y = (cellChar k a a' α₀ β₀ b.1 t₁ t₂ : ℂ) • y := by
  intro k _ _ _ _ a a' m α₀ β₀ b f g t₁ t₂ y
  have hc0 : b.1 false 0 + b.1 true 0 = 1 := by
    have := b.2.2 0
    rw [Fintype.sum_bool, Fintype.card_fin] at this
    rw [add_comm]; exact this
  have hc2 : b.1 false 2 + b.1 true 2 = 1 := by
    have := b.2.2 2
    rw [Fintype.sum_bool, Fintype.card_fin] at this
    rw [add_comm]; exact this
  have hrf : b.1 false 0 + b.1 false 1 + b.1 false 2 = a := by
    have := b.2.1 false
    rw [Fin.sum_univ_three] at this
    rw [this]; exact Fintype.card_fin a
  have hrt : b.1 true 0 + b.1 true 1 + b.1 true 2 = a' := by
    have := b.2.1 true
    rw [Fin.sum_univ_three] at this
    rw [this]; exact Fintype.card_fin a'
  refine GlobalTheory.CellCentral.smInd_central _ _ _ (torusPt_mem g t₁ t₂) (torusPt_central t₁ t₂) _ (fun w => ?_) y
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  simp only [MonoidHom.comp_apply, twist_apply, relJac_mk]
  rw [relDeltaHalf_cols_torusPt g t₁ t₂ hc0 hc2, Units.val_one, one_smul]
  have hdp : ∀ (x : Levi k (Two (Fin a) (Fin a'))) (v : ℂ ⊗[ℂ] ℂ), detPair k a a' α₀ β₀ x v =
      ((α₀ (Matrix.GeneralLinearGroup.det (x false)) * β₀ (Matrix.GeneralLinearGroup.det (x true)) : ℂˣ) : ℂ) • v :=
    fun x v => extTensor_detRep_apply α₀ β₀ _ v
  rw [hdp, Submodule.Quotient.mk_smul, smul_smul, ← Units.val_mul]
  refine congrArg (· • _) (congrArg Units.val ?_)
  have hrow : ∀ (i : Bool) (χ : kˣ →* ℂˣ) (n : ℕ), b.1 i 0 + b.1 i 1 + b.1 i 2 = n →
      (deltaHalf k (fun j => Fin (b.1 i j))
          (swapBlocks k (fun i j => Fin (b.1 i j)) (relProj k g ⟨torusPt k m t₁ t₂, torusPt_mem g t₁ t₂⟩) i))⁻¹ *
        χ (Matrix.GeneralLinearGroup.det (relEmb k f
          (swapBlocks k (fun i j => Fin (b.1 i j)) (relProj k g ⟨torusPt k m t₁ t₂, torusPt_mem g t₁ t₂⟩)) i)) =
      ((χ * absPow k ((1 - (n : ℂ)) / 2)) t₁) ^ b.1 i 0 * ((χ * absPow k (((n : ℂ) - 1) / 2)) t₂) ^ b.1 i 2 := by
    intro i χ n hn
    rw [relEmb_apply]
    refine row_block χ n (b.1 i) (f i) t₁ t₂ _ (relProj_torusPt_zero g t₁ t₂ i) ?_ (relProj_torusPt_two g t₁ t₂ i) hn
      (by cases i <;> omega) (by cases i <;> omega)
    show relProj k g ⟨torusPt k m t₁ t₂, torusPt_mem g t₁ t₂⟩ 1 i = 1
    rw [relProj_torusPt_one]; rfl
  rw [relDeltaHalf_apply, Fintype.prod_bool, cellChar, Fintype.prod_bool]
  have h1 := hrow true β₀ a' hrt
  have h2 := hrow false α₀ a hrf
  simp only [cond_true, cond_false]
  rw [← h1, ← h2, mul_inv]
  ac_rfl

end GlobalTheory.IndLineGL.CellTorus
