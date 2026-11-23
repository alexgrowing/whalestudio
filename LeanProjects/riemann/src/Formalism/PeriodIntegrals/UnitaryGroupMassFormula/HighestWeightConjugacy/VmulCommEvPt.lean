import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightConjugacy.ConjugationSwap

noncomputable section

open NumberField Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP Matrix

namespace PI.UnitaryGroupMassFormula.HwConjInf

section

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

abbrev Vars (L : Type) [Field L] (n : ℕ) := (L →+* ℂ) × Fin n × Fin n

def vmul (y z : Vars L n → ℂ) : Vars L n → ℂ := fun p => ∑ k, y (p.1, p.2.1, k) * z (p.1, k, p.2.2)

theorem eval_aeval_eq {σ' : Type} (y : σ' → ℂ) (f : Vars L n → MvPolynomial σ' ℂ) (Q : MvPolynomial (Vars L n) ℂ) :
    MvPolynomial.eval y (MvPolynomial.aeval f Q) = MvPolynomial.eval (fun p => MvPolynomial.eval y (f p)) Q := by
  induction Q using MvPolynomial.induction_on with
  | C c => rw [MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, MvPolynomial.eval_C, MvPolynomial.eval_C]
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add]
  | mul_X p i hp => rw [map_mul, map_mul, hp, MvPolynomial.aeval_X, map_mul, MvPolynomial.eval_X]

def tInv (g : GL (Fin n) ℂ) : GL (Fin n) ℂ :=
  ⟨((g⁻¹).val)ᵀ, (g.val)ᵀ,
    by rw [← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.transpose_one]⟩

theorem inV_evPt (τ : L →+* ℂ) (g : GL (Fin n) ℂ) : InV (evPt τ g) := by
  intro σ
  by_cases h1 : σ = τ
  · subst h1
    refine ⟨g, fun i j => ⟨?_, ?_⟩⟩
    · simp [evPt]
    · simp [evPt, conj_ne σ]
  · by_cases h2 : σ = ComplexEmbedding.conjugate τ
    · subst h2
      refine ⟨tInv g, fun i j => ⟨?_, ?_⟩⟩
      · simp [evPt, conj_ne τ, tInv]
      · simp [evPt, conj_conj, tInv]
    · have h3 : ComplexEmbedding.conjugate σ ≠ τ := fun h => h2 (by rw [← h, conj_conj])
      have h4 : ComplexEmbedding.conjugate σ ≠ ComplexEmbedding.conjugate τ := fun h => h1 (by
        rw [← conj_conj σ, h, conj_conj])
      refine ⟨1, fun i j => ⟨?_, ?_⟩⟩
      · simp [evPt, h1, h2, Matrix.one_apply]
      · simp [evPt, h3, h4, Matrix.one_apply, eq_comm]

theorem unit_conj (γ₀ : GL (Fin n) L) (hg : γ₀ ∈ GQ0 L n) (i j : Fin n) :
    (IsCMField.complexConj L : L →+* L) (γ₀.val i j) = (γ₀⁻¹).val j i := by
  have hg' : γ₀.val * conjT (IsCMField.complexConj L : L →+* L) γ₀.val = 1 := hg
  rw [Units.inv_eq_of_mul_eq_one_right hg']
  rfl

theorem conj_ratPt (γ₀ : GL (Fin n) L) (hg : γ₀ ∈ GQ0 L n) (σ : L →+* ℂ) (i j : Fin n) :
    (ComplexEmbedding.conjugate σ) (γ₀.val i j) = σ ((γ₀⁻¹).val j i) := by
  rw [← unit_conj γ₀ hg]
  exact (IsCMField.complexEmbedding_complexConj (K := L) σ _).symm

theorem inV_ratPt (γ₀ : GL (Fin n) L) (hg : γ₀ ∈ GQ0 L n) : InV (ratPt (γ₀ : Matrix (Fin n) (Fin n) L)) := by
  intro σ
  refine ⟨Matrix.GeneralLinearGroup.map σ γ₀, fun i j => ⟨rfl, ?_⟩⟩
  rw [← map_inv]
  exact conj_ratPt γ₀ hg σ i j

open Classical in

def trivAt (τ : L →+* ℂ) (y : Vars L n → ℂ) : Vars L n → ℂ := fun p =>
  if p.1 = τ ∨ p.1 = ComplexEmbedding.conjugate τ then (if p.2.1 = p.2.2 then 1 else 0) else y p

theorem inV_trivAt (τ : L →+* ℂ) (y : Vars L n → ℂ) (hy : InV y) : InV (trivAt τ y) := by
  intro σ
  by_cases h : σ = τ ∨ σ = ComplexEmbedding.conjugate τ
  · have h' : ComplexEmbedding.conjugate σ = τ ∨ ComplexEmbedding.conjugate σ = ComplexEmbedding.conjugate τ := by
      rcases h with h | h <;> subst h <;> simp [conj_conj]
    refine ⟨1, fun i j => ⟨?_, ?_⟩⟩
    · simp only [trivAt, if_pos h]; simp [Matrix.one_apply]
    · simp only [trivAt, if_pos h']; simp [Matrix.one_apply, eq_comm]
  · have h' : ¬ (ComplexEmbedding.conjugate σ = τ ∨ ComplexEmbedding.conjugate σ = ComplexEmbedding.conjugate τ) := by
      rintro (h1 | h1)
      · exact h (Or.inr (by rw [← h1, conj_conj]))
      · exact h (Or.inl (by rw [← conj_conj σ, h1, conj_conj]))
    obtain ⟨B, hB⟩ := hy σ
    exact ⟨B, fun i j => by simp only [trivAt, h, h', if_false]; exact hB i j⟩

theorem trivAt_tau (τ : L →+* ℂ) (y : Vars L n → ℂ) (i j : Fin n) :
    trivAt τ y (τ, i, j) = if i = j then 1 else 0 := by simp [trivAt]

theorem trivAt_conj (τ : L →+* ℂ) (y : Vars L n → ℂ) (i j : Fin n) :
    trivAt τ y (ComplexEmbedding.conjugate τ, i, j) = if i = j then 1 else 0 := by simp [trivAt]

theorem ratPt_split (τ : L →+* ℂ) (γ₀ : GL (Fin n) L) (hg : γ₀ ∈ GQ0 L n) :
    ratPt (γ₀ : Matrix (Fin n) (Fin n) L) =
      vmul (trivAt τ (ratPt (γ₀ : Matrix (Fin n) (Fin n) L))) (evPt τ (Matrix.GeneralLinearGroup.map τ γ₀)) := by
  funext p
  obtain ⟨σ, i, j⟩ := p
  by_cases h1 : σ = τ
  · subst h1
    simp [vmul, trivAt, evPt, ratPt]
  · by_cases h2 : σ = ComplexEmbedding.conjugate τ
    · subst h2
      have e1 : ∀ k, trivAt τ (ratPt (γ₀ : Matrix (Fin n) (Fin n) L)) (ComplexEmbedding.conjugate τ, i, k) =
          if i = k then 1 else 0 := fun k => trivAt_conj τ _ i k
      have e2 : ∀ k, evPt τ (Matrix.GeneralLinearGroup.map τ γ₀) (ComplexEmbedding.conjugate τ, k, j) =
          ((Matrix.GeneralLinearGroup.map τ γ₀)⁻¹).val j k := fun k => by
        simp only [evPt, conj_ne τ, if_false, if_true]
      simp only [vmul, e1, e2, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      show (ComplexEmbedding.conjugate τ) (γ₀.val i j) = _
      rw [conj_ratPt γ₀ hg, ← map_inv]
      rfl
    · simp [vmul, trivAt, evPt, ratPt, h1, h2]

theorem vmul_comm_evPt (τ : L →+* ℂ) (y : Vars L n → ℂ)
    (hy : ∀ i j, y (τ, i, j) = (if i = j then 1 else 0) ∧ y (ComplexEmbedding.conjugate τ, i, j) = (if i = j then 1 else 0))
    (g : GL (Fin n) ℂ) : vmul y (evPt τ g) = vmul (evPt τ g) y := by
  funext p
  obtain ⟨σ, i, j⟩ := p
  by_cases h1 : σ = τ
  · subst h1
    simp [vmul, evPt, (hy _ _).1]
  · by_cases h2 : σ = ComplexEmbedding.conjugate τ
    · subst h2
      simp [vmul, evPt, (hy _ _).2, conj_ne τ]
    · simp [vmul, evPt, h1, h2]

theorem evPt_mul (τ : L →+* ℂ) (g h : GL (Fin n) ℂ) : evPt τ (g * h) = vmul (evPt τ g) (evPt τ h) := by
  funext p
  obtain ⟨σ, i, j⟩ := p
  by_cases h1 : σ = τ
  · subst h1
    simp [vmul, evPt, Matrix.mul_apply]
  · by_cases h2 : σ = ComplexEmbedding.conjugate τ
    · subst h2
      simp [vmul, evPt, conj_ne τ, Matrix.mul_apply, mul_comm]
    · simp [vmul, evPt, h1, h2]

theorem vmul_ratPt (γ₀ δ₀ : Matrix (Fin n) (Fin n) L) : vmul (ratPt γ₀) (ratPt δ₀) = ratPt (γ₀ * δ₀) := by
  funext p
  simp [vmul, ratPt, Matrix.mul_apply]

end

end PI.UnitaryGroupMassFormula.HwConjInf
