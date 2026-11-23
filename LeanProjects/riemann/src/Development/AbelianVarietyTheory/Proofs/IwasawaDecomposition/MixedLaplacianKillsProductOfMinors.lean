import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqTopOfTranslates
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DefLift

namespace GlobalTheory.MinorHarmonic

theorem pderiv_comm {σ R : Type*} [CommRing R] (i j : σ) (f : MvPolynomial σ R) :
    MvPolynomial.pderiv i (MvPolynomial.pderiv j f) = MvPolynomial.pderiv j (MvPolynomial.pderiv i f) := by
  classical
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p k hp =>
    have h : ∀ a b : σ, MvPolynomial.pderiv a (MvPolynomial.pderiv b (MvPolynomial.X k : MvPolynomial σ R)) = 0 := by
      intro a b
      rw [MvPolynomial.pderiv_X]
      by_cases hk : k = b
      · subst hk; simp
      · simp [Pi.single_eq_of_ne hk]
    simp only [Derivation.leibniz, map_add, smul_eq_mul, hp, h]
    ring

def ker {σ : Type*} (v : σ) : Subring (MvPolynomial σ ℂ) where
  carrier := {f | MvPolynomial.pderiv v f = 0}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    simp [Derivation.leibniz, ha, hb]
  one_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    simp [ha, hb]
  zero_mem' := by simp
  neg_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    simp [ha]

theorem det_mem {R : Type*} [CommRing R] (S : Subring R) {k : ℕ} (M : Matrix (Fin k) (Fin k) R)
    (h : ∀ i j, M i j ∈ S) : M.det ∈ S := by
  rw [Matrix.det_apply']
  exact S.sum_mem fun σ _ => S.mul_mem (intCast_mem S _) (S.prod_mem fun i _ => h _ _)

variable {D : D7} {m n : ℕ}

theorem varF_mem (τ τ' : D.what₂.Tau) (a : Fin m) (c : Fin n) (i j : ℕ)
    (h : τ' = τ → i = a → j = c → False) :
    (varF τ' i j : MvPolynomial (FVar D m n) ℂ) ∈ ker ((τ, a, c) : FVar D m n) := by
  classical
  unfold varF
  split_ifs with h1
  · show MvPolynomial.pderiv _ _ = 0
    apply MvPolynomial.pderiv_X_of_ne
    intro he
    simp only [Prod.mk.injEq] at he
    exact h he.1 (congrArg Fin.val he.2.1) (congrArg Fin.val he.2.2)
  · exact Subring.zero_mem _

theorem delta_mem (p q : D.what₂.Tau → ℕ) (ap am : D.what₂.Tau → ℕ → ℕ) (hpq : ∀ τ, p τ + q τ ≤ n)
    (τ : D.what₂.Tau) (a : Fin m) (c : Fin n)
    (h : ((a : ℕ) < p τ ∧ p τ ≤ c) ∨ (p τ ≤ (a : ℕ) ∧ (c : ℕ) < p τ)) :
    (delta p q ap am : MvPolynomial (FVar D m n) ℂ) ∈ ker ((τ, a, c) : FVar D m n) := by
  unfold delta deltaAt
  refine Subring.prod_mem _ fun τ' _ => Subring.mul_mem _ ?_ ?_
  · refine Subring.prod_mem _ fun i hi => Subring.pow_mem _ ?_ _
    refine det_mem _ _ fun α β => varF_mem τ τ' a c _ _ ?_
    rintro rfl h1 h2
    have := Finset.mem_range.1 hi
    have := α.2
    have := β.2
    omega
  · refine Subring.prod_mem _ fun i hi => Subring.pow_mem _ ?_ _
    refine det_mem _ _ fun α β => varF_mem τ τ' a c _ _ ?_
    rintro rfl h1 h2
    have := Finset.mem_range.1 hi
    have := hpq τ'
    omega

theorem laplacian_delta : ∀ (D : D7) (m n : ℕ) (p q : D.what₂.Tau → ℕ) (ap am : D.what₂.Tau → ℕ → ℕ), (∀ τ, p τ + q τ ≤ n) → ∀ τ (a b : Fin m), p τ ≤ (a : ℕ) → (b : ℕ) < p τ → ∑ c : Fin n, MvPolynomial.pderiv (τ, a, c) (MvPolynomial.pderiv (τ, b, c) (delta p q ap am : PolF D m n)) = 0 := by
  intro D m n p q ap am hpq τ a b ha hb
  refine Finset.sum_eq_zero fun c _ => ?_
  rcases lt_or_ge (c : ℕ) (p τ) with hc | hc
  · rw [pderiv_comm]
    have : MvPolynomial.pderiv (τ, a, c) (delta p q ap am : PolF D m n) = 0 :=
      delta_mem p q ap am hpq τ a c (Or.inr ⟨ha, hc⟩)
    rw [this, map_zero]
  · have : MvPolynomial.pderiv (τ, b, c) (delta p q ap am : PolF D m n) = 0 :=
      delta_mem p q ap am hpq τ b c (Or.inl ⟨hb, hc⟩)
    rw [this, map_zero]

end GlobalTheory.MinorHarmonic

end
