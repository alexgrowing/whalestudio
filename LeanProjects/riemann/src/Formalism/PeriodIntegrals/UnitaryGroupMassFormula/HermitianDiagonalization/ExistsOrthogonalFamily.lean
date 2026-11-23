import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianDiagonalization.HermDiag

namespace PI.UnitaryGroupMassFormula.HermConj

open Matrix

variable {E : Type} [Field E]

structure IsHermForm (σ : E →+* E) {V : Type} [AddCommGroup V] [Module E V]
    (h : V → V → E) : Prop where
  add : ∀ x y z, h x (y + z) = h x y + h x z
  smul : ∀ x (a : E) y, h x (a • y) = a * h x y
  herm : ∀ x y, h y x = σ (h x y)

section Form

variable {σ : E →+* E} {V : Type} [AddCommGroup V] [Module E V] {h : V → V → E}

theorem IsHermForm.add_left (hh : IsHermForm σ h) (x y z : V) :
    h (x + y) z = h x z + h y z := by
  rw [hh.herm z (x + y), hh.add, map_add, ← hh.herm z x, ← hh.herm z y]

theorem IsHermForm.smul_left (hh : IsHermForm σ h) (a : E) (x y : V) :
    h (a • x) y = σ a * h x y := by
  rw [hh.herm y (a • x), hh.smul, map_mul, ← hh.herm y x]

theorem IsHermForm.eq_zero_of_diag [CharZero E] (hh : IsHermForm σ h)
    (hz : ∀ x, h x x = 0) (x y : V) : h x y = 0 := by
  have hsum : ∀ u v, h u v + h v u = 0 := by
    intro u v
    have e := hz (u + v)
    rw [hh.add_left, hh.add, hh.add, hz u, hz v] at e
    linear_combination e
  have hfix : ∀ a : E, (σ a - a) * h x y = 0 := by
    intro a
    have e := hsum (a • x) y
    rw [hh.smul_left, hh.smul] at e
    have e2 := hsum x y
    linear_combination e - a * e2
  by_contra hne
  have hσ : ∀ a, σ a = a := by
    intro a
    rcases mul_eq_zero.1 (hfix a) with h1 | h1
    · linear_combination h1
    · exact absurd h1 hne
  have e := hsum x y
  rw [hh.herm x y, hσ] at e
  have e2 : (2 : E) * h x y = 0 := by linear_combination e
  rcases mul_eq_zero.1 e2 with h2 | h2
  · norm_num at h2
  · exact hne h2

end Form

theorem exists_orthogonal_family [CharZero E] (σ : E →+* E) :
    ∀ (k : ℕ) (V : Type) [AddCommGroup V] [Module E V] [FiniteDimensional E V],
      Module.finrank E V = k → ∀ h : V → V → E, IsHermForm σ h →
        ∃ v : Fin k → V, LinearIndependent E v ∧ ∀ i j, i ≠ j → h (v i) (v j) = 0 := by
  intro k
  induction k with
  | zero =>
    intro V _ _ _ hk h hh
    exact ⟨Fin.elim0, linearIndependent_empty_type, fun i => Fin.elim0 i⟩
  | succ k ih =>
    intro V _ _ _ hk h hh
    by_cases hzero : ∀ x, h x x = 0
    · let b := Module.finBasisOfFinrankEq E V hk
      exact ⟨b, b.linearIndependent, fun i j _ => hh.eq_zero_of_diag hzero _ _⟩
    · push_neg at hzero
      obtain ⟨v, hv⟩ := hzero
      let f : V →ₗ[E] E :=
        { toFun := h v
          map_add' := hh.add v
          map_smul' := fun a y => by
            simp only [RingHom.id_apply, smul_eq_mul]
            exact hh.smul v a y }
      have hfv : ∀ y, f y = h v y := fun _ => rfl
      have hf : f v ≠ 0 := hv
      have hsurj : Function.Surjective f := by
        intro c
        refine ⟨(c / f v) • v, ?_⟩
        rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hf]
      have hW : Module.finrank E (LinearMap.ker f) = k := by
        have := LinearMap.finrank_range_add_finrank_ker f
        rw [LinearMap.range_eq_top.2 hsurj, finrank_top, Module.finrank_self] at this
        omega
      obtain ⟨w, hwi, hwo⟩ := ih (LinearMap.ker f) hW (fun x y => h x y)
        ⟨fun x y z => hh.add _ _ _, fun x a y => hh.smul _ _ _, fun x y => hh.herm _ _⟩
      have hw0 : ∀ i, h v (w i) = 0 := fun i => by
        rw [← hfv]; exact LinearMap.mem_ker.1 (w i).2
      refine ⟨Fin.cons v (fun i => (w i : V)), ?_, ?_⟩
      · rw [linearIndependent_fin_cons]
        refine ⟨hwi.map' (LinearMap.ker f).subtype (Submodule.ker_subtype _), ?_⟩
        intro hmem
        have hle : Submodule.span E (Set.range fun i => (w i : V)) ≤ LinearMap.ker f :=
          Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact (w i).2)
        exact hf (LinearMap.mem_ker.1 (hle hmem))
      · intro i j hij
        cases i using Fin.cases with
        | zero =>
          cases j using Fin.cases with
          | zero => exact absurd rfl hij
          | succ j => simpa using hw0 j
        | succ i =>
          cases j using Fin.cases with
          | zero =>
            simp only [Fin.cons_zero, Fin.cons_succ]
            rw [hh.herm, hw0 i, map_zero]
          | succ j =>
            simp only [Fin.cons_succ]
            exact hwo i j (fun e => hij (by rw [e]))

end PI.UnitaryGroupMassFormula.HermConj
