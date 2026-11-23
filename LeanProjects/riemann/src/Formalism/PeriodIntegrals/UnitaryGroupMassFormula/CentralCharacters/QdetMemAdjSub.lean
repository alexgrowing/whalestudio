import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CentralCharacters.CentralScalar

noncomputable section

namespace PI.UnitaryGroupMassFormula.DSIC

open PI.DSInfCharCap
open scoped InnerProductSpace Matrix

def opOn {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (S : Submodule ℂ H) (f : H → H)
    (hst : ∀ v ∈ S, f v ∈ S) (hadd : ∀ v ∈ S, ∀ w ∈ S, f (v + w) = f v + f w)
    (hsm : ∀ (c : ℂ), ∀ v ∈ S, f (c • v) = c • f v) : Module.End ℂ S where
  toFun v := ⟨f v, hst v v.2⟩
  map_add' v w := Subtype.ext (hadd v v.2 w w.2)
  map_smul' c v := Subtype.ext (hsm c v v.2)

theorem qdet_map {A B : Type*} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] {n : ℕ} (φ : A →ₐ[ℂ] B)
    (E : Fin n → Fin n → A) (u : ℂ) :
    φ (Formalism.REAL.qdet E u) = Formalism.REAL.qdet (fun a b => φ (E a b)) u := by
  unfold Formalism.REAL.qdet Formalism.REAL.qminor
  rw [map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [map_mul, map_intCast, map_list_prod, List.map_ofFn]
  congr 2
  all_goals first
    | (funext k; simp [Formalism.REAL.Tm, apply_ite])
    | (congr 1; funext k; simp [Formalism.REAL.Tm, apply_ite])

def conjHom {A : Type*} [Ring A] [Algebra ℂ A] (P P' : A) (h1 : P' * P = 1) (h2 : P * P' = 1) : A →ₐ[ℂ] A where
  toFun X := P * X * P'
  map_one' := by rw [mul_one, h2]
  map_mul' X Y := by
    calc P * (X * Y) * P' = P * X * (P' * P) * Y * P' := by rw [h1]; noncomm_ring
      _ = P * X * P' * (P * Y * P') := by noncomm_ring
  map_zero' := by rw [mul_zero, zero_mul]
  map_add' X Y := by rw [mul_add, add_mul]
  commutes' r := by
    show P * algebraMap ℂ A r * P' = algebraMap ℂ A r
    rw [← Algebra.commutes r P, mul_assoc, h2, mul_one]

def adjSub {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (S : Submodule ℂ H) :
    Subalgebra ℂ (Module.End ℂ S) where
  carrier := {X | ∃ X' : Module.End ℂ S, ∀ v w : S, ⟪((X v : S) : H), (w : H)⟫_ℂ = ⟪(v : H), ((X' w : S) : H)⟫_ℂ}
  mul_mem' := by
    rintro X Y ⟨X', hX⟩ ⟨Y', hY⟩
    refine ⟨Y' * X', fun v w => ?_⟩
    rw [Module.End.mul_apply, hX, hY, Module.End.mul_apply]
  add_mem' := by
    rintro X Y ⟨X', hX⟩ ⟨Y', hY⟩
    refine ⟨X' + Y', fun v w => ?_⟩
    rw [LinearMap.add_apply, LinearMap.add_apply, Submodule.coe_add, Submodule.coe_add, inner_add_left,
      inner_add_right, hX, hY]
  algebraMap_mem' r := by
    refine ⟨algebraMap ℂ (Module.End ℂ S) ((starRingEnd ℂ) r), fun v w => ?_⟩
    rw [Module.algebraMap_end_apply, Module.algebraMap_end_apply, Submodule.coe_smul, Submodule.coe_smul,
      inner_smul_left, inner_smul_right]

end PI.UnitaryGroupMassFormula.DSIC
