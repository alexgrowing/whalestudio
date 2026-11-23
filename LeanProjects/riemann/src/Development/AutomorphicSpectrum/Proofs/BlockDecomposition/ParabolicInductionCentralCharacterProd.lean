import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanNecTemp
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.PropsCos
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL Filter Topology

namespace GlobalTheory.CompanionTheory.ZCentre

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem scalar_apply {R : Type} [Field R] {n : Type} [Fintype n] [DecidableEq n] (t : Rˣ) (i j : n) :
    ((Matrix.GeneralLinearGroup.scalar n t : GL n R) : Matrix n n R) i j = if i = j then (t : R) else 0 := by
  simp [Matrix.GeneralLinearGroup.scalar, Matrix.scalar_apply, Matrix.diagonal_apply]

theorem det_scalar {R : Type} [Field R] {n : Type} [Fintype n] [DecidableEq n] (t : Rˣ) :
    Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar n t : GL n R) = t ^ Fintype.card n := by
  ext; simp [Matrix.GeneralLinearGroup.scalar]

theorem scalar_comm {R : Type} [Field R] {n : Type} [Fintype n] [DecidableEq n] (t : Rˣ) (g : GL n R) :
    g * Matrix.GeneralLinearGroup.scalar n t = Matrix.GeneralLinearGroup.scalar n t * g := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  simp [Matrix.GeneralLinearGroup.scalar, Matrix.mul_apply, Matrix.scalar_apply, Matrix.diagonal_apply, mul_comm]

variable {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
  [Fintype n] [DecidableEq n]

theorem sum_card_mul_modExp : ∑ a, (Fintype.card (m a) : ℤ) * modExp m a = 0 := by
  simp only [modExp, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_filter]
  rw [sub_eq_zero, Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  split_ifs <;> simp [mul_comm]

variable (k) in

theorem deltaHalf_scalar (t : kˣ) :
    deltaHalf k m (fun a => Matrix.GeneralLinearGroup.scalar (m a) t) = 1 := by
  have h1 : modulus k m (fun a => Matrix.GeneralLinearGroup.scalar (m a) t) = 1 := by
    have h2 : ∀ a, nabs k (Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (m a) t : GL (m a) k)) ^ modExp m a =
        nabs k t ^ ((Fintype.card (m a) : ℤ) * modExp m a) := fun a => by
      rw [det_scalar, zpow_mul, zpow_natCast]
      congr 1
      simp [nabs]
    simp only [modulus, h2]
    have h3 : ∀ (s : Finset α) (f : α → ℤ), ∏ a ∈ s, nabs k t ^ f a = nabs k t ^ ∑ a ∈ s, f a := fun s f => by
      induction s using Finset.induction_on with
      | empty => simp
      | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, zpow_add₀ (nabs_pos' k t).ne', ih]
    rw [h3, sum_card_mul_modExp, zpow_zero]
  refine Units.ext ?_
  rw [val_deltaHalf, h1]
  simp

theorem piTensor_scalar {Γ X : α → Type} [∀ a, Group (Γ a)] [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
    (ρ : ∀ a, Representation ℂ (Γ a) (X a)) (g : ∀ a, Γ a) (c : α → ℂ)
    (h : ∀ a v, ρ a (g a) v = c a • v) (w : PiTensorProduct ℂ X) :
    piTensor ρ g w = (∏ a, c a) • w := by
  induction w using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    rw [map_smul, piTensor_tprod, smul_comm]
    congr 1
    simp only [h]
    exact MultilinearMap.map_smul_univ _ _ _
  | add x y hx hy => rw [map_add, hx, hy, smul_add]

theorem scalar_mem_parab (e : (Σ a, m a) ≃ n) (t : kˣ) :
    Matrix.GeneralLinearGroup.scalar n t ∈ parab k e := by
  refine mem_parab.2 fun i j hij => ?_
  rw [scalar_apply, if_neg]
  rintro rfl
  exact lt_irrefl _ hij

theorem leviProj_scalar (e : (Σ a, m a) ≃ n) (t : kˣ) :
    leviProj k e ⟨_, scalar_mem_parab e t⟩ = fun a => Matrix.GeneralLinearGroup.scalar (m a) t := by
  funext a
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [leviProj_apply, scalar_apply, scalar_apply]
  simp

theorem parInd_scalar {W : Type} [AddCommGroup W] [Module ℂ W] (e : (Σ a, m a) ≃ n)
    (ρ : Representation ℂ (Levi k m) W) (t : kˣ) (c : ℂ)
    (h : ∀ w, ρ (fun a => Matrix.GeneralLinearGroup.scalar (m a) t) w = c • w) (f : IndSp e ρ) :
    parInd e ρ (Matrix.GeneralLinearGroup.scalar n t) f = c • f := by
  refine Subtype.ext (Subtype.ext (funext fun g => ?_))
  have h1 := parInd_law e ρ f ⟨_, scalar_mem_parab e t⟩ g
  rw [leviProj_scalar, deltaHalf_scalar, h] at h1
  rw [parInd_apply, scalar_comm]
  simpa using h1

theorem prodIrr_scalar : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (h N : ℕ) (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N) (t : kˣ) (c : Fin h → ℂ),
    (∀ a, Zl.ScalarBy (x a) t (c a)) →
      ∀ v, prodIrr x hd (Matrix.GeneralLinearGroup.scalar (Fin N) t) v = (∏ a, c a) • v := by
  intro k _ _ _ _ h N x hd t c hc v
  exact parInd_scalar _ _ t _ (fun w => piTensor_scalar _ _ c (fun a v => hc a v) w) v

end GlobalTheory.CompanionTheory.ZCentre

end
