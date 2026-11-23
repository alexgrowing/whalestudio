import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZAEqAlgebraMapPt

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKGal.JumpDR

section Abstract

variable {R O B K V C : Type} [CommSemiring R] [Semiring O] [Algebra R O] [Semiring B] [Algebra R B]
  [CommSemiring K] [AddCommMonoid V] [Module K V] [Semiring C] [Module K C]

theorem tensorAct_mul (s : O → V → V) (φ : B →+* C)
    (act : O ⊗[R] B →+ (V ⊗[K] C →+ V ⊗[K] C))
    (hs : ∀ (o o' : O) (v : V), s (o * o') v = s o (s o' v))
    (h : ∀ (o : O) (b : B) (v : V) (c : C), act (o ⊗ₜ[R] b) (v ⊗ₜ[K] c) = s o v ⊗ₜ[K] (φ b * c))
    (d d' : O ⊗[R] B) (w : V ⊗[K] C) : act (d * d') w = act d (act d' w) := by
  induction d using TensorProduct.induction_on with
  | zero => simp only [zero_mul, map_zero, AddMonoidHom.zero_apply]
  | add x y hx hy => simp only [add_mul, map_add, AddMonoidHom.add_apply, hx, hy]
  | tmul o b =>
    induction d' using TensorProduct.induction_on with
    | zero => simp only [mul_zero, map_zero, AddMonoidHom.zero_apply]
    | add x y hx hy => simp only [mul_add, map_add, AddMonoidHom.add_apply, hx, hy]
    | tmul o' b' =>
      induction w using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | add x y hx hy => simp only [map_add, hx, hy]
      | tmul v c =>
        rw [Algebra.TensorProduct.tmul_mul_tmul, h, h, h, hs, map_mul, mul_assoc]

theorem tensorAct_one (s : O → V → V) (φ : B →+* C)
    (act : O ⊗[R] B →+ (V ⊗[K] C →+ V ⊗[K] C))
    (hs : ∀ v : V, s 1 v = v)
    (h : ∀ (o : O) (b : B) (v : V) (c : C), act (o ⊗ₜ[R] b) (v ⊗ₜ[K] c) = s o v ⊗ₜ[K] (φ b * c))
    (w : V ⊗[K] C) : act 1 w = w := by
  rw [Algebra.TensorProduct.one_def]
  induction w using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul v c => rw [h, hs, map_one, one_mul]

end Abstract

theorem odAct_mul_one : ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l) (T : QLat LL) (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI) (act : OD l ↥(OL LL) →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR)), (∀ (o : ↥(OL LL)) (b : Per.BdRp l) (v : T.V) (c : Pl.R.BdR), act (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (GlobalTheory.BKGal.JumpDR.cD Td b * c)) → (∀ (d d' : OD l ↥(OL LL)) (w : T.V ⊗[ℚ_[l]] Pl.R.BdR), act (d * d') w = act d (act d' w)) ∧ ∀ w : T.V ⊗[ℚ_[l]] Pl.R.BdR, act 1 w = w :=
  fun _ _ LL T _ _ Td act h =>
    ⟨tensorAct_mul (fun (o : ↥(OL LL)) (v : T.V) => (o : ↥LL.1) • v) (cD Td) act
        (fun o o' v => mul_smul (o : ↥LL.1) (o' : ↥LL.1) v) h,
      tensorAct_one (fun (o : ↥(OL LL)) (v : T.V) => (o : ↥LL.1) • v) (cD Td) act
        (fun v => one_smul ↥LL.1 v) h⟩

end GlobalTheory.BKGal.JumpDR
