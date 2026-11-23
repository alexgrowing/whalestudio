import Mathlib
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.ClifMod
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.DominantRearrangementProperties

noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

namespace UpperTheory.RealTr.CfB

variable {n : ℕ}

private theorem ex_add (x y : Wt n) : ex (x + y) = ex x * ex y := by
  simp [ex, AddMonoidAlgebra.single_mul_single]

private theorem ex_zero : ex (0 : Wt n) = 1 := rfl

private theorem cf_ext {f g : FR n} (h : ∀ x, cf f x = cf g x) : f = g :=
  AddMonoidAlgebra.ext (Finsupp.ext h)

private theorem cf_add (f g : FR n) (x : Wt n) : cf (f + g) x = cf f x + cf g x := rfl

private theorem cf_smul (c : ℂ) (f : FR n) (x : Wt n) : cf (c • f) x = c * cf f x := rfl

private theorem cf_sum {ι : Type} (s : Finset ι) (f : ι → FR n) (x : Wt n) :
    cf (∑ i ∈ s, f i) x = ∑ i ∈ s, cf (f i) x := by
  simp [cf, Finsupp.finset_sum_apply]

private theorem cf_ex (y x : Wt n) : cf (ex y) x = if y = x then 1 else 0 := by
  classical
  simp [cf, ex, Finsupp.single_apply]

private theorem eq_sum (f : FR n) : f = ∑ y ∈ f.coeff.support, cf f y • ex y := by
  classical
  apply cf_ext
  intro x
  rw [cf_sum]
  simp only [cf_smul, cf_ex, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq' f.coeff.support x]
  split_ifs with h
  · rfl
  · simpa [cf] using h

private theorem cf_ex_mul (f : FR n) (x y : Wt n) : cf (ex y * f) x = cf f (x - y) := by
  classical
  conv_lhs => rw [eq_sum f]
  conv_rhs => rw [eq_sum f]
  rw [Finset.mul_sum, cf_sum, cf_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [mul_smul_comm, cf_smul, cf_smul, ← ex_add, cf_ex, cf_ex]
  congr 2
  simp only [eq_iff_iff]
  constructor
  · intro h; rw [← h]; abel
  · intro h; rw [h]; abel

private theorem cf_mul (f g : FR n) (x : Wt n) :
    cf (f * g) x = ∑ y ∈ f.coeff.support, cf f y * cf g (x - y) := by
  conv_lhs => rw [eq_sum f]
  rw [Finset.sum_mul, cf_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [smul_mul_assoc, cf_smul, cf_ex_mul]

private theorem sg_mul (a b : Equiv.Perm (Fin n)) : sg (a * b) = sg a * sg b := by
  simp [sg, Equiv.Perm.sign_mul]

private theorem sg_one : sg (1 : Equiv.Perm (Fin n)) = 1 := by simp [sg]

private theorem sg_symm (a : Equiv.Perm (Fin n)) : sg a.symm = sg a := by
  simp [sg, Equiv.Perm.sign_symm]

private theorem sg_sq (a : Equiv.Perm (Fin n)) : sg a * sg a = 1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign a) with h | h <;> simp [sg, h]

private def pe (v : Equiv.Perm (Fin n)) : Wt n ≃+ Wt n where
  toFun x := x ∘ v
  invFun x := x ∘ v.symm
  left_inv x := by ext a; simp
  right_inv x := by ext a; simp
  map_add' _ _ := rfl

private def act (v : Equiv.Perm (Fin n)) : FR n ≃ₐ[ℂ] FR n := AddMonoidAlgebra.domCongr ℂ ℂ (pe v)

private theorem cf_act (v : Equiv.Perm (Fin n)) (f : FR n) (x : Wt n) :
    cf (act v f) x = cf f (x ∘ v.symm) :=
  AddMonoidAlgebra.coeff_domCongr (pe v) f x

private theorem act_ex (v : Equiv.Perm (Fin n)) (x : Wt n) : act v (ex x) = ex (x ∘ v) :=
  AddMonoidAlgebra.domCongr_single (pe v) x 1

private theorem sym_iff (f : FR n) : UpperTheory.RealTr.Sym f ↔ ∀ v, act v f = f := by
  constructor
  · intro h v
    apply cf_ext
    intro x
    rw [cf_act]
    exact h v.symm x
  · intro h w x
    have e := cf_act w.symm f x
    rw [h w.symm] at e
    exact e.symm

private theorem asym_iff (f : FR n) : ASym f ↔ ∀ v, act v f = sg v • f := by
  constructor
  · intro h v
    apply cf_ext
    intro x
    rw [cf_act, cf_smul, h v.symm x, sg_symm]
  · intro h w x
    have e := cf_act w.symm f x
    rw [h w.symm, cf_smul, sg_symm] at e
    exact e.symm

private theorem alt_comp (x : Wt n) (w : Equiv.Perm (Fin n)) : alt (x ∘ w) = sg w • alt x := by
  unfold alt
  rw [Finset.smul_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft w) _ _ fun u => ?_
  have e : (x ∘ w) ∘ u = x ∘ (Equiv.mulLeft w u) := rfl
  rw [e, smul_smul]
  congr 1
  simp only [Equiv.coe_mulLeft, sg_mul]
  rw [← mul_assoc, sg_sq, one_mul]

private theorem act_alt (x : Wt n) (v : Equiv.Perm (Fin n)) : act v (alt x) = sg v • alt x := by
  unfold alt
  rw [map_sum, Finset.smul_sum]
  refine Fintype.sum_equiv (Equiv.mulRight v) _ _ fun u => ?_
  have e : (x ∘ u) ∘ v = x ∘ (Equiv.mulRight v u) := rfl
  rw [map_smul, act_ex, e, smul_smul]
  congr 1
  simp only [Equiv.coe_mulRight, sg_mul]
  rw [mul_comm (sg v), mul_assoc, sg_sq, mul_one]

private theorem cf_alt (x y : Wt n) :
    cf (alt x) y = ∑ w : Equiv.Perm (Fin n), sg w * if x ∘ w = y then 1 else 0 := by
  unfold alt
  rw [cf_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [cf_smul, cf_ex]

private theorem cf_alt_mul (f : FR n) (x y : Wt n) :
    cf (alt y * f) x = ∑ w : Equiv.Perm (Fin n), sg w * cf f (x - y ∘ w) := by
  unfold alt
  rw [Finset.sum_mul, cf_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [smul_mul_assoc, cf_smul, cf_ex_mul]

private theorem alt_supp (x y : Wt n) (h : cf (alt x) y ≠ 0) :
    ∃ w : Equiv.Perm (Fin n), y = x ∘ w := by
  by_contra hc
  push_neg at hc
  apply h
  rw [cf_alt]
  refine Finset.sum_eq_zero fun w _ => ?_
  rw [if_neg fun e => hc w e.symm, mul_zero]

private theorem alt_top (x : Wt n) (hx : StrictAnti x) : cf (alt x) x = 1 := by
  rw [cf_alt, Finset.sum_eq_single 1]
  · simp [sg_one]
  · intro w _ hw
    rw [if_neg, mul_zero]
    intro e
    apply hw
    ext a
    have h : x (w a) = x a := congrFun e a
    simp [hx.injective h]
  · simp

private theorem alt_other (x y : Wt n) (hx : StrictAnti x) (hy : StrictAnti y) (hne : y ≠ x) :
    cf (alt x) y = 0 := by
  by_contra h
  obtain ⟨w, rfl⟩ := alt_supp x y h
  have hw : StrictMono w := fun a b hab => by
    by_contra hc
    exact absurd (hx.antitone (not_lt.1 hc)) (not_le.2 (hy hab))
  have e : ∀ a, w a = a := fun a => by
    have k := congrArg (fun g : Fin n ≃o Fin n => g a)
      (Subsingleton.elim (hw.orderIsoOfSurjective w w.surjective) (OrderIso.refl _))
    simpa using k
  apply hne
  funext a
  simp [e]

private theorem alt_zero (x : Wt n) (h : ¬ Function.Injective x) : alt x = 0 := by
  obtain ⟨a, b, hab, hne⟩ := Function.not_injective_iff.1 h
  have e : x ∘ (Equiv.swap a b) = x := by
    ext c
    simp only [Function.comp_apply, Equiv.swap_apply_def]
    split_ifs with h1 h2
    · rw [h1, hab]
    · rw [h2, hab]
    · rfl
  have s : sg (Equiv.swap a b) = -1 := by simp [sg, Equiv.Perm.sign_swap hne]
  have k := alt_comp x (Equiv.swap a b)
  rw [e, s] at k
  apply cf_ext
  intro z
  have c : cf (alt x) z = (-1) * cf (alt x) z := by
    conv_lhs => rw [k]
    rfl
  have d : cf (0 : FR n) z = 0 := rfl
  rw [d]
  linear_combination (1 / 2 : ℂ) * c

end UpperTheory.RealTr.CfB

open UpperTheory.RealTr.CfB in
theorem UpperTheory.RealTr.cfBasic :
    ∀ n : ℕ, (∀ x y : Wt n, ex (x + y) = ex x * ex y) ∧ ex (0 : Wt n) = 1 ∧ (∀ f g : FR n, (∀ x, cf f x = cf g x) → f = g) ∧
      (∀ (f g : FR n) (c : ℂ) x, cf (f + g) x = cf f x + cf g x ∧ cf (c • f) x = c * cf f x) ∧
      (∀ (f : FR n) x y, cf (ex y * f) x = cf f (x - y)) ∧ (∀ (f g : FR n) x, cf (f * g) x ≠ 0 → ∃ y, cf f y ≠ 0 ∧ cf g (x - y) ≠ 0) ∧
      (∀ (f : FR n) x y, cf (alt y * f) x = ∑ w : Equiv.Perm (Fin n), sg w * cf f (x - y ∘ w)) ∧
      (∀ (x : Wt n) (w : Equiv.Perm (Fin n)), alt (x ∘ w) = sg w • alt x) ∧ (∀ x : Wt n, ASym (alt x)) ∧
      (∀ f g : FR n, Sym f → (ASym g → ASym (f * g)) ∧ (Sym g → Sym (f * g))) ∧
      (∀ x y : Wt n, cf (alt x) y ≠ 0 → ∃ w : Equiv.Perm (Fin n), y = x ∘ w) ∧
      (∀ x : Wt n, StrictAnti x → cf (alt x) x = 1 ∧ ∀ y, StrictAnti y → y ≠ x → cf (alt x) y = 0) ∧
      ∀ x : Wt n, ¬ Function.Injective x → alt x = 0 := by
  intro n
  refine ⟨ex_add, ex_zero, fun f g h => cf_ext h, fun f g c x => ⟨cf_add f g x, cf_smul c f x⟩,
    cf_ex_mul, ?_, cf_alt_mul, alt_comp, fun x => (asym_iff _).2 (act_alt x), ?_, alt_supp,
    fun x hx => ⟨alt_top x hx, fun y hy hne => alt_other x y hx hy hne⟩, alt_zero⟩
  · intro f g x h
    by_contra hc
    push_neg at hc
    apply h
    rw [cf_mul]
    refine Finset.sum_eq_zero fun y _ => ?_
    by_cases hy : cf f y = 0
    · rw [hy, zero_mul]
    · rw [hc y hy, mul_zero]
  · intro f g hf
    have hf' := (sym_iff f).1 hf
    refine ⟨fun hg => (asym_iff _).2 fun v => ?_, fun hg => (sym_iff _).2 fun v => ?_⟩
    · rw [map_mul, hf', (asym_iff g).1 hg v, mul_smul_comm]
    · rw [map_mul, hf', (sym_iff g).1 hg v]
