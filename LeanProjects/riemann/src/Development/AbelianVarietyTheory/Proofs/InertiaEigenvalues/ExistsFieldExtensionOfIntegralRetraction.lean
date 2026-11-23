import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftQMk
open Formalism.MainNotions.N Formalism.BasicNotions.Loc GlobalTheory.UseLoc

noncomputable section

namespace GlobalTheory.UseLoc.ExtRet

variable {l : ℕ} [Fact l.Prime] {LL LL' : FinExt l}

theorem algebraMap_ne_zero (LL : FinExt l) {d : ℤ_[l]} (hd : d ≠ 0) : algebraMap ℤ_[l] LL.1 d ≠ 0 := by
  rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] LL.1]
  intro h0
  apply hd
  have h1 : algebraMap ℤ_[l] ℚ_[l] d = 0 := (map_eq_zero_iff _ (algebraMap ℚ_[l] LL.1).injective).1 h0
  exact (map_eq_zero_iff _ (IsFractionRing.injective ℤ_[l] ℚ_[l])).1 h1

theorem exists_mul (LL : FinExt l) (x : LL.1) : ∃ d : ℤ_[l], d ≠ 0 ∧ IsIntegral ℤ_[l] (d • x) := by
  haveI := LL.2
  haveI : Algebra.IsAlgebraic ℤ_[l] LL.1 :=
    (IsFractionRing.comap_isAlgebraic_iff (A := ℤ_[l]) (K := ℚ_[l]) (C := LL.1)).2 inferInstance
  exact (Algebra.IsAlgebraic.isAlgebraic x).exists_integral_multiple

theorem r_smul (h : LL.1 ≤ LL'.1) (r : ↥(OL LL') →+ ↥(OL LL))
    (hr : ∀ (a : ↥(OL LL)) (x : ↥(OL LL')), r (incO h a * x) = a * r x) (c : ℤ_[l]) (z : ↥(OL LL')) :
    ((r (c • z) : ↥(OL LL)) : LL.1) = algebraMap ℤ_[l] LL.1 c * ((r z : ↥(OL LL)) : LL.1) := by
  have e : c • z = incO h (algebraMap ℤ_[l] (OL LL) c) * z := by
    apply Subtype.ext
    simp [incO, Algebra.smul_def]
  rw [e, hr]
  simp

def ext (r : ↥(OL LL') →+ ↥(OL LL)) (x : LL'.1) : LL.1 :=
  ((r ⟨(exists_mul LL' x).choose • x, (exists_mul LL' x).choose_spec.2⟩ : ↥(OL LL)) : LL.1) /
    algebraMap ℤ_[l] LL.1 (exists_mul LL' x).choose

theorem ext_eq (h : LL.1 ≤ LL'.1) (r : ↥(OL LL') →+ ↥(OL LL))
    (hr : ∀ (a : ↥(OL LL)) (x : ↥(OL LL')), r (incO h a * x) = a * r x)
    (x : LL'.1) (d : ℤ_[l]) (hd : d ≠ 0) (y : ↥(OL LL')) (hy : (y : LL'.1) = d • x) :
    ext r x = ((r y : ↥(OL LL)) : LL.1) / algebraMap ℤ_[l] LL.1 d := by
  unfold ext
  set d0 := (exists_mul LL' x).choose with hd0def
  have hd0 : d0 ≠ 0 := (exists_mul LL' x).choose_spec.1
  set y0 : ↥(OL LL') := ⟨d0 • x, (exists_mul LL' x).choose_spec.2⟩ with hy0
  have key : d • y0 = d0 • y := by
    apply Subtype.ext
    simp only [SetLike.val_smul, hy0, hy, smul_smul, mul_comm]
  have k2 := congrArg (fun z => ((r z : ↥(OL LL)) : LL.1)) key
  simp only [r_smul h r hr] at k2
  rw [div_eq_div_iff (algebraMap_ne_zero LL hd0) (algebraMap_ne_zero LL hd)]
  linear_combination k2

theorem ext_add (h : LL.1 ≤ LL'.1) (r : ↥(OL LL') →+ ↥(OL LL))
    (hr : ∀ (a : ↥(OL LL)) (x : ↥(OL LL')), r (incO h a * x) = a * r x) (x₁ x₂ : LL'.1) :
    ext r (x₁ + x₂) = ext r x₁ + ext r x₂ := by
  obtain ⟨d₁, hd₁, hi₁⟩ := exists_mul LL' x₁
  obtain ⟨d₂, hd₂, hi₂⟩ := exists_mul LL' x₂
  let y₁ : ↥(OL LL') := ⟨d₁ • x₁, hi₁⟩
  let y₂ : ↥(OL LL') := ⟨d₂ • x₂, hi₂⟩
  have hy : ((d₂ • y₁ + d₁ • y₂ : ↥(OL LL')) : LL'.1) = (d₁ * d₂) • (x₁ + x₂) := by
    simp only [y₁, y₂, Subalgebra.coe_add, SetLike.val_smul, smul_smul, smul_add]
    rw [mul_comm d₂ d₁]
  rw [ext_eq h r hr _ (d₁ * d₂) (mul_ne_zero hd₁ hd₂) _ hy, ext_eq h r hr x₁ d₁ hd₁ y₁ rfl,
    ext_eq h r hr x₂ d₂ hd₂ y₂ rfl, map_add, Subalgebra.coe_add, r_smul h r hr, r_smul h r hr, map_mul]
  have n₁ := algebraMap_ne_zero LL hd₁
  have n₂ := algebraMap_ne_zero LL hd₂
  field_simp

theorem ext_mul (h : LL.1 ≤ LL'.1) (r : ↥(OL LL') →+ ↥(OL LL))
    (hr : ∀ (a : ↥(OL LL)) (x : ↥(OL LL')), r (incO h a * x) = a * r x) (a : LL.1) (x : LL'.1) :
    ext r (IntermediateField.inclusion h a * x) = a * ext r x := by
  obtain ⟨d, hd, hi⟩ := exists_mul LL' x
  obtain ⟨e, he, hie⟩ := exists_mul LL a
  let y : ↥(OL LL') := ⟨d • x, hi⟩
  let a'' : ↥(OL LL) := ⟨e • a, hie⟩
  have hy : ((incO h a'' * y : ↥(OL LL')) : LL'.1) = (e * d) • (IntermediateField.inclusion h a * x) := by
    simp only [incO, y, a'', RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, Subalgebra.coe_mul,
      SetLike.val_smul, map_smul]
    simp only [Algebra.smul_def, map_mul]
    have hc : IntermediateField.inclusion h (algebraMap ℤ_[l] LL.1 e) = algebraMap ℤ_[l] LL'.1 e := by simp
    rw [hc]
    ring
  rw [ext_eq h r hr _ (e * d) (mul_ne_zero he hd) _ hy, ext_eq h r hr x d hd y rfl, hr,
    Subalgebra.coe_mul, map_mul]
  have n₁ := algebraMap_ne_zero LL hd
  have n₂ := algebraMap_ne_zero LL he
  have ha : ((a'' : ↥(OL LL)) : LL.1) = algebraMap ℤ_[l] LL.1 e * a := by
    simp [a'', Algebra.smul_def]
  rw [ha]
  field_simp

theorem ext_int (h : LL.1 ≤ LL'.1) (r : ↥(OL LL') →+ ↥(OL LL))
    (hr : ∀ (a : ↥(OL LL)) (x : ↥(OL LL')), r (incO h a * x) = a * r x) (x : ↥(OL LL')) :
    ext r (x : LL'.1) = ((r x : ↥(OL LL)) : LL.1) := by
  rw [ext_eq h r hr _ 1 one_ne_zero x (by simp)]
  simp

end GlobalTheory.UseLoc.ExtRet

namespace GlobalTheory.UseLoc

theorem extRet_exists : ∀ {l : ℕ} [Fact l.Prime] {LL LL' : FinExt l} (h : LL.1 ≤ LL'.1) (r : ↥(OL LL') →+ ↥(OL LL)), (∀ (a : ↥(OL LL)) (x : ↥(OL LL')), r (incO h a * x) = a * r x) → r 1 = 1 → ∃ p : ↥LL'.1 →ₗ[ℚ_[l]] ↥LL.1, (∀ (a : ↥LL.1) (x : ↥LL'.1), p (IntermediateField.inclusion h a * x) = a * p x) ∧ ∀ x : ↥(OL LL'), p (x : ↥LL'.1) = ((r x : ↥(OL LL)) : ↥LL.1) := by
  intro l _ LL LL' h r hr _
  refine ⟨{ toFun := ExtRet.ext r
            map_add' := ExtRet.ext_add h r hr
            map_smul' := fun q x => ?_ }, ExtRet.ext_mul h r hr, ExtRet.ext_int h r hr⟩
  have e : q • x = IntermediateField.inclusion h (algebraMap ℚ_[l] LL.1 q) * x := by
    rw [Algebra.smul_def]
    rfl
  simp only [RingHom.id_apply]
  rw [e, ExtRet.ext_mul h r hr, Algebra.smul_def]

end GlobalTheory.UseLoc
