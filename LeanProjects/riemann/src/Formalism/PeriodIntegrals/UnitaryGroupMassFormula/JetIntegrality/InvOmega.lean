import Mathlib
import Formalism.PeriodIntegrals.JetsPhW
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.InverseOmegaHolds
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsTerTer

noncomputable section

open Classical

namespace PI.JetsPhW.Inv

variable {p : ℕ} [Fact p.Prime]

noncomputable def intS (p : ℕ) [Fact p.Prime] : Subring ℂ_[p] :=
  _root_.UpperTheory.Reformulated.B.PadicComplexValuationRing.intS p

theorem coeff_mul_memS {S : Subring ℂ_[p]} {f g : PowerSeries ℂ_[p]} {m : ℕ}
    (hf : ∀ i ≤ m, PowerSeries.coeff i f ∈ S) (hg : ∀ i ≤ m, PowerSeries.coeff i g ∈ S) :
    PowerSeries.coeff m (f * g) ∈ S := by
  rw [PowerSeries.coeff_mul]
  refine S.sum_mem fun x hx => S.mul_mem (hf _ ?_) (hg _ ?_)
  · have := Finset.HasAntidiagonal.mem_antidiagonal.mp hx; omega
  · have := Finset.HasAntidiagonal.mem_antidiagonal.mp hx; omega

theorem coeff_pow_memS {S : Subring ℂ_[p]} {f : PowerSeries ℂ_[p]} {m : ℕ}
    (hf : ∀ i ≤ m, PowerSeries.coeff i f ∈ S) (k : ℕ) : ∀ i ≤ m, PowerSeries.coeff i (f ^ k) ∈ S := by
  induction k with
  | zero =>
    intro i _
    rw [pow_zero, PowerSeries.coeff_one]
    split_ifs
    · exact S.one_mem
    · exact S.zero_mem
  | succ k ih =>
    intro i hi
    rw [pow_succ]
    exact coeff_mul_memS (fun j hj => ih j (hj.trans hi)) (fun j hj => hf j (hj.trans hi))

theorem coeff_termS (a : ℂ_[p]) (k n : ℕ) (f : PowerSeries ℂ_[p]) :
    PowerSeries.coeff n (algebraMap ℂ_[p] (PowerSeries ℂ_[p]) a * PowerSeries.X ^ k * f) =
      if k ≤ n then a * PowerSeries.coeff (n - k) f else 0 := by
  rw [PowerSeries.algebraMap_apply, mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul']
  simp only [Algebra.algebraMap_self, RingHom.id_apply]
  split_ifs <;> simp

theorem wq_mem {S : Subring ℂ_[p]} {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]}
    (h1 : W.a₁ ∈ S) (h2 : W.a₂ ∈ S) (h3 : W.a₃ ∈ S) (h4 : W.a₄ ∈ S) (h6 : W.a₆ ∈ S) (h : IsWq W wq) :
    ∀ n, PowerSeries.coeff n wq ∈ S := by
  simp only [IsWq] at h
  have h' : wq = 1 + algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₁ * PowerSeries.X ^ 1 * wq +
      algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₂ * PowerSeries.X ^ 2 * wq +
      algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₃ * PowerSeries.X ^ 3 * wq ^ 2 +
      algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₄ * PowerSeries.X ^ 4 * wq ^ 2 +
      algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₆ * PowerSeries.X ^ 6 * wq ^ 3 := by
    rw [pow_one]; exact h
  have key : ∀ n, (∀ i < n, PowerSeries.coeff i wq ∈ S) → PowerSeries.coeff n wq ∈ S := by
    intro n ih
    rw [h']
    simp only [map_add, coeff_termS, PowerSeries.coeff_one]
    refine S.add_mem (S.add_mem (S.add_mem (S.add_mem (S.add_mem ?_ ?_) ?_) ?_) ?_) ?_
    · split_ifs
      · exact S.one_mem
      · exact S.zero_mem
    · split_ifs
      · exact S.mul_mem h1 (ih _ (by omega))
      · exact S.zero_mem
    · split_ifs
      · exact S.mul_mem h2 (ih _ (by omega))
      · exact S.zero_mem
    · split_ifs
      · exact S.mul_mem h3 (coeff_pow_memS (m := n - 3) (fun i hi => ih i (by omega)) 2 _ le_rfl)
      · exact S.zero_mem
    · split_ifs
      · exact S.mul_mem h4 (coeff_pow_memS (m := n - 4) (fun i hi => ih i (by omega)) 2 _ le_rfl)
      · exact S.zero_mem
    · split_ifs
      · exact S.mul_mem h6 (coeff_pow_memS (m := n - 6) (fun i hi => ih i (by omega)) 3 _ le_rfl)
      · exact S.zero_mem
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn => exact key n ihn

theorem wq_const {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]} (h : IsWq W wq) :
    PowerSeries.constantCoeff wq = 1 := by
  simp only [IsWq] at h
  have := congrArg PowerSeries.constantCoeff h
  simpa using this

def serS (S : Subring ℂ_[p]) : Subring (PowerSeries ℂ_[p]) where
  carrier := {f | ∀ n, PowerSeries.coeff n f ∈ S}
  mul_mem' {f g} hf hg n := coeff_mul_memS (fun i _ => hf i) (fun i _ => hg i)
  one_mem' n := by
    rw [PowerSeries.coeff_one]
    split_ifs
    · exact S.one_mem
    · exact S.zero_mem
  add_mem' {f g} hf hg n := by
    rw [map_add]; exact S.add_mem (hf n) (hg n)
  zero_mem' n := by simp
  neg_mem' {f} hf n := by
    rw [map_neg]; exact S.neg_mem (hf n)

theorem X_mem_serS (S : Subring ℂ_[p]) : (PowerSeries.X : PowerSeries ℂ_[p]) ∈ serS S := by
  intro n
  rw [PowerSeries.coeff_X]
  split_ifs
  · exact S.one_mem
  · exact S.zero_mem

theorem C_mem_serS {S : Subring ℂ_[p]} {a : ℂ_[p]} (ha : a ∈ S) :
    algebraMap ℂ_[p] (PowerSeries ℂ_[p]) a ∈ serS S := by
  intro n
  rw [PowerSeries.algebraMap_apply]
  simp only [Algebra.algebraMap_self, RingHom.id_apply, PowerSeries.coeff_C]
  split_ifs
  · exact ha
  · exact S.zero_mem

theorem dX_eq_derivative (f : PowerSeries ℂ_[p]) : dX f = PowerSeries.derivative ℂ_[p] f := by
  ext n
  simp only [dX, PowerSeries.coeff_mk, PowerSeries.coeff_derivative]
  ring

theorem dX_flog (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) :
    dX (flog W wq) = omegaW W wq := by
  ext n
  simp only [dX, PowerSeries.coeff_mk, flog, if_neg (Nat.succ_ne_zero n), Nat.add_sub_cancel]
  have h : ((n : ℂ_[p]) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  push_cast
  field_simp

def vInv (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) : PowerSeries ℂ_[p] :=
  1 - (algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₁ * PowerSeries.X +
    algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₂ * PowerSeries.X ^ 2 +
    2 * algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₃ * (PowerSeries.X ^ 3 * wq) +
    2 * algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₄ * PowerSeries.X * (PowerSeries.X ^ 3 * wq) +
    3 * algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₆ * (PowerSeries.X ^ 3 * wq) ^ 2)

theorem vInv_mul_omega {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]} (h : IsWq W wq) :
    vInv W wq * omegaW W wq = 1 := by
  have hc := wq_const h
  simp only [IsWq] at h
  have hd : PowerSeries.derivative ℂ_[p] wq =
      algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₁ * (wq + PowerSeries.X * PowerSeries.derivative ℂ_[p] wq) +
      algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₂ *
        (2 * PowerSeries.X * wq + PowerSeries.X ^ 2 * PowerSeries.derivative ℂ_[p] wq) +
      algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₃ *
        (3 * PowerSeries.X ^ 2 * wq ^ 2 + 2 * PowerSeries.X ^ 3 * wq * PowerSeries.derivative ℂ_[p] wq) +
      algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₄ *
        (4 * PowerSeries.X ^ 3 * wq ^ 2 + 2 * PowerSeries.X ^ 4 * wq * PowerSeries.derivative ℂ_[p] wq) +
      algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₆ *
        (6 * PowerSeries.X ^ 5 * wq ^ 3 + 3 * PowerSeries.X ^ 6 * wq ^ 2 * PowerSeries.derivative ℂ_[p] wq) := by
    conv_lhs => rw [h]
    simp only [map_add, Derivation.leibniz, Derivation.leibniz_pow, Derivation.map_algebraMap,
      PowerSeries.derivative_X, Derivation.map_one_eq_zero, smul_eq_mul, nsmul_eq_mul]
    norm_num
    ring
  have hden : PowerSeries.constantCoeff (wq * (algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₁ * PowerSeries.X +
      algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₃ * PowerSeries.X ^ 3 * wq - 2)) ≠ 0 := by
    simp [hc]
    rw [map_ofNat]
    norm_num
  have key : vInv W wq * (-(2 : PowerSeries ℂ_[p]) * wq - PowerSeries.X * dX wq) =
      wq * (algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₁ * PowerSeries.X +
      algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₃ * PowerSeries.X ^ 3 * wq - 2) := by
    rw [dX_eq_derivative]
    simp only [vInv]
    linear_combination (-(PowerSeries.X : PowerSeries ℂ_[p])) * hd
  simp only [omegaW]
  rw [← mul_assoc, key, PowerSeries.mul_inv_cancel _ hden]

theorem vInv_mem {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]}
    (h1 : IsIntP W.a₁) (h2 : IsIntP W.a₂) (h3 : IsIntP W.a₃) (h4 : IsIntP W.a₄) (h6 : IsIntP W.a₆)
    (h : IsWq W wq) : vInv W wq ∈ serS (intS p) := by
  have hw : wq ∈ serS (intS p) := wq_mem (S := intS p) h1 h2 h3 h4 h6 h
  have hX := X_mem_serS (intS p)
  have c1 := C_mem_serS (S := intS p) h1
  have c2 := C_mem_serS (S := intS p) h2
  have c3 := C_mem_serS (S := intS p) h3
  have c4 := C_mem_serS (S := intS p) h4
  have c6 := C_mem_serS (S := intS p) h6
  have t2 : (2 : PowerSeries ℂ_[p]) ∈ serS (intS p) := by
    exact_mod_cast natCast_mem (serS (intS p)) 2
  have t3 : (3 : PowerSeries ℂ_[p]) ∈ serS (intS p) := by
    exact_mod_cast natCast_mem (serS (intS p)) 3
  have hw3 : PowerSeries.X ^ 3 * wq ∈ serS (intS p) := Subring.mul_mem _ (Subring.pow_mem _ hX 3) hw
  simp only [vInv]
  refine Subring.sub_mem _ (Subring.one_mem _) ?_
  refine Subring.add_mem _ (Subring.add_mem _ (Subring.add_mem _ (Subring.add_mem _ ?_ ?_) ?_) ?_) ?_
  · exact Subring.mul_mem _ c1 hX
  · exact Subring.mul_mem _ c2 (Subring.pow_mem _ hX 2)
  · exact Subring.mul_mem _ (Subring.mul_mem _ t2 c3) hw3
  · exact Subring.mul_mem _ (Subring.mul_mem _ (Subring.mul_mem _ t2 c4) hX) hw3
  · exact Subring.mul_mem _ (Subring.mul_mem _ t3 c6) (Subring.pow_mem _ hw3 2)

theorem inverse_omega_holds : InvOmega :=
  _root_.UpperTheory.Reformulated.B.Gwa1.inverse_omega_holds

end PI.JetsPhW.Inv
