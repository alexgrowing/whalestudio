import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.WittLift

variable (l : ℕ) [hl : Fact l.Prime] {C : Type} [CommRing C] (J : Ideal C)

theorem ghost_eq (n : ℕ) (x : _root_.WittVector l C) :
    _root_.WittVector.ghostComponent n x =
      ∑ i ∈ Finset.range (n + 1), (l : C) ^ i * x.coeff i ^ l ^ (n - i) := by
  rw [_root_.WittVector.ghostComponent_apply, aeval_wittPolynomial]

theorem ghost_mem_pow (hlJ : (l : C) ∈ J) (n : ℕ) (x : _root_.WittVector l C)
    (hx : ∀ i, x.coeff i ∈ J) : _root_.WittVector.ghostComponent n x ∈ J ^ n := by
  rw [ghost_eq]
  refine Ideal.sum_mem _ fun i _ => ?_
  have h1 : (l : C) ^ i ∈ J ^ i := Ideal.pow_mem_pow hlJ i
  have h2 : x.coeff i ^ l ^ (n - i) ∈ J ^ (l ^ (n - i)) := Ideal.pow_mem_pow (hx i) _
  have h3 : (l : C) ^ i * x.coeff i ^ l ^ (n - i) ∈ J ^ (i + l ^ (n - i)) := by
    rw [pow_add]; exact Ideal.mul_mem_mul h1 h2
  refine Ideal.pow_le_pow_right ?_ h3
  have : n - i < l ^ (n - i) := Nat.lt_pow_self hl.out.one_lt
  omega

def liftW (y : _root_.WittVector l (C ⧸ J)) : _root_.WittVector l C :=
  _root_.WittVector.mk l (fun i => Function.surjInv Ideal.Quotient.mk_surjective (y.coeff i))

theorem map_liftW (y : _root_.WittVector l (C ⧸ J)) :
    _root_.WittVector.map (Ideal.Quotient.mk J) (liftW l J y) = y := by
  ext i
  rw [_root_.WittVector.map_coeff]
  simp only [liftW, _root_.WittVector.coeff_mk]
  exact Function.surjInv_eq Ideal.Quotient.mk_surjective _

def gh (hlJ : (l : C) ∈ J) (n : ℕ) : _root_.WittVector l (C ⧸ J) →+* C ⧸ J ^ n :=
  RingHom.liftOfRightInverse (_root_.WittVector.map (Ideal.Quotient.mk J)) (liftW l J) (map_liftW l J)
    ⟨(Ideal.Quotient.mk (J ^ n)).comp (_root_.WittVector.ghostComponent n), fun x hx => by
      rw [RingHom.mem_ker] at hx ⊢
      rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
      refine ghost_mem_pow l J hlJ n x fun i => ?_
      rw [← Ideal.Quotient.eq_zero_iff_mem, ← _root_.WittVector.map_coeff, hx,
        _root_.WittVector.zero_coeff]⟩

theorem gh_map (hlJ : (l : C) ∈ J) (n : ℕ) (x : _root_.WittVector l C) :
    gh l J hlJ n (_root_.WittVector.map (Ideal.Quotient.mk J) x) =
      Ideal.Quotient.mk (J ^ n) (_root_.WittVector.ghostComponent n x) :=
  RingHom.liftOfRightInverse_comp_apply _ _ _ _ x

end GlobalTheory.WittLift

namespace GlobalTheory.WittLift

variable (l : ℕ) [hl : Fact l.Prime] {C : Type} [CommRing C] (J : Ideal C)
variable (k : Type) [CommRing k] [CharP k l] [PerfectRing k l]

theorem symm_iter_pow (n : ℕ) (x : k) :
    (iterateFrobeniusEquiv k l (n + 1)).symm x ^ l = (iterateFrobeniusEquiv k l n).symm x := by
  apply (iterateFrobeniusEquiv k l n).injective
  rw [RingEquiv.apply_symm_apply, iterateFrobeniusEquiv_def, ← pow_mul, ← pow_succ',
    ← iterateFrobeniusEquiv_def k l (n + 1), RingEquiv.apply_symm_apply]

theorem symm_iter_zero (x : k) : (iterateFrobeniusEquiv k l 0).symm x = x := by
  apply (iterateFrobeniusEquiv k l 0).injective
  rw [RingEquiv.apply_symm_apply, iterateFrobeniusEquiv_zero_apply]

variable {k} (ψ : k →+* C ⧸ J)

def wn (n : ℕ) : _root_.WittVector l k →+* _root_.WittVector l (C ⧸ J) :=
  _root_.WittVector.map (ψ.comp (iterateFrobeniusEquiv k l n).symm.toRingHom)

def yh (n : ℕ) (w : _root_.WittVector l k) : _root_.WittVector l C := liftW l J (wn l J ψ n w)

theorem mk_yh_coeff (n : ℕ) (w : _root_.WittVector l k) (i : ℕ) :
    Ideal.Quotient.mk J ((yh l J ψ n w).coeff i) = ψ ((iterateFrobeniusEquiv k l n).symm (w.coeff i)) := by
  rw [← _root_.WittVector.map_coeff, yh, map_liftW, wn, _root_.WittVector.map_coeff]
  rfl

def fn (hlJ : (l : C) ∈ J) (n : ℕ) : _root_.WittVector l k →+* C ⧸ J ^ n :=
  (gh l J hlJ n).comp (wn l J ψ n)

theorem fn_apply (hlJ : (l : C) ∈ J) (n : ℕ) (w : _root_.WittVector l k) :
    fn l J ψ hlJ n w = Ideal.Quotient.mk (J ^ n) (_root_.WittVector.ghostComponent n (yh l J ψ n w)) := by
  rw [fn, RingHom.comp_apply, ← gh_map l J hlJ n, yh, map_liftW]

theorem step (hlJ : (l : C) ∈ J) (n : ℕ) (w : _root_.WittVector l k) :
    _root_.WittVector.ghostComponent (n + 1) (yh l J ψ (n + 1) w) -
      _root_.WittVector.ghostComponent n (yh l J ψ n w) ∈ J ^ n := by
  set y := yh l J ψ (n + 1) w with hy
  let z : _root_.WittVector l C := _root_.WittVector.mk l (fun i => y.coeff i ^ l)
  have hz : _root_.WittVector.map (Ideal.Quotient.mk J) z = wn l J ψ n w := by
    ext i
    rw [_root_.WittVector.map_coeff, _root_.WittVector.coeff_mk, map_pow, hy, mk_yh_coeff, ← map_pow,
      symm_iter_pow, wn, _root_.WittVector.map_coeff]
    rfl
  have h1 : _root_.WittVector.ghostComponent n (yh l J ψ n w) - _root_.WittVector.ghostComponent n z ∈ J ^ n := by
    rw [← Ideal.Quotient.eq, ← fn_apply, ← gh_map l J hlJ, hz, fn, RingHom.comp_apply]
  have h2 : _root_.WittVector.ghostComponent (n + 1) y - _root_.WittVector.ghostComponent n z =
      (l : C) ^ (n + 1) * y.coeff (n + 1) := by
    have ha : _root_.WittVector.ghostComponent (n + 1) y =
        (∑ i ∈ Finset.range (n + 1), (l : C) ^ i * y.coeff i ^ l ^ (n + 1 - i)) +
          (l : C) ^ (n + 1) * y.coeff (n + 1) := by
      rw [ghost_eq, Finset.sum_range_succ, Nat.sub_self, pow_zero, pow_one]
    have hb : _root_.WittVector.ghostComponent n z =
        ∑ i ∈ Finset.range (n + 1), (l : C) ^ i * y.coeff i ^ l ^ (n + 1 - i) := by
      rw [ghost_eq]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi' := Finset.mem_range.mp hi
      simp only [z, _root_.WittVector.coeff_mk]
      rw [← pow_mul, ← pow_succ']
      congr 3
      omega
    rw [ha, hb]; ring
  have h3 : (l : C) ^ (n + 1) * y.coeff (n + 1) ∈ J ^ n :=
    Ideal.pow_le_pow_right (Nat.le_succ n) (Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hlJ _))
  rw [← h2] at h3
  have := Ideal.sub_mem _ h3 h1
  convert this using 1
  abel

theorem compat (hlJ : (l : C) ∈ J) (w : _root_.WittVector l k) {m n : ℕ} (hle : m ≤ n) :
    _root_.WittVector.ghostComponent n (yh l J ψ n w) -
      _root_.WittVector.ghostComponent m (yh l J ψ m w) ∈ J ^ m := by
  induction n, hle using Nat.le_induction with
  | base => rw [sub_self]; exact Ideal.zero_mem _
  | succ n hmn ih =>
    have := Ideal.add_mem _ (Ideal.pow_le_pow_right hmn (step l J ψ hlJ n w)) ih
    convert this using 1
    abel

end GlobalTheory.WittLift

namespace GlobalTheory.WittLift

variable (l : ℕ) [hl : Fact l.Prime] {C : Type} [CommRing C] (J : Ideal C)
variable {k : Type} [CommRing k] [CharP k l] [PerfectRing k l] (ψ : k →+* C ⧸ J)

theorem fn_compat (hlJ : (l : C) ∈ J) {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow J hle).comp (fn l J ψ hlJ n) = fn l J ψ hlJ m := by
  refine RingHom.ext fun w => ?_
  rw [RingHom.comp_apply, fn_apply, fn_apply, Ideal.Quotient.factor_mk, Ideal.Quotient.eq]
  exact compat l J ψ hlJ w hle

end GlobalTheory.WittLift

namespace GlobalTheory

theorem exists_wittVector_lift_of_isAdicComplete :
    ∀ (l : ℕ) [Fact l.Prime] (k : Type) [CommRing k] [CharP k l] [PerfectRing k l] (C : Type) [CommRing C]
      (J : Ideal C), (l : C) ∈ J → IsAdicComplete J C → ∀ ψ : k →+* C ⧸ J,
      ∃ ω : WittVector l k →+* C, ∀ w, Ideal.Quotient.mk J (ω w) = ψ (w.coeff 0) := by
  intro l _ k _ _ _ C _ J hlJ hC ψ
  haveI := hC
  refine ⟨IsAdicComplete.liftRingHom J (WittLift.fn l J ψ hlJ) (WittLift.fn_compat l J ψ hlJ), fun w => ?_⟩
  have h0 : Ideal.Quotient.mk (J ^ 1)
      (IsAdicComplete.liftRingHom J (WittLift.fn l J ψ hlJ) (WittLift.fn_compat l J ψ hlJ) w) =
      Ideal.Quotient.mk (J ^ 1) (_root_.WittVector.ghostComponent 1 (WittLift.yh l J ψ 1 w)) := by
    rw [IsAdicComplete.mk_liftRingHom, WittLift.fn_apply]
  have h1 := Ideal.Quotient.eq.mp h0
  rw [pow_one] at h1
  rw [Ideal.Quotient.eq.mpr h1, WittLift.ghost_eq, Finset.sum_range_succ, Finset.sum_range_one]
  simp only [pow_zero, one_mul, Nat.sub_zero, pow_one, Nat.sub_self, map_add, map_mul, map_pow]
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hlJ, zero_mul, add_zero, WittLift.mk_yh_coeff, ← map_pow,
    WittLift.symm_iter_pow, WittLift.symm_iter_zero]

end GlobalTheory
