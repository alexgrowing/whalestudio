import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantCoeffNmul
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DefectComp

variable {R Q : Type} [CommRing R] [CommRing Q] [Algebra R Q] {d : ℕ}

set_option autoImplicit false in
open MvPowerSeries TensorProduct in
variable {R Q : Type} [CommRing R] [CommRing Q] [Algebra R Q] {d : ℕ} in
variable {S : Type} [CommRing S] in
private lemma nmul_zero (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) S) :
    _root_.GlobalTheory.QLog.nmul μ 0 = fun _ => 0 := rfl

set_option autoImplicit false in
open MvPowerSeries TensorProduct in
variable {R Q : Type} [CommRing R] [CommRing Q] [Algebra R Q] {d : ℕ} in
variable {S : Type} [CommRing S] in
private lemma nmul_succ_eq_op_X (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) S) (k : ℕ) :
    _root_.GlobalTheory.QLog.nmul μ (k + 1) =
      _root_.GlobalTheory.Katz.op μ (_root_.GlobalTheory.QLog.nmul μ k) (fun i => X i) := by
  rw [_root_.GlobalTheory.QLog.nmul, _root_.GlobalTheory.QLog.nmul, Function.iterate_succ_apply']

set_option autoImplicit false in
open MvPowerSeries TensorProduct in
variable {R Q : Type} [CommRing R] [CommRing Q] [Algebra R Q] {d : ℕ} in
variable {S : Type} [CommRing S] in
private lemma hasSubst_sumElim_of_constantCoeff_eq_zero {τ : Type} {v w : Fin d → MvPowerSeries τ S}
    (hv : ∀ i, constantCoeff (v i) = 0) (hw : ∀ i, constantCoeff (w i) = 0) :
    HasSubst (Sum.elim v w) :=
  hasSubst_of_constantCoeff_zero fun s => by cases s <;> simp [hv, hw]

set_option autoImplicit false in
open MvPowerSeries TensorProduct in
variable {R Q : Type} [CommRing R] [CommRing Q] [Algebra R Q] {d : ℕ} in
variable {S : Type} [CommRing S] in
private lemma constantCoeff_katz_op_eq_zero {τ : Type} (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) S)
    (hμ : ∀ i, constantCoeff (μ i) = 0) {v w : Fin d → MvPowerSeries τ S}
    (hv : ∀ i, constantCoeff (v i) = 0) (hw : ∀ i, constantCoeff (w i) = 0) (i : Fin d) :
    constantCoeff (_root_.GlobalTheory.Katz.op μ v w i) = 0 :=
  constantCoeff_subst_eq_zero (hasSubst_sumElim_of_constantCoeff_eq_zero hv hw)
    (fun s => by cases s <;> simp [hv, hw]) (hμ i)

set_option autoImplicit false in
open MvPowerSeries TensorProduct in
variable {R Q : Type} [CommRing R] [CommRing Q] [Algebra R Q] {d : ℕ} in
variable {S : Type} [CommRing S] in
private lemma constantCoeff_nmul_eq_zero' (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) S)
    (hμ : ∀ i, constantCoeff (μ i) = 0) (k : ℕ) (i : Fin d) :
    constantCoeff (_root_.GlobalTheory.QLog.nmul μ k i) = 0 := by
  induction k generalizing i with
  | zero => simp [nmul_zero]
  | succ k ih =>
    rw [nmul_succ_eq_op_X]
    exact constantCoeff_katz_op_eq_zero μ hμ ih (fun j => constantCoeff_X j) i

set_option autoImplicit false in
open MvPowerSeries TensorProduct in
variable {R Q : Type} [CommRing R] [CommRing Q] [Algebra R Q] {d : ℕ} in
variable {S : Type} [CommRing S] in
private lemma mvPowerSeries_map_injective {σ A B : Type} [CommRing A] [CommRing B] {h : A →+* B}
    (hh : Function.Injective h) : Function.Injective (map (σ := σ) h) := fun p q hpq => by
  ext n
  apply hh
  simpa using congrArg (coeff n) hpq

set_option autoImplicit false in
open MvPowerSeries TensorProduct in
variable {R Q : Type} [CommRing R] [CommRing Q] [Algebra R Q] {d : ℕ} in
variable {S : Type} [CommRing S] in
private lemma subst_zero_divisor {σ τ : Type} {c : σ → MvPowerSeries τ S} (hc : HasSubst c) :
    subst c (0 : MvPowerSeries σ S) = 0 := by
  rw [← coe_substAlgHom hc, map_zero]

set_option autoImplicit false in
open MvPowerSeries TensorProduct in
variable {R Q : Type} [CommRing R] [CommRing Q] [Algebra R Q] {d : ℕ} in
variable {S : Type} [CommRing S] in
private lemma subst_subst_sumElim_eq_subst_sumElim_subst {τ υ : Type} {v w : Fin d → MvPowerSeries τ S}
    (hv : ∀ i, constantCoeff (v i) = 0) (hw : ∀ i, constantCoeff (w i) = 0)
    {c : τ → MvPowerSeries υ S} (hc : HasSubst c) (g : MvPowerSeries (Fin d ⊕ Fin d) S) :
    subst c (subst (Sum.elim v w) g) =
      subst (Sum.elim (fun j => subst c (v j)) (fun j => subst c (w j))) g := by
  rw [subst_comp_subst_apply (hasSubst_sumElim_of_constantCoeff_eq_zero hv hw) hc]
  congr 1
  funext s
  cases s <;> rfl

set_option autoImplicit false in
open MvPowerSeries TensorProduct in
variable {R Q : Type} [CommRing R] [CommRing Q] [Algebra R Q] {d : ℕ} in
variable {S : Type} [CommRing S] in
private lemma subst_katz_op_eq_op_subst {τ υ : Type} (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) S)
    {v w : Fin d → MvPowerSeries τ S}
    (hv : ∀ i, constantCoeff (v i) = 0) (hw : ∀ i, constantCoeff (w i) = 0)
    {c : τ → MvPowerSeries υ S} (hc : HasSubst c) (i : Fin d) :
    subst c (_root_.GlobalTheory.Katz.op μ v w i) =
      _root_.GlobalTheory.Katz.op μ (fun j => subst c (v j)) (fun j => subst c (w j)) i :=
  subst_subst_sumElim_eq_subst_sumElim_subst hv hw hc (μ i)

set_option autoImplicit false in
open MvPowerSeries TensorProduct in
variable {R Q : Type} [CommRing R] [CommRing Q] [Algebra R Q] {d : ℕ} in
variable {S : Type} [CommRing S] in
private lemma nmul_add_eq_op {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) S}
    (hG : _root_.GlobalTheory.Katz.IsLaw μ) (a b : ℕ) :
    _root_.GlobalTheory.QLog.nmul μ (a + b) =
      _root_.GlobalTheory.Katz.op μ (_root_.GlobalTheory.QLog.nmul μ a) (_root_.GlobalTheory.QLog.nmul μ b) := by
  have hμ := hG.const
  have hN := constantCoeff_nmul_eq_zero' μ hμ
  have ha : HasSubst (_root_.GlobalTheory.QLog.nmul μ a) := hasSubst_of_constantCoeff_zero (hN a)
  induction b with
  | zero =>
    funext i
    have h := congrArg (subst (_root_.GlobalTheory.QLog.nmul μ a))
      (congrFun hG.unit i)
    rw [subst_katz_op_eq_op_subst μ (fun j => constantCoeff_X j) (fun _ => by simp) ha] at h
    simp only [subst_X ha, subst_zero_divisor ha] at h
    rw [Nat.add_zero, nmul_zero]
    exact h.symm
  | succ b ih =>
    rw [← Nat.add_assoc, nmul_succ_eq_op_X, ih, nmul_succ_eq_op_X]
    funext i
    have hc : HasSubst (Sum.elim (_root_.GlobalTheory.QLog.nmul μ a)
        (Sum.elim (_root_.GlobalTheory.QLog.nmul μ b) fun j => (X j : MvPowerSeries (Fin d) S))) :=
      hasSubst_of_constantCoeff_zero fun s => by rcases s with s | s | s <;> simp [hN]
    have h := congrArg (subst (Sum.elim (_root_.GlobalTheory.QLog.nmul μ a)
        (Sum.elim (_root_.GlobalTheory.QLog.nmul μ b) fun j => (X j : MvPowerSeries (Fin d) S))))
      (congrFun hG.assoc i)
    have h1 : ∀ j, constantCoeff (_root_.GlobalTheory.Katz.x1 (R := S) (d := d) j) = 0 := fun j => by
      simp [_root_.GlobalTheory.Katz.x1]
    have h2 : ∀ j, constantCoeff (_root_.GlobalTheory.Katz.x2 (R := S) (d := d) j) = 0 := fun j => by
      simp [_root_.GlobalTheory.Katz.x2]
    have h3 : ∀ j, constantCoeff (_root_.GlobalTheory.Katz.x3 (R := S) (d := d) j) = 0 := fun j => by
      simp [_root_.GlobalTheory.Katz.x3]
    rw [subst_katz_op_eq_op_subst μ (constantCoeff_katz_op_eq_zero μ hμ h1 h2) h3 hc,
      subst_katz_op_eq_op_subst μ h1 (constantCoeff_katz_op_eq_zero μ hμ h2 h3) hc] at h
    simp_rw [subst_katz_op_eq_op_subst μ h1 h2 hc, subst_katz_op_eq_op_subst μ h2 h3 hc] at h
    simp only [_root_.GlobalTheory.Katz.x1, _root_.GlobalTheory.Katz.x2, _root_.GlobalTheory.Katz.x3,
      subst_X hc, Sum.elim_inl, Sum.elim_inr] at h
    exact h

set_option autoImplicit false in
open MvPowerSeries TensorProduct in
variable {R Q : Type} [CommRing R] [CommRing Q] [Algebra R Q] {d : ℕ} in
variable {S : Type} [CommRing S] in
private lemma subst_nmul_nmul_eq_nmul_mul {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) S}
    (hG : _root_.GlobalTheory.Katz.IsLaw μ) (k m : ℕ) (i : Fin d) :
    subst (_root_.GlobalTheory.QLog.nmul μ m) (_root_.GlobalTheory.QLog.nmul μ k i) =
      _root_.GlobalTheory.QLog.nmul μ (k * m) i := by
  have hμ := hG.const
  have hN := constantCoeff_nmul_eq_zero' μ hμ
  have hm : HasSubst (_root_.GlobalTheory.QLog.nmul μ m) := hasSubst_of_constantCoeff_zero (hN m)
  induction k generalizing i with
  | zero =>
    simp only [Nat.zero_mul, nmul_zero]
    exact subst_zero_divisor hm
  | succ k ih =>
    rw [nmul_succ_eq_op_X, subst_katz_op_eq_op_subst μ (hN k) (fun j => constantCoeff_X j) hm]
    simp_rw [ih, subst_X hm]
    rw [Nat.succ_mul, nmul_add_eq_op hG]

set_option autoImplicit false in
open MvPowerSeries TensorProduct in
variable {R Q : Type} [CommRing R] [CommRing Q] [Algebra R Q] {d : ℕ} in
variable {S : Type} [CommRing S] in

theorem _root_.GlobalTheory.DefectComp.main : ∀ (R Q : Type) [CommRing R] [CommRing Q] [Algebra R Q] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), _root_.GlobalTheory.Katz.IsLaw μ → Function.Injective (algebraMap R Q) → ∀ (f : MvPowerSeries (Fin d) Q), constantCoeff f = 0 → ∀ (k m : ℕ) (s t u : MvPowerSeries (Fin d) R), map (algebraMap R Q) s = _root_.GlobalTheory.QLog.defect μ k f → map (algebraMap R Q) t = _root_.GlobalTheory.QLog.defect μ m f → map (algebraMap R Q) u = _root_.GlobalTheory.QLog.defect μ (k * m) f → u = subst (_root_.GlobalTheory.QLog.nmul μ m) s + (k : R) • t := by
  intro R Q _ _ _ d μ hG hinj f _ k m s t u hs ht hu
  have hμ := hG.const
  have hm : HasSubst (_root_.GlobalTheory.QLog.nmul μ m) :=
    hasSubst_of_constantCoeff_zero (constantCoeff_nmul_eq_zero' μ hμ m)
  have hmQ := _root_.GlobalTheory.QLog.hasSubst_up_nmul (Q := Q) hμ m
  have hkQ := _root_.GlobalTheory.QLog.hasSubst_up_nmul (Q := Q) hμ k
  apply mvPowerSeries_map_injective hinj
  rw [map_add, map_subst hm, hs, hu, Nat.cast_smul_eq_nsmul, map_nsmul, ht]
  change _ = subst (_root_.GlobalTheory.QLog.up Q (_root_.GlobalTheory.QLog.nmul μ m))
    (_root_.GlobalTheory.QLog.defect μ k f) + _
  simp only [_root_.GlobalTheory.QLog.defect]
  rw [subst_sub hmQ, subst_smul hmQ, subst_comp_subst_apply hkQ hmQ]
  have hcomp : (fun i => subst (_root_.GlobalTheory.QLog.up Q (_root_.GlobalTheory.QLog.nmul μ m))
      (_root_.GlobalTheory.QLog.up Q (_root_.GlobalTheory.QLog.nmul μ k) i)) =
      _root_.GlobalTheory.QLog.up Q (_root_.GlobalTheory.QLog.nmul μ (k * m)) := by
    funext i
    change subst (fun j => map (algebraMap R Q) (_root_.GlobalTheory.QLog.nmul μ m j))
      (map (algebraMap R Q) (_root_.GlobalTheory.QLog.nmul μ k i)) =
        map (algebraMap R Q) (_root_.GlobalTheory.QLog.nmul μ (k * m) i)
    rw [← map_subst hm, subst_nmul_nmul_eq_nmul_mul hG]
  rw [hcomp, ← Nat.cast_smul_eq_nsmul Q, Nat.cast_mul, mul_smul, smul_sub]
  abel

end GlobalTheory.DefectComp
