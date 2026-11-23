import Formalism.LocalToGlobal.Columns.TwQCmp
import Formalism.LocalToGlobal.Columns.TwQThetaOpen

open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Col

open Formalism.UG

section Grp

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} {n : ℕ}

local notation "Kv" => v.adicCompletion F
local notation "Ov" => v.adicCompletionIntegers F

def qbInt (A : Matrix (Fin n) (Fin n) Kv) : Prop := ∀ i j, A i j ∈ Ov

def qbDiv (c : Kv) (A : Matrix (Fin n) (Fin n) Kv) : Prop := ∀ i j, ∃ z ∈ Ov, A i j = c * z

theorem qbInt_one : qbInt (1 : Matrix (Fin n) (Fin n) Kv) := fun i j => by
  rw [Matrix.one_apply]; split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem qbInt_mul {A B : Matrix (Fin n) (Fin n) Kv} (hA : qbInt A) (hB : qbInt B) : qbInt (A * B) := by
  intro i j
  rw [Matrix.mul_apply]
  exact sum_mem fun k _ => mul_mem (hA i k) (hB k j)

theorem qbDiv_zero (c : Kv) : qbDiv c (0 : Matrix (Fin n) (Fin n) Kv) := fun _ _ => ⟨0, zero_mem _, by simp⟩

theorem qbDiv_add {c : Kv} {A B : Matrix (Fin n) (Fin n) Kv} (hA : qbDiv c A) (hB : qbDiv c B) : qbDiv c (A + B) := fun i j => by
  obtain ⟨z, hz, e⟩ := hA i j
  obtain ⟨z', hz', e'⟩ := hB i j
  exact ⟨z + z', Subring.add_mem _ hz hz', by rw [Matrix.add_apply, e, e', mul_add]⟩

theorem qbDiv_neg {c : Kv} {A : Matrix (Fin n) (Fin n) Kv} (hA : qbDiv c A) : qbDiv c (-A) := fun i j => by
  obtain ⟨z, hz, e⟩ := hA i j
  exact ⟨-z, Subring.neg_mem _ hz, by rw [Matrix.neg_apply, e, mul_neg]⟩

theorem qbDiv_mul_right {c : Kv} {A B : Matrix (Fin n) (Fin n) Kv} (hA : qbDiv c A) (hB : qbInt B) : qbDiv c (A * B) := fun i j => by
  choose z hz e using hA
  refine ⟨∑ l, z i l * B l j, Subring.sum_mem _ fun l _ => Subring.mul_mem _ (hz i l) (hB l j), ?_⟩
  rw [Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by rw [e i l, mul_assoc]

theorem qbDiv_mul_left {c : Kv} {A B : Matrix (Fin n) (Fin n) Kv} (hA : qbInt A) (hB : qbDiv c B) : qbDiv c (A * B) := by
  intro i j
  choose z hz he using hB
  refine ⟨∑ k, A i k * z k j, sum_mem fun k _ => mul_mem (hA i k) (hz k j), ?_⟩
  rw [Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [he k j, mul_left_comm]

def qbK (c : Kv) : Subgroup (GL (Fin n) Kv) where
  carrier := {k | qbInt (k : Matrix (Fin n) (Fin n) Kv) ∧ qbInt ((k⁻¹ : GL (Fin n) Kv) : Matrix (Fin n) (Fin n) Kv) ∧
    qbDiv c ((k : Matrix (Fin n) (Fin n) Kv) - 1)}
  mul_mem' := by
    rintro a b ⟨ha1, ha2, ha3⟩ ⟨hb1, hb2, hb3⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [Units.val_mul]; exact qbInt_mul ha1 hb1
    · rw [mul_inv_rev, Units.val_mul]; exact qbInt_mul hb2 ha2
    · have e : ((a * b : GL (Fin n) Kv) : Matrix (Fin n) (Fin n) Kv) - 1 =
          ((a : Matrix (Fin n) (Fin n) Kv) - 1) * (b : Matrix (Fin n) (Fin n) Kv) + ((b : Matrix (Fin n) (Fin n) Kv) - 1) := by
        rw [Units.val_mul]; noncomm_ring
      rw [e]
      exact qbDiv_add (qbDiv_mul_right ha3 hb1) hb3
  one_mem' := ⟨by rw [Units.val_one]; exact qbInt_one, by rw [inv_one, Units.val_one]; exact qbInt_one,
    by rw [Units.val_one, sub_self]; exact qbDiv_zero c⟩
  inv_mem' := by
    rintro a ⟨ha1, ha2, ha3⟩
    refine ⟨ha2, by rw [inv_inv]; exact ha1, ?_⟩
    have e : ((a⁻¹ : GL (Fin n) Kv) : Matrix (Fin n) (Fin n) Kv) - 1 =
        -(((a⁻¹ : GL (Fin n) Kv) : Matrix (Fin n) (Fin n) Kv) * ((a : Matrix (Fin n) (Fin n) Kv) - 1)) := by
      have hh : ((a⁻¹ : GL (Fin n) Kv) : Matrix (Fin n) (Fin n) Kv) * (a : Matrix (Fin n) (Fin n) Kv) = 1 := by
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
      rw [_root_.mul_sub, hh]; noncomm_ring
    rw [e]
    exact qbDiv_neg (qbDiv_mul_left ha2 ha3)

theorem mem_qbK {c : Kv} {k : GL (Fin n) Kv} : k ∈ qbK c ↔ qbInt (k : Matrix (Fin n) (Fin n) Kv) ∧
    qbInt ((k⁻¹ : GL (Fin n) Kv) : Matrix (Fin n) (Fin n) Kv) ∧ qbDiv c ((k : Matrix (Fin n) (Fin n) Kv) - 1) := Iff.rfl

theorem qbK_conj {c : Kv} {k h : GL (Fin n) Kv} (hk : k ∈ qbK c) (h1 : qbInt (h : Matrix (Fin n) (Fin n) Kv))
    (h2 : qbInt ((h⁻¹ : GL (Fin n) Kv) : Matrix (Fin n) (Fin n) Kv)) : h⁻¹ * k * h ∈ qbK c := by
  obtain ⟨k1, k2, k3⟩ := hk
  refine ⟨?_, ?_, ?_⟩
  · rw [Units.val_mul, Units.val_mul]; exact qbInt_mul (qbInt_mul h2 k1) h1
  · rw [mul_inv_rev, mul_inv_rev, inv_inv, Units.val_mul, Units.val_mul]; exact qbInt_mul h2 (qbInt_mul k2 h1)
  · have e : ((h⁻¹ * k * h : GL (Fin n) Kv) : Matrix (Fin n) (Fin n) Kv) - 1 =
        ((h⁻¹ : GL (Fin n) Kv) : Matrix (Fin n) (Fin n) Kv) * ((k : Matrix (Fin n) (Fin n) Kv) - 1) * (h : Matrix (Fin n) (Fin n) Kv) := by
      have hh : ((h⁻¹ : GL (Fin n) Kv) : Matrix (Fin n) (Fin n) Kv) * (h : Matrix (Fin n) (Fin n) Kv) = 1 := by
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
      rw [Units.val_mul, Units.val_mul, _root_.mul_sub, _root_.sub_mul, _root_.mul_one, hh]
    rw [e]
    exact qbDiv_mul_right (qbDiv_mul_left h2 k3) h1

end Grp

end Formalism.L2.Col
