import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsMirClass
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BlockParabolicUnitriangularSubgroupsGLnPrimeFielStatement

noncomputable section

namespace GlobalTheory.GLm.ResInd

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

variable {g : ℕ} [Fact g.Prime]

theorem coe_toG {n : ℕ} {M : Mt g n} (h : IsUnit M) : ((toG M : Gn g n) : Mt g n) = M := by
  unfold toG
  rw [dif_pos h]
  rfl

theorem toG_coe {n : ℕ} (x : Gn g n) : toG (x : Mt g n) = x := by
  unfold toG
  rw [dif_pos x.isUnit]
  exact Units.ext rfl

theorem sum_par (a b n : ℕ) (hn : n = a + b) (Φ : Gn g a → Gn g b → ℂ) :
    (∑ x : Gn g n, if InPar a (x : Mt g n) then
      Φ (toG (tl a (x : Mt g n))) (toG (br a b (x : Mt g n))) else 0) =
      (g : ℂ) ^ (a * b) * ∑ h₁, ∑ h₂, Φ h₁ h₂ := by
  obtain ⟨-, -, hU, -, hcard, -⟩ := GlobalTheory.T.blockParabolic_unitriangular_subgroups_GLnPrimeField g a b n hn
  have key : ∀ x : Gn g n, (if InPar a (x : Mt g n) then
      Φ (toG (tl a (x : Mt g n))) (toG (br a b (x : Mt g n))) else 0) =
      ∑ h₁ : Gn g a, ∑ h₂ : Gn g b, if (InPar a (x : Mt g n) ∧ tl a (x : Mt g n) = (h₁ : Mt g a) ∧
        br a b (x : Mt g n) = (h₂ : Mt g b)) then Φ h₁ h₂ else 0 := by
    intro x
    by_cases hx : InPar a (x : Mt g n)
    · rw [if_pos hx]
      obtain ⟨u1, u2⟩ := hU x hx
      rw [Finset.sum_eq_single (toG (tl a (x : Mt g n)))]
      · rw [Finset.sum_eq_single (toG (br a b (x : Mt g n)))]
        · rw [if_pos ⟨hx, (coe_toG u1).symm, (coe_toG u2).symm⟩]
        · intro h₂ _ hne
          rw [if_neg]
          rintro ⟨-, -, hb⟩
          apply hne
          rw [hb, toG_coe]
        · intro hh; exact absurd (Finset.mem_univ _) hh
      · intro h₁ _ hne
        apply Finset.sum_eq_zero
        intro h₂ _
        rw [if_neg]
        rintro ⟨-, ht, -⟩
        apply hne
        rw [ht, toG_coe]
      · intro hh; exact absurd (Finset.mem_univ _) hh
    · rw [if_neg hx]
      symm
      apply Finset.sum_eq_zero
      intro h₁ _
      apply Finset.sum_eq_zero
      intro h₂ _
      rw [if_neg]
      rintro ⟨hp, -⟩
      exact hx hp
  rw [Finset.sum_congr rfl (fun x _ => key x)]
  conv_lhs => rw [Finset.sum_comm]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun h₁ _ => ?_
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun h₂ _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, hcard, nsmul_eq_mul]
  push_cast
  ring

theorem conj_par (a b n : ℕ) (hn : n = a + b) (p z : Gn g n) (hp : InPar a (p : Mt g n)) :
    (InPar a ((p⁻¹ * z * p : Gn g n) : Mt g n) ↔ InPar a (z : Mt g n)) ∧
    (InPar a (z : Mt g n) →
      toG (tl a ((p⁻¹ * z * p : Gn g n) : Mt g n)) =
        (toG (tl a (p : Mt g n)))⁻¹ * toG (tl a (z : Mt g n)) * toG (tl a (p : Mt g n)) ∧
      toG (br a b ((p⁻¹ * z * p : Gn g n) : Mt g n)) =
        (toG (br a b (p : Mt g n)))⁻¹ * toG (br a b (z : Mt g n)) * toG (br a b (p : Mt g n))) := by
  obtain ⟨⟨Q, hQ⟩, -, hU, hM, -, -⟩ := GlobalTheory.T.blockParabolic_unitriangular_subgroups_GLnPrimeField g a b n hn
  have hpQ : p ∈ Q := (hQ p).2 hp
  have hpi : InPar a ((p⁻¹ : Gn g n) : Mt g n) := (hQ _).1 (Q.inv_mem hpQ)
  have h1Q : InPar a (1 : Mt g n) := by
    have := (hQ 1).1 Q.one_mem
    rwa [Units.val_one] at this
  have hmem : InPar a ((p⁻¹ * z * p : Gn g n) : Mt g n) ↔ InPar a (z : Mt g n) := by
    rw [← hQ, ← hQ, Q.mul_mem_cancel_right hpQ, Q.mul_mem_cancel_left (Q.inv_mem hpQ)]
  refine ⟨hmem, fun hz => ?_⟩
  have hc : InPar a ((p⁻¹ * z : Gn g n) : Mt g n) := by
    have := Q.mul_mem (Q.inv_mem hpQ) ((hQ z).2 hz)
    exact (hQ _).1 this
  have e1 : ((p⁻¹ * z * p : Gn g n) : Mt g n) = ((p⁻¹ : Gn g n) : Mt g n) * (z : Mt g n) * (p : Mt g n) := by
    simp only [Units.val_mul]
  have e2 : ((p⁻¹ : Gn g n) : Mt g n) * (p : Mt g n) = 1 := Units.inv_mul p
  have hq := hU _ (hmem.2 hz)
  obtain ⟨hup, hup'⟩ := hU p hp
  obtain ⟨huz, huz'⟩ := hU z hz
  have hprod := hM _ _ hpi hp
  rw [e2] at hprod
  have hone := hM _ _ h1Q hp
  rw [one_mul] at hone
  have htl1 : tl a (1 : Mt g n) = 1 :=
    hup.mul_right_cancel (by rw [one_mul]; exact hone.1.symm)
  have hbr1 : br a b (1 : Mt g n) = 1 :=
    hup'.mul_right_cancel (by rw [one_mul]; exact hone.2.symm)
  have hinvt : tl a ((p⁻¹ : Gn g n) : Mt g n) = ((toG (tl a (p : Mt g n)))⁻¹ : Gn g a) := by
    calc tl a ((p⁻¹ : Gn g n) : Mt g n)
        = tl a ((p⁻¹ : Gn g n) : Mt g n) * (((toG (tl a (p : Mt g n)) : Gn g a) : Mt g a) *
            (((toG (tl a (p : Mt g n)))⁻¹ : Gn g a) : Mt g a)) := by rw [Units.mul_inv, mul_one]
      _ = _ := by rw [← mul_assoc, coe_toG hup, ← hprod.1, htl1, one_mul]
  have hinvb : br a b ((p⁻¹ : Gn g n) : Mt g n) = ((toG (br a b (p : Mt g n)))⁻¹ : Gn g b) := by
    calc br a b ((p⁻¹ : Gn g n) : Mt g n)
        = br a b ((p⁻¹ : Gn g n) : Mt g n) * (((toG (br a b (p : Mt g n)) : Gn g b) : Mt g b) *
            (((toG (br a b (p : Mt g n)))⁻¹ : Gn g b) : Mt g b)) := by rw [Units.mul_inv, mul_one]
      _ = _ := by rw [← mul_assoc, coe_toG hup', ← hprod.2, hbr1, one_mul]
  have hc2 := hM _ _ hc hp
  have hc1 := hM _ _ hpi hz
  have e3 : ((p⁻¹ * z : Gn g n) : Mt g n) = ((p⁻¹ : Gn g n) : Mt g n) * (z : Mt g n) := Units.val_mul _ _
  rw [e3] at hc2
  constructor
  · apply Units.ext
    rw [coe_toG hq.1, e1, hc2.1, hc1.1]
    simp only [Units.val_mul]
    rw [coe_toG huz, coe_toG hup, ← hinvt]
  · apply Units.ext
    rw [coe_toG hq.2, e1, hc2.2, hc1.2]
    simp only [Units.val_mul]
    rw [coe_toG huz', coe_toG hup', ← hinvb]

def fR (ψ : AddChar (ZMod g) ℂ) (i : ℕ) (ρ : Gn g i → ℂ) {n : ℕ} (z : Gn g n) : ℂ :=
  if InR i (z : Mt g n) then ρ (toG (tl i (z : Mt g n))) * ψ (supFrom i (z : Mt g n)) else 0

def fU (ψ : AddChar (ZMod g) ℂ) {n : ℕ} (z : Gn g n) : ℂ :=
  if IsUniUp (z : Mt g n) then ψ (∑ i ∈ Finset.range (n - 1), entN (z : Mt g n) i (i + 1)) else 0

theorem supFrom_eq (i n : ℕ) (M : Mt g n) :
    supFrom i M = ∑ j ∈ Finset.range (n - i - 1), entN (br i (n - i) M) j (j + 1) := by
  unfold supFrom
  rw [Finset.sum_Ico_eq_sum_range, show n - 1 - i = n - i - 1 by omega]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  have h1 : j < n - i := by omega
  have h2 : j + 1 < n - i := by omega
  rw [show entN (br i (n - i) M) j (j + 1) = br i (n - i) M ⟨j, h1⟩ ⟨j + 1, h2⟩ from dif_pos ⟨h1, h2⟩]
  simp only [br, Nat.add_assoc]

theorem fR_eq (ψ : AddChar (ZMod g) ℂ) (i n : ℕ) (hi : i ≤ n) (ρ : Gn g i → ℂ) (z : Gn g n) :
    fR ψ i ρ z = if InPar i (z : Mt g n) then
      ρ (toG (tl i (z : Mt g n))) * fU ψ (toG (br i (n - i) (z : Mt g n))) else 0 := by
  obtain ⟨-, -, hU, -, -, -⟩ := GlobalTheory.T.blockParabolic_unitriangular_subgroups_GLnPrimeField g i (n - i) n (by omega)
  unfold fR fU InR
  by_cases hp : InPar i (z : Mt g n)
  · rw [if_pos hp, coe_toG (hU z hp).2, supFrom_eq]
    by_cases hu : IsUniUp (br i (n - i) (z : Mt g n))
    · rw [if_pos ⟨hp, hu⟩, if_pos hu]
    · rw [if_neg (fun hh => hu hh.2), if_neg hu, mul_zero]
  · rw [if_neg (fun hh => hp hh.1), if_neg hp]

theorem sum_conj_fR (ψ : AddChar (ZMod g) ℂ) (i n : ℕ) (hi : i ≤ n) (ρ : Gn g i → ℂ) (hρ : IsClass ρ)
    (z : Gn g n) :
    (∑ p : Gn g n, if InPar i (p : Mt g n) then fR ψ i ρ (p⁻¹ * z * p) else 0) =
      (g : ℂ) ^ (i * (n - i)) * Fintype.card (Gn g i) * if InPar i (z : Mt g n) then
        ρ (toG (tl i (z : Mt g n))) *
          ∑ w : Gn g (n - i), fU ψ (w⁻¹ * toG (br i (n - i) (z : Mt g n)) * w) else 0 := by
  have hn : n = i + (n - i) := by omega
  have key : ∀ p : Gn g n, (if InPar i (p : Mt g n) then fR ψ i ρ (p⁻¹ * z * p) else 0) =
      if InPar i (p : Mt g n) then (if InPar i (z : Mt g n) then ρ (toG (tl i (z : Mt g n))) *
        fU ψ ((toG (br i (n - i) (p : Mt g n)))⁻¹ * toG (br i (n - i) (z : Mt g n)) *
          toG (br i (n - i) (p : Mt g n))) else 0) else 0 := by
    intro p
    by_cases hp : InPar i (p : Mt g n)
    · rw [if_pos hp, if_pos hp, fR_eq ψ i n hi]
      obtain ⟨hiff, hbl⟩ := conj_par i (n - i) n hn p z hp
      by_cases hz : InPar i (z : Mt g n)
      · obtain ⟨e1, e2⟩ := hbl hz
        rw [if_pos (hiff.2 hz), if_pos hz, e1, e2]
        congr 1
        have := hρ (toG (tl i (z : Mt g n))) (toG (tl i (p : Mt g n)))⁻¹
        rw [inv_inv] at this
        exact this
      · rw [if_neg (fun hh => hz (hiff.1 hh)), if_neg hz]
    · rw [if_neg hp, if_neg hp]
  rw [Finset.sum_congr rfl (fun p _ => key p), sum_par i (n - i) n hn (fun (_ : Gn g i) (h₂ : Gn g (n - i)) =>
    if InPar i (z : Mt g n) then ρ (toG (tl i (z : Mt g n))) *
      fU ψ (h₂⁻¹ * toG (br i (n - i) (z : Mt g n)) * h₂) else 0)]
  by_cases hz : InPar i (z : Mt g n)
  · simp only [if_pos hz, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  · simp only [if_neg hz, Finset.sum_const_zero, mul_zero]

theorem card_inR (i n : ℕ) (hi : i ≤ n) :
    ((Finset.univ.filter fun p : Gn g n => InR i (p : Mt g n)).card : ℂ) =
      (g : ℂ) ^ (i * (n - i)) * Fintype.card (Gn g i) *
        (Finset.univ.filter fun u : Gn g (n - i) => IsUniUp (u : Mt g (n - i))).card := by
  have hn : n = i + (n - i) := by omega
  obtain ⟨-, -, hU, -, -, -⟩ := GlobalTheory.T.blockParabolic_unitriangular_subgroups_GLnPrimeField g i (n - i) n hn
  have h := sum_par i (n - i) n hn (fun (_ : Gn g i) (h₂ : Gn g (n - i)) => if IsUniUp (h₂ : Mt g (n - i)) then (1 : ℂ) else 0)
  have e : (∑ x : Gn g n, if InR i (x : Mt g n) then (1 : ℂ) else 0) =
      ∑ x : Gn g n, if InPar i (x : Mt g n) then
        (if IsUniUp ((toG (br i (n - i) (x : Mt g n)) : Gn g (n - i)) : Mt g (n - i)) then (1 : ℂ) else 0)
        else 0 := by
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hp : InPar i (x : Mt g n)
    · rw [if_pos hp, coe_toG (hU x hp).2]
      unfold InR
      simp only [hp, true_and]
    · rw [if_neg hp]
      unfold InR
      simp only [hp, false_and, if_false]
  simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [e, h]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

theorem isUniUp_one (n : ℕ) : IsUniUp (1 : Mt g n) := by
  intro a b
  refine ⟨fun hab => Matrix.one_apply_ne (ne_of_lt hab).symm, fun hab => ?_⟩
  subst hab
  exact Matrix.one_apply_eq a

theorem stages (ψ : AddChar (ZMod g) ℂ) (i n : ℕ) (hi : i ≤ n) (ρ : Gn g i → ℂ) (hρ : IsClass ρ)
    (h : Gn g n) :
    ((Finset.univ.filter fun p : Gn g n => InR i (p : Mt g n)).card : ℂ)⁻¹ *
      ∑ y : Gn g n, fR ψ i ρ (y⁻¹ * h * y) = hc i (n - i) ρ (gg ψ (n - i)) n h := by
  have hP0 : ((Finset.univ.filter fun p : Gn g n => InPar i (p : Mt g n)).card : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    refine Finset.card_ne_zero_of_mem (a := 1) (Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩)
    rw [Units.val_one]
    intro a b hb ha
    exact Matrix.one_apply_ne (Fin.ne_of_val_ne (by omega))
  have hU0 : ((Finset.univ.filter fun u : Gn g (n - i) => IsUniUp (u : Mt g (n - i))).card : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    refine Finset.card_ne_zero_of_mem (a := 1) (Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩)
    rw [Units.val_one]
    exact isUniUp_one _
  have hg : (g : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : g.Prime).ne_zero
  have hGi : (Fintype.card (Gn g i) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hgg : ∀ x : Gn g (n - i), ∑ w : Gn g (n - i), fU ψ (w⁻¹ * x * w) =
      ((Finset.univ.filter fun u : Gn g (n - i) => IsUniUp (u : Mt g (n - i))).card : ℂ) *
        gg ψ (n - i) x := by
    intro x
    unfold gg fU
    rw [mul_inv_cancel_left₀ hU0]
  have e2 : ∀ p : Gn g n, ∑ y : Gn g n, fR ψ i ρ (y⁻¹ * h * y) =
      ∑ y : Gn g n, fR ψ i ρ (p⁻¹ * (y⁻¹ * h * y) * p) := by
    intro p
    exact (Fintype.sum_equiv (Equiv.mulRight p) (fun y => fR ψ i ρ (p⁻¹ * (y⁻¹ * h * y) * p))
      (fun y => fR ψ i ρ (y⁻¹ * h * y))
      (fun y => by simp only [Equiv.coe_mulRight, mul_inv_rev, mul_assoc])).symm
  have hmain : ((Finset.univ.filter fun p : Gn g n => InPar i (p : Mt g n)).card : ℂ) *
      ∑ y : Gn g n, fR ψ i ρ (y⁻¹ * h * y) =
      (g : ℂ) ^ (i * (n - i)) * Fintype.card (Gn g i) *
        ((Finset.univ.filter fun u : Gn g (n - i) => IsUniUp (u : Mt g (n - i))).card : ℂ) *
        ∑ y : Gn g n, if InPar i ((y⁻¹ * h * y : Gn g n) : Mt g n) then
          ρ (toG (tl i ((y⁻¹ * h * y : Gn g n) : Mt g n))) *
            gg ψ (n - i) (toG (br i (n - i) ((y⁻¹ * h * y : Gn g n) : Mt g n))) else 0 := by
    have e1 : ((Finset.univ.filter fun p : Gn g n => InPar i (p : Mt g n)).card : ℂ) *
        ∑ y : Gn g n, fR ψ i ρ (y⁻¹ * h * y) =
        ∑ p : Gn g n, if InPar i (p : Mt g n) then ∑ y : Gn g n, fR ψ i ρ (y⁻¹ * h * y) else 0 := by
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have e3 : ∀ p : Gn g n, (if InPar i (p : Mt g n) then ∑ y : Gn g n, fR ψ i ρ (y⁻¹ * h * y) else 0) =
        ∑ y : Gn g n, (if InPar i (p : Mt g n) then fR ψ i ρ (p⁻¹ * (y⁻¹ * h * y) * p) else 0) := by
      intro p
      by_cases hp : InPar i (p : Mt g n)
      · simp only [if_pos hp]
        exact e2 p
      · simp only [if_neg hp, Finset.sum_const_zero]
    rw [e1, Finset.sum_congr rfl (fun p _ => e3 p), Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [sum_conj_fR ψ i n hi ρ hρ (y⁻¹ * h * y)]
    by_cases hz : InPar i ((y⁻¹ * h * y : Gn g n) : Mt g n)
    · rw [if_pos hz, if_pos hz, hgg]
      ring
    · rw [if_neg hz, if_neg hz]
      ring
  have hK := card_inR (g := g) i n hi
  have hKne : (g : ℂ) ^ (i * (n - i)) * Fintype.card (Gn g i) *
      ((Finset.univ.filter fun u : Gn g (n - i) => IsUniUp (u : Mt g (n - i))).card : ℂ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero _ hg) hGi) hU0
  have hS : ∑ y : Gn g n, fR ψ i ρ (y⁻¹ * h * y) =
      ((Finset.univ.filter fun p : Gn g n => InPar i (p : Mt g n)).card : ℂ)⁻¹ *
        ((g : ℂ) ^ (i * (n - i)) * Fintype.card (Gn g i) *
        ((Finset.univ.filter fun u : Gn g (n - i) => IsUniUp (u : Mt g (n - i))).card : ℂ) *
        ∑ y : Gn g n, if InPar i ((y⁻¹ * h * y : Gn g n) : Mt g n) then
          ρ (toG (tl i ((y⁻¹ * h * y : Gn g n) : Mt g n))) *
            gg ψ (n - i) (toG (br i (n - i) ((y⁻¹ * h * y : Gn g n) : Mt g n))) else 0) := by
    rw [← hmain, inv_mul_cancel_left₀ hP0]
  have hal : ∀ K Q T : ℂ, K ≠ 0 → K⁻¹ * (Q⁻¹ * (K * T)) = Q⁻¹ * T := by
    intro K Q T hK0
    rw [mul_left_comm, inv_mul_cancel_left₀ hK0]
  rw [hS, hK, hal _ _ _ hKne]
  rfl

theorem entN_tl {k n : ℕ} (M : Mt g n) {a b : ℕ} (ha : a < k) (hb : b < k) :
    entN (tl k M) a b = entN M a b := by
  show (if hh : a < k ∧ b < k then tl k M ⟨a, hh.1⟩ ⟨b, hh.2⟩ else 0) = _
  rw [dif_pos ⟨ha, hb⟩]
  rfl

theorem tl_apply_succ {k : ℕ} (M : Mt g (k + 1)) (a b : Fin k) :
    tl k M a b = M a.castSucc b.castSucc := by
  show entN M a b = _
  rw [entN, dif_pos ⟨Nat.lt_succ_of_lt a.2, Nat.lt_succ_of_lt b.2⟩]
  rfl

theorem inMir_iff {k : ℕ} (M : Mt g (k + 1)) :
    InMir M ↔ (∀ b : Fin k, M (Fin.last k) b.castSucc = 0) ∧ M (Fin.last k) (Fin.last k) = 1 := by
  constructor
  · intro h
    refine ⟨fun b => ?_, ?_⟩
    · rw [h (Fin.last k) b.castSucc (by simp), Matrix.one_apply_ne (Fin.castSucc_lt_last b).ne']
    · rw [h (Fin.last k) (Fin.last k) (by simp), Matrix.one_apply_eq]
  · rintro ⟨h1, h2⟩ r c hr
    have hr' : r = Fin.last k := Fin.ext (by rw [Fin.val_last]; omega)
    subst hr'
    induction c using Fin.lastCases with
    | last => rw [h2, Matrix.one_apply_eq]
    | cast b => rw [h1 b, Matrix.one_apply_ne (Fin.castSucc_lt_last b).ne']

private theorem br_one_zero_zero_eq_last {k : ℕ} (M : Mt g (k + 1)) : br k 1 M 0 0 = M (Fin.last k) (Fin.last k) := by
  show entN M (k + ((0 : Fin 1) : ℕ)) (k + ((0 : Fin 1) : ℕ)) = _
  rw [entN, dif_pos ⟨by simp, by simp⟩]
  congr 1 <;> exact Fin.ext (by simp)

theorem inMir_iff' {k : ℕ} (M : Mt g (k + 1)) : InMir M ↔ InPar k M ∧ br k 1 M = 1 := by
  rw [inMir_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun r c hc hr => ?_, ?_⟩
    · have hr' : r = Fin.last k := Fin.ext (by rw [Fin.val_last]; omega)
      subst hr'
      exact h1 ⟨c, hc⟩
    · ext a b
      rw [Subsingleton.elim a 0, Subsingleton.elim b 0, br_one_zero_zero_eq_last, h2, Matrix.one_apply_eq]
  · rintro ⟨h1, h2⟩
    refine ⟨fun b => h1 _ _ (by simp) (by simp), ?_⟩
    have := congrFun (congrFun h2 0) 0
    rwa [br_one_zero_zero_eq_last, Matrix.one_apply_eq] at this

theorem sum_mir (k : ℕ) (f : Gn g k → ℂ) :
    (∑ x : Gn g (k + 1), if InMir (x : Mt g (k + 1)) then f (toG (tl k (x : Mt g (k + 1)))) else 0) =
      (g : ℂ) ^ k * ∑ h, f h := by
  obtain ⟨-, -, hU, -, -, -⟩ := GlobalTheory.T.blockParabolic_unitriangular_subgroups_GLnPrimeField g k 1 (k + 1) rfl
  have h := sum_par k 1 (k + 1) rfl (fun (h₁ : Gn g k) (h₂ : Gn g 1) => if (h₂ : Mt g 1) = 1 then f h₁ else 0)
  have e : ∀ x : Gn g (k + 1), (if InMir (x : Mt g (k + 1)) then f (toG (tl k (x : Mt g (k + 1)))) else 0) =
      if InPar k (x : Mt g (k + 1)) then
        (if ((toG (br k 1 (x : Mt g (k + 1))) : Gn g 1) : Mt g 1) = 1 then f (toG (tl k (x : Mt g (k + 1))))
          else 0) else 0 := by
    intro x
    rw [inMir_iff']
    by_cases hp : InPar k (x : Mt g (k + 1))
    · rw [coe_toG (hU x hp).2]
      simp only [hp, true_and, if_true]
    · simp only [hp, false_and, if_false]
  rw [Finset.sum_congr rfl fun x _ => e x, h, mul_one]
  congr 1
  refine Finset.sum_congr rfl fun h₁ _ => ?_
  simp only [Units.val_eq_one, Finset.sum_ite_eq', Finset.mem_univ, if_true]

def dM {k : ℕ} (h : Mt g k) : Mt g (k + 1) := fun i j =>
  if (i : ℕ) < k ∧ (j : ℕ) < k then entN h i j else (1 : Mt g (k + 1)) i j

theorem dM_cc {k : ℕ} (h : Mt g k) (a b : Fin k) : dM h a.castSucc b.castSucc = h a b := by
  unfold dM
  rw [if_pos ⟨by simp, by simp⟩]
  simp [entN]

theorem dM_cl {k : ℕ} (h : Mt g k) (a : Fin k) : dM h a.castSucc (Fin.last k) = 0 := by
  unfold dM
  rw [if_neg (by simp), Matrix.one_apply_ne (Fin.castSucc_lt_last a).ne]

theorem dM_lc {k : ℕ} (h : Mt g k) (a : Fin k) : dM h (Fin.last k) a.castSucc = 0 := by
  unfold dM
  rw [if_neg (by simp), Matrix.one_apply_ne (Fin.castSucc_lt_last a).ne']

theorem dM_ll {k : ℕ} (h : Mt g k) : dM h (Fin.last k) (Fin.last k) = 1 := by
  unfold dM
  rw [if_neg (by simp), Matrix.one_apply_eq]

private theorem dM_mul_flag_measures {k : ℕ} (A B : Mt g k) : dM A * dM B = dM (A * B) := by
  ext r c
  induction r using Fin.lastCases with
  | last =>
    induction c using Fin.lastCases with
    | last => simp [Matrix.mul_apply, Fin.sum_univ_castSucc, dM_lc, dM_ll]
    | cast b => simp [Matrix.mul_apply, Fin.sum_univ_castSucc, dM_lc, dM_ll, dM_cl]
  | cast a =>
    induction c using Fin.lastCases with
    | last => simp [Matrix.mul_apply, Fin.sum_univ_castSucc, dM_cl, dM_ll, dM_cc]
    | cast b => simp [Matrix.mul_apply, Fin.sum_univ_castSucc, dM_cl, dM_lc, dM_cc]

private theorem dM_one_flag_measures {k : ℕ} : dM (1 : Mt g k) = 1 := by
  ext r c
  induction r using Fin.lastCases with
  | last =>
    induction c using Fin.lastCases with
    | last => rw [dM_ll, Matrix.one_apply_eq]
    | cast b => rw [dM_lc, Matrix.one_apply_ne (Fin.castSucc_lt_last b).ne']
  | cast a =>
    induction c using Fin.lastCases with
    | last => rw [dM_cl, Matrix.one_apply_ne (Fin.castSucc_lt_last a).ne]
    | cast b =>
      rw [dM_cc]
      by_cases hab : a = b
      · subst hab; simp
      · rw [Matrix.one_apply_ne hab, Matrix.one_apply_ne (fun e => hab (Fin.castSucc_injective _ e))]

theorem coe_diag1 {k : ℕ} (h : Gn g k) : (diag1 h (k + 1) : Mt g (k + 1)) = dM (h : Mt g k) := by
  have hu : IsUnit (dM (h : Mt g k)) :=
    ⟨⟨dM (h : Mt g k), dM ((h⁻¹ : Gn g k) : Mt g k),
      by rw [dM_mul_flag_measures, Units.mul_inv, dM_one_flag_measures],
      by rw [dM_mul_flag_measures, Units.inv_mul, dM_one_flag_measures]⟩, rfl⟩
  show ((toG (dM (h : Mt g k)) : Gn g (k + 1)) : Mt g (k + 1)) = dM (h : Mt g k)
  exact coe_toG hu

theorem inR_iff_ent {i n : ℕ} (M : Mt g n) :
    InR i M ↔ (∀ a b : ℕ, b < i → i ≤ a → entN M a b = 0) ∧
      ∀ a b : ℕ, i ≤ b → a < n → (b < a → entN M a b = 0) ∧ (a = b → entN M a b = 1) := by
  unfold InR
  constructor
  · rintro ⟨hP, hu⟩
    refine ⟨fun a b hb ha => ?_, fun a b hb ha => ⟨fun hba => ?_, fun hab => ?_⟩⟩
    · unfold entN
      split_ifs with hh
      · exact hP ⟨a, hh.1⟩ ⟨b, hh.2⟩ hb ha
      · rfl
    · have := (hu ⟨a - i, by omega⟩ ⟨b - i, by omega⟩).1 (by show b - i < a - i; omega)
      simp only [br, Fin.val_mk] at this
      rwa [show i + (a - i) = a by omega, show i + (b - i) = b by omega] at this
    · have := (hu ⟨a - i, by omega⟩ ⟨b - i, by omega⟩).2 (Fin.ext (by show a - i = b - i; omega))
      simp only [br, Fin.val_mk] at this
      rwa [show i + (a - i) = a by omega, show i + (b - i) = b by omega] at this
  · rintro ⟨hA, hB⟩
    refine ⟨fun r c hc hr => ?_, fun a b => ⟨fun hba => ?_, fun hab => ?_⟩⟩
    · have := hA r c hc hr
      rwa [entN, dif_pos ⟨r.2, c.2⟩] at this
    · have ha := a.isLt
      have hb := b.isLt
      rw [Fin.lt_iff_val_lt_val] at hba
      exact (hB (i + a) (i + b) (by omega) (by omega)).1 (by omega)
    · subst hab
      have ha := a.isLt
      exact (hB (i + a) (i + a) (by omega) (by omega)).2 rfl

theorem inMir_of_inR {i n : ℕ} (hi : i < n) {M : Mt g n} (h : InR i M) : InMir M := by
  rw [inR_iff_ent] at h
  intro r c hr
  have hM : M r c = entN M r c := by rw [entN, dif_pos ⟨r.2, c.2⟩]
  rw [hM]
  rcases lt_or_ge (c : ℕ) i with hc | hc
  · rw [h.1 r c hc (by omega), Matrix.one_apply_ne (Fin.ne_of_val_ne (by omega))]
  · rcases lt_or_eq_of_le (show (c : ℕ) ≤ r by omega) with hcr | hcr
    · rw [(h.2 r c hc r.2).1 hcr, Matrix.one_apply_ne (Fin.ne_of_val_ne (by omega))]
    · have e : c = r := Fin.ext hcr
      rw [e, Matrix.one_apply_eq]
      exact (h.2 r r (by omega) r.2).2 rfl

private theorem entN_tl' {k n : ℕ} (M : Mt g n) (a b : ℕ) :
    entN (tl k M) a b = if a < k ∧ b < k then entN M a b else 0 := by
  by_cases hh : a < k ∧ b < k
  · rw [if_pos hh, entN_tl M hh.1 hh.2]
  · rw [if_neg hh, entN, dif_neg hh]

private theorem entN_last_of_inMir {k : ℕ} {M : Mt g (k + 1)} (hM : InMir M) (b : ℕ) :
    entN M k b = if b = k then 1 else 0 := by
  unfold entN
  split_ifs with h1 h2 h2
  · rw [hM ⟨k, h1.1⟩ ⟨b, h1.2⟩ rfl, Matrix.one_apply, if_pos (Fin.ext h2.symm)]
  · rw [hM ⟨k, h1.1⟩ ⟨b, h1.2⟩ rfl, Matrix.one_apply_ne (Fin.ne_of_val_ne (by show k ≠ b; omega))]
  · exact absurd ⟨by omega, by omega⟩ h1
  · rfl

theorem inR_iff_tl {i k : ℕ} (hi : i ≤ k) {M : Mt g (k + 1)} (hM : InMir M) :
    InR i M ↔ InR i (tl k M) := by
  rw [inR_iff_ent, inR_iff_ent]
  simp only [entN_tl']
  constructor
  · rintro ⟨hA, hB⟩
    refine ⟨fun a b hb ha => ?_, fun a b hb ha => ⟨fun hba => ?_, fun hab => ?_⟩⟩
    · split_ifs
      · exact hA a b hb ha
      · rfl
    · rw [if_pos ⟨ha, by omega⟩]
      exact (hB a b hb (by omega)).1 hba
    · rw [if_pos ⟨ha, by omega⟩]
      exact (hB a b hb (by omega)).2 hab
  · rintro ⟨hA, hB⟩
    refine ⟨fun a b hb ha => ?_, fun a b hb ha => ?_⟩
    · rcases lt_trichotomy a k with hh | hh | hh
      · have := hA a b hb ha
        rwa [if_pos ⟨hh, by omega⟩] at this
      · subst hh
        rw [entN_last_of_inMir hM, if_neg (by omega)]
      · rw [entN, dif_neg (by omega)]
    · rcases lt_or_eq_of_le (Nat.lt_succ_iff.1 ha) with hh | hh
      · have h2 := hB a b hb hh
        refine ⟨fun hba => ?_, fun hab => ?_⟩
        · have := h2.1 hba
          rwa [if_pos ⟨hh, by omega⟩] at this
        · have := h2.2 hab
          rwa [if_pos ⟨hh, by omega⟩] at this
      · subst hh
        rw [entN_last_of_inMir hM]
        exact ⟨fun hba => if_neg (by omega), fun hab => if_pos hab.symm⟩

theorem tl_tl {i k n : ℕ} (hi : i ≤ k) (M : Mt g n) : tl i (tl k M) = tl i M := by
  ext a b
  exact entN_tl M (lt_of_lt_of_le a.2 hi) (lt_of_lt_of_le b.2 hi)

private theorem entN_eq_zero_of_mul_eq_of_inR {k i : ℕ} (hik : i < k) (X Yi Dm : Mt g (k + 1))
    (hXY : X * Yi = Yi * Dm) (hR : InR i X) (hYl : Yi (Fin.last k) (Fin.last k) = 1)
    (hD : ∀ c : Fin k, Dm c.castSucc (Fin.last k) = 0) (hDl : Dm (Fin.last k) (Fin.last k) = 1) :
    entN X (k - 1) k = 0 := by
  rw [inR_iff_ent] at hR
  have e := congrFun (congrFun hXY ⟨k - 1, by omega⟩) (Fin.last k)
  simp only [Matrix.mul_apply, Fin.sum_univ_castSucc, hD, hDl, hYl, mul_zero, Finset.sum_const_zero,
    zero_add, mul_one] at e
  have hrow : ∀ c : Fin k, X ⟨k - 1, by omega⟩ c.castSucc = if (c : ℕ) = k - 1 then 1 else 0 := by
    intro c
    have hc := c.isLt
    have hX : X ⟨k - 1, by omega⟩ c.castSucc = entN X (k - 1) c := by
      rw [entN, dif_pos ⟨by omega, by omega⟩]
      rfl
    rw [hX]
    split_ifs with hck
    · rw [hck]
      exact (hR.2 (k - 1) (k - 1) (by omega) (by omega)).2 rfl
    · rcases lt_or_ge (c : ℕ) i with hci | hci
      · exact hR.1 (k - 1) c hci (by omega)
      · exact (hR.2 (k - 1) c hci (by omega)).1 (by omega)
  simp only [hrow, ite_mul, one_mul, zero_mul] at e
  have hs : (∑ c : Fin k, if (c : ℕ) = k - 1 then Yi c.castSucc (Fin.last k) else 0) =
      Yi ⟨k - 1, by omega⟩ (Fin.last k) := by
    rw [Finset.sum_eq_single ⟨k - 1, by omega⟩]
    · rw [if_pos rfl]
      rfl
    · intro c _ hc
      rw [if_neg (fun hh => hc (Fin.ext hh))]
    · intro hh
      exact absurd (Finset.mem_univ _) hh
  rw [hs] at e
  rw [entN, dif_pos ⟨by omega, by omega⟩]
  show X ⟨k - 1, by omega⟩ (Fin.last k) = 0
  linear_combination e

theorem fR_conj_diag1 (ψ : AddChar (ZMod g) ℂ) (i k : ℕ) (hi : i ≤ k) (ρ : Gn g i → ℂ) (h : Gn g k)
    (y : Gn g (k + 1)) (hy : InMir (y : Mt g (k + 1))) :
    fR ψ i ρ (y⁻¹ * diag1 h (k + 1) * y) =
      fR ψ i ρ ((toG (tl k (y : Mt g (k + 1))))⁻¹ * h * toG (tl k (y : Mt g (k + 1)))) := by
  obtain ⟨-, -, hU, -, -, -⟩ := GlobalTheory.T.blockParabolic_unitriangular_subgroups_GLnPrimeField g k 1 (k + 1) rfl
  have hDm : InMir ((diag1 h (k + 1) : Gn g (k + 1)) : Mt g (k + 1)) := by
    rw [coe_diag1]
    exact (inMir_iff _).2 ⟨fun b => dM_lc _ b, dM_ll _⟩
  obtain ⟨hDP, hDb⟩ := (inMir_iff' _).1 hDm
  obtain ⟨hyP, hyb⟩ := (inMir_iff' _).1 hy
  obtain ⟨hiff, hbl⟩ := conj_par k 1 (k + 1) rfl y (diag1 h (k + 1)) hyP
  obtain ⟨htl, hbr⟩ := hbl hDP
  have hXP : InPar k ((y⁻¹ * diag1 h (k + 1) * y : Gn g (k + 1)) : Mt g (k + 1)) := hiff.2 hDP
  have htoG1 : toG (1 : Mt g 1) = 1 := by
    have := toG_coe (1 : Gn g 1)
    rwa [Units.val_one] at this
  have htlD : toG (tl k ((diag1 h (k + 1) : Gn g (k + 1)) : Mt g (k + 1))) = h := by
    have e : tl k (dM (h : Mt g k)) = (h : Mt g k) := by
      ext a b
      rw [tl_apply_succ, dM_cc]
    rw [coe_diag1, e, toG_coe]
  rw [hyb, hDb, htoG1, inv_one, one_mul, mul_one] at hbr
  have hXb : br k 1 ((y⁻¹ * diag1 h (k + 1) * y : Gn g (k + 1)) : Mt g (k + 1)) = 1 := by
    rw [← coe_toG (hU _ hXP).2, hbr, Units.val_one]
  have hXm : InMir ((y⁻¹ * diag1 h (k + 1) * y : Gn g (k + 1)) : Mt g (k + 1)) :=
    (inMir_iff' _).2 ⟨hXP, hXb⟩
  have hT : tl k ((y⁻¹ * diag1 h (k + 1) * y : Gn g (k + 1)) : Mt g (k + 1)) =
      (((toG (tl k (y : Mt g (k + 1))))⁻¹ * h * toG (tl k (y : Mt g (k + 1))) : Gn g k) : Mt g k) := by
    rw [← coe_toG (hU _ hXP).1, htl, htlD]
  have hyrow := (inMir_iff _).1 hy
  have hYl : ((y⁻¹ : Gn g (k + 1)) : Mt g (k + 1)) (Fin.last k) (Fin.last k) = 1 := by
    have e := congrFun (congrFun (Units.mul_inv y) (Fin.last k)) (Fin.last k)
    simp only [Matrix.mul_apply, Fin.sum_univ_castSucc, hyrow.1, hyrow.2, zero_mul,
      Finset.sum_const_zero, zero_add, one_mul, Matrix.one_apply_eq] at e
    exact e
  have hsup : InR i (((toG (tl k (y : Mt g (k + 1))))⁻¹ * h * toG (tl k (y : Mt g (k + 1))) : Gn g k) : Mt g k) →
      supFrom i ((y⁻¹ * diag1 h (k + 1) * y : Gn g (k + 1)) : Mt g (k + 1)) =
        supFrom i (((toG (tl k (y : Mt g (k + 1))))⁻¹ * h * toG (tl k (y : Mt g (k + 1))) : Gn g k) : Mt g k) := by
    intro hR
    have hRX : InR i ((y⁻¹ * diag1 h (k + 1) * y : Gn g (k + 1)) : Mt g (k + 1)) := by
      rw [inR_iff_tl hi hXm, hT]
      exact hR
    unfold supFrom
    rw [← hT]
    rcases Nat.lt_or_ge i k with hik | hik
    · have hz := entN_eq_zero_of_mul_eq_of_inR hik ((y⁻¹ * diag1 h (k + 1) * y : Gn g (k + 1)) : Mt g (k + 1))
        ((y⁻¹ : Gn g (k + 1)) : Mt g (k + 1)) ((diag1 h (k + 1) : Gn g (k + 1)) : Mt g (k + 1))
        (by simp only [Units.val_mul, mul_assoc, Units.mul_inv, mul_one]) hRX hYl
        (by intro c; rw [coe_diag1]; exact dM_cl _ c) (by rw [coe_diag1]; exact dM_ll _)
      obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
      rw [show m + 1 + 1 - 1 = m + 1 by omega, show m + 1 - 1 = m by omega,
        Finset.sum_Ico_succ_top (by omega : i ≤ m)]
      rw [show m + 1 - 1 = m by omega] at hz
      rw [hz, add_zero]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [Finset.mem_Ico] at hj
      exact (entN_tl _ (by omega) (by omega)).symm
    · rw [Finset.Ico_eq_empty_of_le (show k + 1 - 1 ≤ i by omega),
        Finset.Ico_eq_empty_of_le (show k - 1 ≤ i by omega), Finset.sum_empty, Finset.sum_empty]
  unfold fR
  rw [inR_iff_tl hi hXm, ← tl_tl hi ((y⁻¹ * diag1 h (k + 1) * y : Gn g (k + 1)) : Mt g (k + 1)), hT]
  split_ifs with hR
  · rw [hsup hR]
  · rfl

theorem card_inR_succ (i k : ℕ) (hi : i ≤ k) :
    ((Finset.univ.filter fun p : Gn g (k + 1) => InR i (p : Mt g (k + 1))).card : ℂ) =
      (g : ℂ) ^ k * (Finset.univ.filter fun p : Gn g k => InR i (p : Mt g k)).card := by
  obtain ⟨-, -, hU, -, -, -⟩ := GlobalTheory.T.blockParabolic_unitriangular_subgroups_GLnPrimeField g k 1 (k + 1) rfl
  have h := sum_mir k (fun t : Gn g k => if InR i (t : Mt g k) then (1 : ℂ) else 0)
  simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [← h]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hm : InMir (x : Mt g (k + 1))
  · rw [if_pos hm, coe_toG (hU x ((inMir_iff' _).1 hm).1).1, ← inR_iff_tl hi hm]
  · rw [if_neg hm, if_neg (fun hr => hm (inMir_of_inR (by omega) hr))]

end GlobalTheory.GLm.ResInd

namespace GlobalTheory.GLm

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm.ResInd
open scoped Classical

theorem indR_diag1_eq_hc_gg (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ) (i k : ℕ) (ρ : Gn g i → ℂ)
    (hi : i ≤ k) (hρ : IsClass ρ) (h : Gn g k) :
    indR ψ i (k + 1) ρ (diag1 h (k + 1)) = hc i (k - i) ρ (gg ψ (k - i)) k h := by
  have e1 : ∀ y : Gn g (k + 1), (if InMir (y : Mt g (k + 1)) ∧
      InR i ((y⁻¹ * diag1 h (k + 1) * y : Gn g (k + 1)) : Mt g (k + 1)) then
        ρ (toG (tl i ((y⁻¹ * diag1 h (k + 1) * y : Gn g (k + 1)) : Mt g (k + 1)))) *
          ψ (supFrom i ((y⁻¹ * diag1 h (k + 1) * y : Gn g (k + 1)) : Mt g (k + 1))) else 0) =
      if InMir (y : Mt g (k + 1)) then
        fR ψ i ρ ((toG (tl k (y : Mt g (k + 1))))⁻¹ * h * toG (tl k (y : Mt g (k + 1)))) else 0 := by
    intro y
    by_cases hy : InMir (y : Mt g (k + 1))
    · rw [if_pos hy, ← fR_conj_diag1 ψ i k hi ρ h y hy, fR]
      simp only [hy, true_and]
    · rw [if_neg hy, if_neg (fun hh => hy hh.1)]
  have hg : (g : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : g.Prime).ne_zero
  unfold indR
  rw [Finset.sum_congr rfl fun y _ => e1 y, sum_mir k (fun t => fR ψ i ρ (t⁻¹ * h * t)),
    card_inR_succ i k hi, ← stages ψ i k hi ρ hρ h, mul_inv_rev, mul_assoc,
    inv_mul_cancel_left₀ (pow_ne_zero _ hg)]

end GlobalTheory.GLm
