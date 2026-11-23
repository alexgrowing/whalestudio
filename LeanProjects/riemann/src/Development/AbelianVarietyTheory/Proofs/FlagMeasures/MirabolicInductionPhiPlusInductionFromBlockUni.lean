import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsMirClass

noncomputable section

namespace GlobalTheory.GLm.Stages

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

theorem sum_fibres {G G' : Type} [Group G] [Group G'] [Fintype G] [Fintype G'] (f : G →* G')
    (hf : Function.Surjective f) :
    ∃ N : ℕ, N ≠ 0 ∧ ∀ h : G' → ℂ, ∑ p, h (f p) = (N : ℂ) * ∑ y, h y := by
  refine ⟨(Finset.univ.filter fun p => f p = 1).card, ?_, fun h => ?_⟩
  · exact Finset.card_ne_zero.2 ⟨1, by simp⟩
  · rw [Finset.sum_comp h f, Finset.image_univ_of_surjective hf, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [nsmul_eq_mul]
    congr 2
    exact MonoidHom.card_fiber_eq_of_mem_range f (hf y) (hf 1)

theorem sum_fibres' {G G' : Type} [Group G] [Group G'] [Fintype G] [Fintype G'] (P : Subgroup G) (π : G → G')
    (hmul : ∀ a ∈ P, ∀ b ∈ P, π (a * b) = π a * π b) (hs : ∀ y, ∃ p ∈ P, π p = y) :
    ∃ N : ℕ, N ≠ 0 ∧ ∀ h : G' → ℂ, (∑ p, if p ∈ P then h (π p) else 0) = (N : ℂ) * ∑ y, h y := by
  let f : P →* G' := MonoidHom.mk' (fun p => π p) fun a b => hmul a a.2 b b.2
  obtain ⟨N, hN, h⟩ := sum_fibres f fun y => by
    obtain ⟨p, hp, e⟩ := hs y
    exact ⟨⟨p, hp⟩, e⟩
  refine ⟨N, hN, fun k => ?_⟩
  rw [← h k, ← Finset.sum_filter]
  exact Finset.sum_subtype _ (by simp) fun p => k (π p)

theorem stages {G G' : Type} [Group G] [Group G'] [Fintype G] [Fintype G'] (P : Subgroup G) (P' : Subgroup G')
    (π : G → G') (hmul : ∀ a ∈ P, ∀ b ∈ P, π (a * b) = π a * π b) (N : ℕ)
    (fib : ∀ h : G' → ℂ, (∑ p, if p ∈ P then h (π p) else 0) = (N : ℂ) * ∑ y, h y)
    (θ : G → ℂ) (hθ : ∀ q ∈ P, π q ∈ P' → ∀ z ∈ P, π z ∈ P' → θ (q⁻¹ * z * q) = θ z)
    (F : G → ℂ) (F' : G' → ℂ) (hF : ∀ w ∈ P, F w = if π w ∈ P' then F' (π w) * θ w else 0)
    (x : G) (hx : x ∈ P) :
    ((Finset.univ.filter fun p => p ∈ P ∧ π p ∈ P').card : ℂ) * (∑ y, if y ∈ P then F (y⁻¹ * x * y) else 0) =
      N * ∑ y, if y ∈ P ∧ π (y⁻¹ * x * y) ∈ P' then
        (∑ y', if y' ∈ P' then F' (y'⁻¹ * π (y⁻¹ * x * y) * y') else 0) * θ (y⁻¹ * x * y) else 0 := by
  have h1 : π 1 = 1 := by
    have := hmul 1 P.one_mem 1 P.one_mem
    simpa using this
  have hinv : ∀ q ∈ P, π q⁻¹ = (π q)⁻¹ := fun q hq => by
    rw [eq_inv_iff_mul_eq_one, ← hmul _ (P.inv_mem hq) _ hq, inv_mul_cancel, h1]
  have hconj : ∀ q ∈ P, ∀ z ∈ P, π (q⁻¹ * z * q) = (π q)⁻¹ * π z * π q := fun q hq z hz => by
    rw [hmul _ (P.mul_mem (P.inv_mem hq) hz) _ hq, hmul _ (P.inv_mem hq) _ hz, hinv q hq]
  have shift : ∀ q ∈ P, (∑ y, if y ∈ P then F (y⁻¹ * x * y) else 0) =
      ∑ y, if y ∈ P then F (q⁻¹ * (y⁻¹ * x * y) * q) else 0 := fun q hq => by
    rw [← Equiv.sum_comp (Equiv.mulRight q)]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp only [Equiv.coe_mulRight, P.mul_mem_cancel_right hq, mul_inv_rev, mul_assoc]
  rw [← nsmul_eq_mul, ← Finset.sum_const,
    Finset.sum_congr rfl fun q hq => shift q (Finset.mem_filter.1 hq).2.1, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  by_cases hy : y ∈ P
  · have hz : y⁻¹ * x * y ∈ P := P.mul_mem (P.mul_mem (P.inv_mem hy) hx) hy
    generalize y⁻¹ * x * y = z at hz
    simp only [hy, if_true, true_and]
    have hw : ∀ q ∈ P, q⁻¹ * z * q ∈ P := fun q hq => P.mul_mem (P.mul_mem (P.inv_mem hq) hz) hq
    by_cases hz' : π z ∈ P'
    · rw [if_pos hz', ← mul_assoc, ← fib, Finset.sum_filter, Finset.sum_mul]
      refine Finset.sum_congr rfl fun q _ => ?_
      by_cases hq : q ∈ P
      · by_cases hq' : π q ∈ P'
        · simp only [hq, hq', if_true, and_self]
          rw [hF _ (hw q hq), hconj q hq z hz, if_pos (P'.mul_mem (P'.mul_mem (P'.inv_mem hq') hz') hq'),
            hθ q hq hq' z hz hz']
        · simp [hq, hq']
      · simp [hq]
    · rw [if_neg hz', mul_zero]
      refine Finset.sum_eq_zero fun q hq => ?_
      obtain ⟨hq, hq'⟩ := (Finset.mem_filter.1 hq).2
      rw [hF _ (hw q hq), hconj q hq z hz, if_neg]
      rw [P'.mul_mem_cancel_right hq', P'.mul_mem_cancel_left (P'.inv_mem hq')]
      exact hz'
  · simp [hy]

variable {g : ℕ} [Fact g.Prime]

theorem mir_mul_apply {n : ℕ} {A : Mt g n} (hA : InMir A) (B : Mt g n) (i j : Fin n) (hi : (i : ℕ) + 1 = n) :
    (A * B) i j = B i j := by
  rw [Matrix.mul_apply, Finset.sum_congr rfl fun k _ => by rw [hA i k hi], ← Matrix.mul_apply, one_mul]

def mir (g n : ℕ) [Fact g.Prime] : Subgroup (Gn g n) where
  carrier := {p | InMir (p : Mt g n)}
  one_mem' := inMir_one n
  mul_mem' := fun {a b} ha hb i j hi => by
    rw [Units.val_mul, mir_mul_apply ha _ i j hi]; exact hb i j hi
  inv_mem' := fun {a} ha i j hi => by
    rw [← mir_mul_apply ha ((a⁻¹ : Gn g n) : Mt g n) i j hi, Units.mul_inv]

theorem mem_mir {n : ℕ} (p : Gn g n) : p ∈ mir g n ↔ InMir (p : Mt g n) := Iff.rfl

theorem tl_apply {m : ℕ} (A : Mt g (m + 1)) (i j : Fin m) : tl m A i j = A i.castSucc j.castSucc := by
  have h1 : (i : ℕ) < m + 1 := by omega
  have h2 : (j : ℕ) < m + 1 := by omega
  simp only [tl, entN, h1, h2, and_self, dif_pos]
  rfl

theorem tl_mul {m : ℕ} (A : Mt g (m + 1)) {B : Mt g (m + 1)} (hB : InMir B) : tl m (A * B) = tl m A * tl m B := by
  ext i j
  rw [tl_apply, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_castSucc, hB (Fin.last m) _ rfl,
    Matrix.one_apply_ne (Fin.castSucc_lt_last j).ne']
  simp [tl_apply]

theorem tl_one {m : ℕ} : tl m (1 : Mt g (m + 1)) = 1 := by
  ext i j
  simp [tl_apply, Matrix.one_apply]

theorem coe_toG {n : ℕ} {M : Mt g n} (h : IsUnit M) : ((toG M : Gn g n) : Mt g n) = M := by
  unfold toG; rw [dif_pos h]; rfl

theorem coe_toG_tl {m : ℕ} {w : Gn g (m + 1)} (hw : w ∈ mir g (m + 1)) :
    ((toG (tl m (w : Mt g (m + 1))) : Gn g m) : Mt g m) = tl m (w : Mt g (m + 1)) := by
  refine coe_toG (IsUnit.of_mul_eq_one (tl m ((w⁻¹ : Gn g (m + 1)) : Mt g (m + 1))) ?_)
  rw [← tl_mul _ ((mir g (m + 1)).inv_mem hw), Units.mul_inv, tl_one]

theorem toG_tl_mul {m : ℕ} (a : Gn g (m + 1)) (ha : a ∈ mir g (m + 1)) (b : Gn g (m + 1))
    (hb : b ∈ mir g (m + 1)) :
    toG (tl m ((a * b : Gn g (m + 1)) : Mt g (m + 1))) =
      toG (tl m (a : Mt g (m + 1))) * toG (tl m (b : Mt g (m + 1))) := by
  apply Units.ext
  rw [coe_toG_tl ((mir g (m + 1)).mul_mem ha hb), Units.val_mul (toG _), coe_toG_tl ha, coe_toG_tl hb, Units.val_mul,
    tl_mul _ hb]

def ext1 {m : ℕ} (M : Mt g m) : Mt g (m + 1) := fun i j =>
  Fin.lastCases (Fin.lastCases 1 (fun _ => 0) j) (fun i' => Fin.lastCases 0 (fun j' => M i' j') j) i

theorem extendMatrixByIdentityAlongIndices_mul {m : ℕ} (M N : Mt g m) : ext1 M * ext1 N = ext1 (M * N) := by
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;> simp [ext1, Matrix.mul_apply]

theorem blockDiagonalExtendByOnePrimeField_one {m : ℕ} : ext1 (1 : Mt g m) = 1 := by
  ext i j
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
    simp [ext1, Matrix.one_apply, (Fin.castSucc_lt_last _).ne, (Fin.castSucc_lt_last _).ne']

theorem toG_tl_surj {m : ℕ} (y : Gn g m) : ∃ p ∈ mir g (m + 1), toG (tl m (p : Mt g (m + 1))) = y := by
  let p : Gn g (m + 1) := ⟨ext1 (y : Mt g m), ext1 ((y⁻¹ : Gn g m) : Mt g m),
    by rw [extendMatrixByIdentityAlongIndices_mul, Units.mul_inv, blockDiagonalExtendByOnePrimeField_one], by rw [extendMatrixByIdentityAlongIndices_mul, Units.inv_mul, blockDiagonalExtendByOnePrimeField_one]⟩
  have hp : p ∈ mir g (m + 1) := by
    intro i j hi
    obtain rfl : i = Fin.last m := Fin.ext (by simpa using hi)
    induction j using Fin.lastCases <;> simp [p, ext1, Matrix.one_apply, (Fin.castSucc_lt_last _).ne']
  refine ⟨p, hp, Units.ext ?_⟩
  rw [coe_toG_tl hp]
  ext i j
  simp [tl_apply, p, ext1]

theorem corner_mul {m : ℕ} (hm : 0 < m) {A B : Mt g (m + 1)} (hA : InMir (tl m A)) (hB : InMir B) :
    entN (A * B) (m - 1) m = entN A (m - 1) m + entN B (m - 1) m := by
  have e : ∀ C : Mt g (m + 1), entN C (m - 1) m = C (Fin.castSucc ⟨m - 1, by omega⟩) (Fin.last m) := fun C => by
    have h1 : m - 1 < m + 1 := by omega
    simp only [entN, h1, Nat.lt_succ_self, and_self, dif_pos]
    rfl
  rw [e, e, e, Matrix.mul_apply, Fin.sum_univ_castSucc, hB (Fin.last m) _ rfl, Matrix.one_apply_eq, mul_one,
    add_comm]
  congr 1
  rw [Finset.sum_congr rfl fun k _ => by rw [← tl_apply A _ k, hA _ k (by simp; omega)]]
  simp [Matrix.one_apply]

theorem entN_tl {m n : ℕ} (A : Mt g n) {a b : ℕ} (ha : a < m) (hb : b < m) : entN (tl m A) a b = entN A a b := by
  simp [entN, ha, hb, tl]

theorem tl_tl {i m n : ℕ} (h : i ≤ m) (A : Mt g n) : tl i (tl m A) = tl i A := by
  ext a b
  exact entN_tl A (by omega) (by omega)

theorem supFrom_succ {i m : ℕ} (h : i < m) (A : Mt g (m + 1)) :
    supFrom i A = supFrom i (tl m A) + entN A (m - 1) m := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  simp only [supFrom, Nat.add_sub_cancel]
  rw [Finset.sum_Ico_succ_top (by omega)]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  have := (Finset.mem_Ico.1 hj).2
  rw [entN_tl A (by omega) (by omega)]

theorem inR_iff {i n : ℕ} (A : Mt g n) :
    InR i A ↔ ∀ a b : Fin n, i ≤ (a : ℕ) → (b : ℕ) ≤ a → A a b = (1 : Mt g n) a b := by
  constructor
  · intro hM a b ha hb
    by_cases hb' : (b : ℕ) < i
    · rw [hM.1 a b hb' ha, Matrix.one_apply_ne]
      intro e; subst e; omega
    · have h2 := hM.2 ⟨a - i, by omega⟩ ⟨b - i, by omega⟩
      have e : br i (n - i) A ⟨a - i, by omega⟩ ⟨b - i, by omega⟩ = A a b := by
        have h1 : i + (a - i) = a := by omega
        have h3 : i + (b - i) = b := by omega
        simp [br, entN, h1, h3]
      rw [e] at h2
      by_cases hab : a = b
      · subst hab; rw [h2.2 rfl]; simp
      · rw [Matrix.one_apply_ne hab]
        apply h2.1
        have : (a : ℕ) ≠ b := fun e => hab (Fin.ext e)
        simp only [Fin.lt_def]; omega
  · intro h
    refine ⟨fun a b hb ha => ?_, fun a b => ?_⟩
    · rw [h a b ha (by omega), Matrix.one_apply_ne]
      intro e; subst e; omega
    · have h1 : i + a < n := by omega
      have h2 : i + b < n := by omega
      have e : br i (n - i) A a b = A ⟨i + a, h1⟩ ⟨i + b, h2⟩ := by simp [br, entN, h1, h2]
      rw [e]
      constructor
      · intro hab
        rw [Fin.lt_def] at hab
        rw [h _ _ (by simp) (by simp; omega), Matrix.one_apply_ne]
        simp; omega
      · rintro rfl
        rw [h _ _ (by simp) (by simp), Matrix.one_apply_eq]

theorem inR_succ {i m : ℕ} {A : Mt g (m + 1)} (hA : InMir A) : InR i A ↔ InR i (tl m A) := by
  rw [inR_iff, inR_iff]
  constructor
  · intro h a b ha hb
    rw [tl_apply, h _ _ (by simpa) (by simpa)]
    simp [Matrix.one_apply]
  · intro h a b ha hb
    induction a using Fin.lastCases with
    | last => exact hA _ _ rfl
    | cast a =>
      induction b using Fin.lastCases with
      | last => simp at hb; omega
      | cast b =>
        rw [← tl_apply A a b, h _ _ (by simpa using ha) (by simpa using hb)]
        simp [Matrix.one_apply]

theorem inMir_of_inR {i n : ℕ} (h : i < n) {M : Mt g n} (hM : InR i M) : InMir M := fun a b ha =>
  (inR_iff M).1 hM a b (by omega) (by omega)

theorem corner_conj {m : ℕ} (hm : 0 < m) (q : Gn g (m + 1)) (hq : q ∈ mir g (m + 1))
    (hq' : toG (tl m (q : Mt g (m + 1))) ∈ mir g m) (z : Gn g (m + 1)) (hz : z ∈ mir g (m + 1))
    (hz' : toG (tl m (z : Mt g (m + 1))) ∈ mir g m) :
    entN ((q⁻¹ * z * q : Gn g (m + 1)) : Mt g (m + 1)) (m - 1) m = entN (z : Mt g (m + 1)) (m - 1) m := by
  have hw : q⁻¹ * z * q ∈ mir g (m + 1) := (mir g _).mul_mem ((mir g _).mul_mem ((mir g _).inv_mem hq) hz) hq
  rw [mem_mir, coe_toG_tl hq] at hq'
  rw [mem_mir, coe_toG_tl hz] at hz'
  have h1 := corner_mul hm hq' hw
  have h2 := corner_mul hm hz' hq
  have e : q * (q⁻¹ * z * q) = z * q := by group
  rw [← Units.val_mul, e, Units.val_mul, h2, add_comm] at h1
  exact (add_left_cancel h1).symm

end GlobalTheory.GLm.Stages

namespace GlobalTheory.GLm

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm.Stages
open scoped Classical

theorem indV_indR (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ) (i m : ℕ) (ρ : Gn g i → ℂ) (him : i < m)
    (x : Gn g (m + 1)) (hx : InMir (x : Mt g (m + 1))) :
    indV ψ m (indR ψ i m ρ) x = indR ψ i (m + 1) ρ x := by
  obtain ⟨N, hN, fib⟩ := sum_fibres' (mir g (m + 1)) (fun p => toG (tl m (p : Mt g (m + 1)))) toG_tl_mul
    toG_tl_surj
  have key := stages (mir g (m + 1)) (mir g m) (fun p => toG (tl m (p : Mt g (m + 1)))) toG_tl_mul N fib
    (fun w => ψ (entN (w : Mt g (m + 1)) (m - 1) m))
    (fun q hq hq' z hz hz' => congrArg ψ (corner_conj (by omega) q hq hq' z hz hz'))
    (fun w => if InR i (w : Mt g (m + 1)) then ρ (toG (tl i (w : Mt g (m + 1)))) * ψ (supFrom i (w : Mt g (m + 1)))
      else 0)
    (fun w => if InR i (w : Mt g m) then ρ (toG (tl i (w : Mt g m))) * ψ (supFrom i (w : Mt g m)) else 0)
    (fun w hw => by
      simp only [mem_mir (toG _), coe_toG_tl hw, ← inR_succ hw, tl_tl him.le]
      by_cases h : InR i (w : Mt g (m + 1))
      · rw [if_pos h, if_pos h, if_pos (inMir_of_inR him ((inR_succ hw).1 h)), supFrom_succ him,
          AddChar.map_add_eq_mul, mul_assoc]
      · simp [h]) x hx
  have hR := fib fun y => if InR i (y : Mt g m) then 1 else 0
  have hR' : ((Finset.univ.filter fun p : Gn g (m + 1) => InR i (p : Mt g (m + 1))).card : ℂ) =
      N * ((Finset.univ.filter fun p : Gn g m => InR i (p : Mt g m)).card : ℂ) := by
    rw [Finset.card_filter, Finset.card_filter]
    push_cast
    rw [← hR]
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases hp : p ∈ mir g (m + 1)
    · simp only [hp, if_true, coe_toG_tl hp, ← inR_succ hp]
    · rw [if_neg hp, if_neg fun h => hp (inMir_of_inR (by omega) h)]
  have hQ : (Finset.univ.filter fun p : Gn g (m + 1) =>
      p ∈ mir g (m + 1) ∧ toG (tl m (p : Mt g (m + 1))) ∈ mir g m) = Finset.univ.filter fun p : Gn g (m + 1) =>
      InMir (p : Mt g (m + 1)) ∧ InMir (tl m (p : Mt g (m + 1))) := by
    refine Finset.filter_congr fun p _ => and_congr_right fun hp => ?_
    rw [mem_mir, coe_toG_tl hp]
  have hQ0 : ((Finset.univ.filter fun p : Gn g (m + 1) =>
      InMir (p : Mt g (m + 1)) ∧ InMir (tl m (p : Mt g (m + 1)))).card : ℂ) ≠ 0 := by
    refine Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 ⟨1, Finset.mem_filter.2 ⟨Finset.mem_univ _, inMir_one _, ?_⟩⟩)
    rw [Units.val_one, tl_one]; exact inMir_one _
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN
  rw [hQ] at key
  have e1 : indR ψ i (m + 1) ρ x =
      ((Finset.univ.filter fun p : Gn g (m + 1) => InR i (p : Mt g (m + 1))).card : ℂ)⁻¹ *
      ∑ y : Gn g (m + 1), if y ∈ mir g (m + 1) then
        (if InR i ((y⁻¹ * x * y : Gn g (m + 1)) : Mt g (m + 1)) then
          ρ (toG (tl i ((y⁻¹ * x * y : Gn g (m + 1)) : Mt g (m + 1)))) *
            ψ (supFrom i ((y⁻¹ * x * y : Gn g (m + 1)) : Mt g (m + 1))) else 0) else 0 := by
    simp only [indR, ite_and, mem_mir]
  rw [e1, hR', (eq_inv_mul_iff_mul_eq₀ hQ0).2 key, mul_inv, mul_left_comm, mul_mul_mul_comm,
    inv_mul_cancel₀ hN', one_mul, Finset.mul_sum]
  unfold indV
  congr 1
  refine Finset.sum_congr rfl fun y _ => ?_
  by_cases hy : y ∈ mir g (m + 1)
  · have hz : y⁻¹ * x * y ∈ mir g (m + 1) := (mir g _).mul_mem ((mir g _).mul_mem ((mir g _).inv_mem hy) hx) hy
    generalize y⁻¹ * x * y = z at hz
    simp only [mem_mir (toG _), coe_toG_tl hz, hy, (mem_mir _).1 hy, (mem_mir _).1 hz, true_and]
    split_ifs
    · simp only [indR, ite_and, mem_mir, mul_assoc]
    · simp
  · have hy' : ¬ InMir (y : Mt g (m + 1)) := hy
    simp [hy, hy']

end GlobalTheory.GLm
