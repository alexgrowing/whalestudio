import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.DzFeCut
import Development.DiscreteGroups.GlobalIrreducibility.DzFeSv
import Development.DiscreteGroups.GlobalIrreducibility.DzFeOrth

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open GlobalTheory.GLq GlobalTheory.Whittaker GlobalTheory.SmGL Matrix
open scoped Classical

namespace DiscreteGroups.sglob.DzFe

variable {g : ℕ} [Fact g.Prime] {m : ℕ}

abbrev SIdx (m : ℕ) := {p : Fin (m + 1) × Fin (m + 1) // p.1 < p.2}

abbrev JIdx (m j : ℕ) := {i : Fin (m + 1) // (i : ℕ) ≤ j}

def Um (N : SIdx m → ZMod g) : Mt g (m + 1) :=
  Matrix.of fun i k => if i = k then 1 else if h : i < k then N ⟨(i, k), h⟩ else 0

theorem um_upper (N : SIdx m → ZMod g) : (Um N : Mt g (m + 1)).BlockTriangular id := by
  intro i k hik
  have hik' : k < i := hik
  simp [Um, ne_of_gt hik', not_lt_of_gt hik']

theorem det_um (N : SIdx m → ZMod g) : (Um N : Mt g (m + 1)).det = 1 := by
  rw [Matrix.det_of_upperTriangular (um_upper N)]
  simp [Um]

def umGL (N : SIdx m → ZMod g) : Gn g (m + 1) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (Um N) (by rw [det_um]; exact one_ne_zero)

theorem umGL_val (N : SIdx m → ZMod g) : ((umGL N : Gn g (m + 1)) : Mt g (m + 1)) = Um N := rfl

theorem umGL_mem (N : SIdx m → ZMod g) : umGL N ∈ unipB (ZMod g) (Fin (m + 1)) := by
  rw [mem_unipB, umGL_val]
  exact ⟨fun i k hki => um_upper N hki, fun i => by simp [Um]⟩

def bcol {j : ℕ} (b : JIdx m j → ZMod g) : Fin (m + 1) → ZMod g :=
  fun i => if h : (i : ℕ) ≤ j then b ⟨i, h⟩ else 0

def j0 (m j : ℕ) : JIdx m j := ⟨0, by simp⟩

theorem bcol_zero {j : ℕ} (b : JIdx m j → ZMod g) : bcol b 0 = b (j0 m j) := by
  simp [bcol, j0]

theorem isColFix_hm {j : ℕ} (b : JIdx m j → ZMod g) (hb : bcol b 0 ≠ 0) : IsColFix j (hmGL (bcol b) hb) := by
  refine ⟨fun i k hk => ?_, fun i k hk hi => ?_⟩
  · have : k ≠ 0 := fun h => hk (by simp [h])
    simp [hmGL_val, Hm, this, Matrix.one_apply]
  · have : k = 0 := Fin.ext hk
    subst this
    simp [hmGL_val, Hm, bcol, not_le.2 hi]

variable (ψ₀ : AddChar (ZMod g) Circle) (τ : FDRep ℂ (Gn g (m + 1)))

theorem psi_neg_mul (s : ZMod g) : (ψ₀ (-s) : ℂ) * (ψ₀ s : ℂ) = 1 := by
  rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, Circle.coe_one]

theorem psi_add (a b : ZMod g) : (ψ₀ (a + b) : ℂ) = (ψ₀ a : ℂ) * (ψ₀ b : ℂ) := by
  rw [AddChar.map_add_eq_mul, Circle.coe_mul]

theorem lhs_term {γ : ℂ}
    (hγ : ∀ v : τ, ∑ᶠ y : Gn g (m + 1), (ψ₀ (Matrix.trace (y : Mt g (m + 1))) : ℂ) • τ.ρ y⁻¹ v = γ • v)
    (hτ : IsCusp τ.character) (hm : 0 < m) (l : Module.Dual ℂ τ) (hl : IsFunctional ψ₀ τ.ρ l) {j : ℕ} (v : τ)
    (hA : ∀ h, IsColFix j h → τ.ρ h v = v) (N : SIdx m → ZMod g) (b : JIdx m j → ZMod g) :
    (ψ₀ (-superDiag (umGL N)) : ℂ) * l (sv ψ₀ τ (Um N * Hm (bcol b)) v) =
      if b (j0 m j) = 0 then 0 else γ * l v := by
  split_ifs with hb
  · rw [← umGL_val, sv_singular ψ₀ τ hτ hm _ _ (by rw [bcol_zero]; exact hb), map_zero, mul_zero]
  · have hb' : bcol b 0 ≠ 0 := by rwa [bcol_zero]
    have hx : Um N * Hm (bcol b) = ((umGL N * hmGL (bcol b) hb' : Gn g (m + 1)) : Mt g (m + 1)) := by
      rw [Units.val_mul, umGL_val, hmGL_val]
    rw [hx, sv_unit ψ₀ τ hγ, map_smul, map_mul, Module.End.mul_apply, hl _ (umGL_mem N),
      hA _ (isColFix_hm b hb'), smul_eq_mul]
    have h1 := psi_neg_mul ψ₀ (superDiag (umGL N))
    linear_combination (γ * l v) * h1

theorem trace_hm_mul (c : Fin (m + 1) → ZMod g) (M : Mt g (m + 1)) :
    trace (Hm c * M) = ∑ i, c i * M 0 i + (trace M - M 0 0) := by
  have hH : (Hm c : Mt g (m + 1)) =
      1 + Matrix.of (fun i l => if l = 0 then c i - (1 : Mt g (m + 1)) i 0 else 0) := by
    ext i l
    by_cases hl : l = 0
    · subst hl; simp [Hm]
    · simp [Hm, hl]
  have h2 : trace ((Matrix.of (fun i l => if l = 0 then c i - (1 : Mt g (m + 1)) i 0 else 0)) * M) =
      ∑ i, c i * M 0 i - M 0 0 := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.of_apply]
    rw [Finset.sum_congr rfl (fun i _ => Finset.sum_eq_single (0 : Fin (m + 1))
      (fun l _ hl => by simp [hl]) (by simp))]
    simp [sub_mul, Finset.sum_sub_distrib, Matrix.one_apply]
  rw [hH, Matrix.add_mul, Matrix.one_mul, Matrix.trace_add, h2]
  ring

theorem um_mul_apply_row (y : Mt g (m + 1)) (N : SIdx m → ZMod g) (i : Fin (m + 1))
    (h : ∀ l, l < i → y 0 l = 0) : (y * Um N) 0 i = y 0 i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · simp [Um]
  · intro l _ hl
    rcases lt_or_gt_of_ne hl with hlt | hgt
    · rw [h l hlt, zero_mul]
    · rw [um_upper N hgt, mul_zero]
  · simp

theorem row_cond (y : Mt g (m + 1)) (N : SIdx m → ZMod g) (j : ℕ) :
    (∀ i : JIdx m j, (y * Um N) 0 i.1 = 0) ↔ ∀ i : Fin (m + 1), (i : ℕ) ≤ j → y 0 i = 0 := by
  constructor
  · intro h
    suffices H : ∀ k : ℕ, ∀ i : Fin (m + 1), (i : ℕ) = k → (i : ℕ) ≤ j → y 0 i = 0 from
      fun i hi => H _ i rfl hi
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro i hik hij
      have hl : ∀ l, l < i → y 0 l = 0 := fun l hl => by
        have hl' : (l : ℕ) < i := hl
        exact ih l.val (by omega) l rfl (by omega)
      rw [← um_mul_apply_row y N i hl]
      exact h ⟨i, hij⟩
  · intro h i
    have hl : ∀ l, l < i.1 → y 0 l = 0 := fun l hl => by
      have hl' : (l : ℕ) < i.1 := hl
      have := i.2
      exact h l (by omega)
    rw [um_mul_apply_row y N i.1 hl]
    exact h i.1 i.2

theorem sum_dite_zero {α β : Type} [Fintype α] [AddCommMonoid β] (p : α → Prop) [DecidablePred p]
    (f : (a : α) → p a → β) : ∑ a, (if h : p a then f a h else 0) = ∑ a : {a // p a}, f a.1 a.2 := by
  rw [← Fintype.sum_subtype_add_sum_subtype p (fun a => if h : p a then f a h else 0)]
  have h1 : ∀ a : {a // p a}, (if h : p a.1 then f a.1 h else 0) = f a.1 a.2 := fun a => dif_pos a.2
  have h2 : ∀ a : {a // ¬ p a}, (if h : p a.1 then f a.1 h else 0) = 0 := fun a => dif_neg a.2
  simp only [h1, h2, Finset.sum_const_zero, add_zero]

theorem sumS {β : Type} [AddCommMonoid β] (F : SIdx m → β) :
    ∑ i : Fin (m + 1), ∑ k : Fin (m + 1), (if h : i < k then F ⟨(i, k), h⟩ else 0) = ∑ p : SIdx m, F p := by
  rw [← Fintype.sum_prod_type' (fun i k => if h : i < k then F ⟨(i, k), h⟩ else 0)]
  rw [sum_dite_zero (fun x : Fin (m + 1) × Fin (m + 1) => x.1 < x.2)]

theorem trace_um (y : Mt g (m + 1)) (N : SIdx m → ZMod g) :
    trace (y * Um N) = trace y + ∑ p : SIdx m, N p * y p.1.2 p.1.1 := by
  have hU : (Um N : Mt g (m + 1)) = 1 + Matrix.of (fun l i => if h : l < i then N ⟨(l, i), h⟩ else 0) := by
    ext l i
    by_cases e : l = i
    · subst e; simp [Um]
    · simp [Um, e, Matrix.one_apply_ne e]
  rw [hU, Matrix.mul_add, Matrix.mul_one, Matrix.trace_add]
  congr 1
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.of_apply]
  rw [Finset.sum_comm, ← sumS]
  refine Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun i _ => ?_))
  split_ifs <;> simp [mul_comm]

theorem sd_um (N : SIdx m → ZMod g) :
    superDiag (umGL N) = ∑ p : SIdx m, (if (p.1.2 : ℕ) = p.1.1 + 1 then N p else 0) := by
  simp only [superDiag, umGL_val]
  simp_rw [Finset.sum_filter]
  rw [← sumS]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ => ?_))
  by_cases h : i < k
  · rw [dif_pos h]
    by_cases e : (k : ℕ) = i + 1
    · simp [e, Um, ne_of_lt h, h]
    · simp [e]
  · rw [dif_neg h]
    have : ¬ (k : ℕ) = i + 1 := fun e => h (by rw [Fin.lt_iff_val_lt_val]; omega)
    simp [this]

def IsY (j : ℕ) (y : Mt g (m + 1)) : Prop :=
  (∀ i : Fin (m + 1), (i : ℕ) ≤ j → y 0 i = 0) ∧
    ∀ i k : Fin (m + 1), i < k → y k i = if (k : ℕ) = i + 1 then 1 else 0

theorem kern_inner (hψ : ψ₀ ≠ 1) (j : ℕ) (y : Mt g (m + 1)) (N : SIdx m → ZMod g) :
    ∑ b : JIdx m j → ZMod g, (ψ₀ (-superDiag (umGL N)) : ℂ) * (ψ₀ (trace (Um N * Hm (bcol b) * y)) : ℂ) =
      (if ∀ i : Fin (m + 1), (i : ℕ) ≤ j → y 0 i = 0 then (g : ℂ) ^ Fintype.card (JIdx m j) else 0) *
        ((ψ₀ (trace y - y 0 0) : ℂ) * (ψ₀ (-superDiag (umGL N) + ∑ p : SIdx m, N p * y p.1.2 p.1.1) : ℂ)) := by
  have step1 : ∀ b, trace (Um N * Hm (bcol b) * y) =
      (∑ i : JIdx m j, b i * (y * Um N) 0 i.1) + ((trace y - y 0 0) + ∑ p : SIdx m, N p * y p.1.2 p.1.1) := by
    intro b
    rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, trace_hm_mul, trace_um,
      um_mul_apply_row y N 0 (fun l hl => absurd hl (Fin.not_lt_zero l))]
    have hsum : ∑ i, bcol b i * (y * Um N) 0 i = ∑ i : JIdx m j, b i * (y * Um N) 0 i.1 := by
      simp only [bcol, dite_mul, zero_mul]
      rw [sum_dite_zero (fun i : Fin (m + 1) => (i : ℕ) ≤ j)]
    rw [hsum]
    ring
  have hb : ∀ b : JIdx m j → ZMod g,
      (ψ₀ (-superDiag (umGL N)) : ℂ) * (ψ₀ (trace (Um N * Hm (bcol b) * y)) : ℂ) =
      (ψ₀ (∑ i : JIdx m j, b i * (y * Um N) 0 i.1) : ℂ) *
      ((ψ₀ (trace y - y 0 0) : ℂ) * (ψ₀ (-superDiag (umGL N) + ∑ p : SIdx m, N p * y p.1.2 p.1.1) : ℂ)) := by
    intro b
    rw [step1]
    simp only [psi_add]
    ring
  rw [Finset.sum_congr rfl (fun b _ => hb b), ← Finset.sum_mul, sum_pi_psi ψ₀ hψ]
  congr 1
  have : ((fun i : JIdx m j => (y * Um N) 0 i.1) = 0) ↔ ∀ i : Fin (m + 1), (i : ℕ) ≤ j → y 0 i = 0 := by
    rw [← row_cond y N j, funext_iff]
    rfl
  by_cases h : ∀ i : Fin (m + 1), (i : ℕ) ≤ j → y 0 i = 0
  · rw [if_pos (this.2 h), if_pos h]
  · rw [if_neg (fun e => h (this.1 e)), if_neg h]

theorem kern_exp (y : Mt g (m + 1)) (N : SIdx m → ZMod g) :
    -superDiag (umGL N) + ∑ p : SIdx m, N p * y p.1.2 p.1.1 =
      ∑ p : SIdx m, N p * (y p.1.2 p.1.1 - if (p.1.2 : ℕ) = p.1.1 + 1 then 1 else 0) := by
  rw [sd_um, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  split_ifs <;> ring

theorem kern_hc (y : Mt g (m + 1)) :
    ((fun p : SIdx m => y p.1.2 p.1.1 - if (p.1.2 : ℕ) = p.1.1 + 1 then (1 : ZMod g) else 0) = 0) ↔
      ∀ i k : Fin (m + 1), i < k → y k i = if (k : ℕ) = i + 1 then 1 else 0 := by
  rw [funext_iff]
  constructor
  · intro h i k hik
    exact sub_eq_zero.1 (h ⟨(i, k), hik⟩)
  · intro h p
    exact sub_eq_zero.2 (h p.1.1 p.1.2 p.2)

theorem kern (hψ : ψ₀ ≠ 1) (j : ℕ) (y : Mt g (m + 1)) :
    ∑ N : SIdx m → ZMod g, ∑ b : JIdx m j → ZMod g,
        (ψ₀ (-superDiag (umGL N)) : ℂ) * (ψ₀ (trace (Um N * Hm (bcol b) * y)) : ℂ) =
      if IsY j y then (g : ℂ) ^ Fintype.card (JIdx m j) * (g : ℂ) ^ Fintype.card (SIdx m) *
        (ψ₀ (trace y - y 0 0) : ℂ) else 0 := by
  rw [Finset.sum_congr rfl (fun N _ => kern_inner ψ₀ hψ j y N), ← Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun N _ => by rw [kern_exp y N]), ← Finset.mul_sum, sum_pi_psi ψ₀ hψ]
  by_cases hR : ∀ i : Fin (m + 1), (i : ℕ) ≤ j → y 0 i = 0
  · by_cases hc : (fun p : SIdx m => y p.1.2 p.1.1 - if (p.1.2 : ℕ) = p.1.1 + 1 then (1 : ZMod g) else 0) = 0
    · rw [if_pos hR, if_pos hc, if_pos (show IsY j y from ⟨hR, (kern_hc y).1 hc⟩)]
      ring
    · rw [if_neg hc, if_neg (show ¬ IsY j y from fun h => hc ((kern_hc y).2 h.2))]
      ring
  · rw [if_neg hR, if_neg (show ¬ IsY j y from fun h => hR h.1)]
    ring

end DiscreteGroups.sglob.DzFe
