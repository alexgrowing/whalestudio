import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneSubEwMem
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.SymChar.EdgeReindex

theorem sum_edge {Q : Type} [AddCommMonoid Q] {r t : ℕ} (ht : t < r) (P : Fin r → Prop) [DecidablePred P]
    (hP : ∀ j, P j ↔ j.val = t) (f : Fin r → Q) : (∑ j, if P j then f j else 0) = f ⟨t, ht⟩ := by
  rw [Finset.sum_eq_single ⟨t, ht⟩]
  · rw [if_pos ((hP _).2 rfl)]
  · intro b _ hb
    rw [if_neg]
    intro h
    exact hb (Fin.ext ((hP b).1 h))
  · simp

def extF {Q : Type} [AddCommGroup Q] {r : ℕ} (F : Fin r → Fin r → Q) (a b : ℕ) : Q :=
  if h : a < r ∧ b < r then F ⟨a, h.1⟩ ⟨b, h.2⟩ else 0

def termAt {Q : Type} [AddCommGroup Q] (ρ k : ℕ) (s : Bool) {r : ℕ} (F : Fin r → Fin r → Q) (n : ℕ) : Q :=
  if n < ρ then extF F n (if n + 1 < ρ then n + 1 else ρ + k)
  else if n + 1 < ρ + k then (if s then extF F n (n + 1) else 0) else 0

theorem inner_eq {Q : Type} [AddCommGroup Q] (ρ k r : ℕ) (hr : r = k + 2 * ρ + 1) (s : Bool)
    (F : Fin r → Fin r → Q) (i : Fin r) :
    (∑ j : Fin r, if symEdge ρ k i j then GlobalTheory.Mem.SymChar.wtA ρ k s i j • F i j else 0) =
      termAt ρ k s F i.1 := by
  have hi := i.2
  unfold termAt
  by_cases h1 : i.1 < ρ
  · by_cases h2 : i.1 + 1 < ρ
    · rw [sum_edge (t := i.1 + 1) (by omega) _ (fun j => by
        simp only [symEdge]; constructor <;> intro h <;> omega)]
      rw [if_pos h1, if_pos h2, extF, dif_pos ⟨i.2, by omega⟩]
      simp only [GlobalTheory.Mem.SymChar.wtA, if_pos h1, one_smul]
    · rw [sum_edge (t := ρ + k) (by omega) _ (fun j => by
        simp only [symEdge]; constructor <;> intro h <;> omega)]
      rw [if_pos h1, if_neg h2, extF, dif_pos ⟨i.2, by omega⟩]
      simp only [GlobalTheory.Mem.SymChar.wtA, if_pos h1, one_smul]
  · by_cases h2 : i.1 + 1 < ρ + k
    · rw [sum_edge (t := i.1 + 1) (by omega) _ (fun j => by
        simp only [symEdge]; constructor <;> intro h <;> omega)]
      rw [if_neg h1, if_pos h2]
      simp only [GlobalTheory.Mem.SymChar.wtA, if_neg h1, if_pos h2]
      cases s
      · simp
      · rw [extF, dif_pos ⟨i.2, by omega⟩]
        simp
    · rw [if_neg h1, if_neg h2]
      refine Finset.sum_eq_zero fun j _ => ?_
      simp only [GlobalTheory.Mem.SymChar.wtA, if_neg h1, if_neg h2, zero_smul, ite_self]

theorem sum_symEdge_wtA : ∀ (Q : Type) [AddCommGroup Q] (ρ k r : ℕ) (hr : r = k + 2 * ρ + 1) (s : Bool) (F : Fin r → Fin r → Q), (∑ i : Fin r, ∑ j : Fin r, if symEdge ρ k i j then GlobalTheory.Mem.SymChar.wtA ρ k s i j • F i j else 0) = (∑ a : Fin ρ, F ⟨a.1, by have := a.2; omega⟩ ⟨if a.1 + 1 < ρ then a.1 + 1 else ρ + k, by have := a.2; split_ifs <;> omega⟩) + ∑ i : Fin k, if h : i.1 + 1 < k then (if s then F ⟨ρ + i.1, by omega⟩ ⟨ρ + i.1 + 1, by omega⟩ else 0) else 0 := by
  intro Q _ ρ k r hr s F
  rw [Finset.sum_congr rfl (fun i _ => inner_eq ρ k r hr s F i)]
  rw [Fin.sum_univ_eq_sum_range (fun n => termAt ρ k s F n) r]
  have e : Finset.range r = Finset.range (ρ + (k + (ρ + 1))) := congrArg Finset.range (by omega)
  rw [e, Finset.sum_range_add, Finset.sum_range_add]
  have h3 : (∑ x ∈ Finset.range (ρ + 1), termAt ρ k s F (ρ + (k + x))) = 0 := by
    refine Finset.sum_eq_zero fun x _ => ?_
    unfold termAt
    rw [if_neg (by omega), if_neg (by omega)]
  rw [h3, add_zero]
  congr 1
  · rw [← Fin.sum_univ_eq_sum_range (fun n => termAt ρ k s F n) ρ]
    refine Finset.sum_congr rfl fun a _ => ?_
    have ha := a.2
    unfold termAt extF
    rw [if_pos ha, dif_pos ⟨by omega, by split_ifs <;> omega⟩]
  · rw [← Fin.sum_univ_eq_sum_range (fun n => termAt ρ k s F (ρ + n)) k]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hi := i.2
    by_cases h : i.1 + 1 < k
    · rw [dif_pos h]
      unfold termAt
      rw [if_neg (by omega), if_pos (by omega)]
      cases s
      · rfl
      · simp only [if_true]
        unfold extF
        rw [dif_pos ⟨by omega, by omega⟩]
    · rw [dif_neg h]
      unfold termAt
      rw [if_neg (by omega), if_neg (by omega)]

end GlobalTheory.Mem.SymChar.EdgeReindex
