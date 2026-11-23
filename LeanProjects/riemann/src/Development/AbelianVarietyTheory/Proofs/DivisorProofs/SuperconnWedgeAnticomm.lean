import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicConnectionAddSection

set_option autoImplicit false

noncomputable section

open Matrix Set Filter Topology GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm
open scoped Real ContDiff

namespace GlobalTheory.TorsionForm.Odd

theorem sgn_erase_of_mem {m : ℕ} {i : Fin m} (k : Fin m) {S : Finset (Fin m)} (hi : i ∈ S) :
    sgn k (S.erase i) = if i < k then -sgn k S else sgn k S := by
  unfold sgn
  rw [Finset.filter_erase]
  split_ifs with h
  · have hm : i ∈ S.filter (· < k) := Finset.mem_filter.2 ⟨hi, h⟩
    rw [Finset.card_erase_of_mem hm]
    have hpos : 0 < (S.filter (· < k)).card := Finset.card_pos.2 ⟨i, hm⟩
    obtain ⟨c, hc⟩ : ∃ c, (S.filter (· < k)).card = c + 1 :=
      ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
    rw [hc, Nat.add_sub_cancel, pow_succ]
    ring
  · have hm : i ∉ S.filter (· < k) := fun hm => h (Finset.mem_filter.1 hm).2
    rw [Finset.erase_eq_self.2 hm]

theorem sgn_insert_of_not_mem {m : ℕ} {i : Fin m} (k : Fin m) {S : Finset (Fin m)} (hi : i ∉ S) :
    sgn k (insert i S) = if i < k then -sgn k S else sgn k S := by
  have e := sgn_erase_of_mem k (Finset.mem_insert_self i S)
  rw [Finset.erase_insert hi] at e
  rw [e]
  split_ifs <;> simp

theorem wedge_wedge {m : ℕ} (i k : Fin m) (w : Ext m) :
    wedge i (wedge k w) = -wedge k (wedge i w) := by
  funext S
  simp only [wedge, Pi.neg_apply]
  by_cases hik : i = k
  · subst hik; simp
  by_cases hi : i ∈ S <;> by_cases hk : k ∈ S <;>
    simp [hi, hk, hik, Ne.symm hik, Finset.mem_erase]
  rw [sgn_erase_of_mem k hi, sgn_erase_of_mem i hk, Finset.erase_right_comm]
  rcases lt_or_gt_of_ne hik with h | h
  · simp [h, not_lt.2 h.le]; ring
  · simp [h, not_lt.2 h.le]; ring

theorem contr_wedge {m : ℕ} {i k : Fin m} (hik : i ≠ k) (w : Ext m) :
    contr i (wedge k w) = -wedge k (contr i w) := by
  funext S
  simp only [contr, wedge, Pi.neg_apply]
  by_cases hi : i ∈ S <;> by_cases hk : k ∈ S <;>
    simp [hi, hk, hik, Ne.symm hik, Finset.mem_erase, Finset.mem_insert]
  rw [sgn_insert_of_not_mem k hi, sgn_erase_of_mem i hk, Finset.erase_insert_of_ne hik]
  rcases lt_or_gt_of_ne hik with h | h
  · simp [h, not_lt.2 h.le]; ring
  · simp [h, not_lt.2 h.le]; ring

theorem wedge_neg {m : ℕ} (i : Fin m) (w : Ext m) : wedge i (-w) = -wedge i w :=
  (wedgeL i).map_neg w

theorem wedge_sub {m : ℕ} (i : Fin m) (w w' : Ext m) : wedge i (w - w') = wedge i w - wedge i w' :=
  (wedgeL i).map_sub w w'

theorem wedge_sum {m : ℕ} (i : Fin m) {ι : Type} (s : Finset ι) (f : ι → Ext m) :
    wedge i (∑ a ∈ s, f a) = ∑ a ∈ s, wedge i (f a) :=
  map_sum (wedgeL i) f s

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g n : ℕ}

theorem fderiv_wedge {m : ℕ} (k : Fin m) {σ : Pt E g → Ext m} {P : Pt E g}
    (hσ : DifferentiableAt ℝ σ P) (v : Pt E g) :
    fderiv ℝ (fun Q => wedge k (σ Q)) P v = wedge k (fderiv ℝ σ P v) := by
  have e := (((wedgeL k).restrictScalars ℝ).hasFDerivAt (x := σ P)).comp P hσ.hasFDerivAt
  rw [show (fun Q => wedge k (σ Q)) = ((wedgeL k).restrictScalars ℝ) ∘ σ from rfl, e.fderiv]
  rfl

theorem dz_wedge_comm {m : ℕ} (k : Fin m) {σ : Pt E g → Ext m} {P : Pt E g}
    (hσ : DifferentiableAt ℝ σ P) (v : Pt E g) :
    d10 (fun Q => wedge k (σ Q)) P v = wedge k (d10 σ P v) := by
  simp only [d10, fderiv_wedge k hσ, ← wedge_smul, ← wedge_sub]

theorem dbar_wedge_comm {m : ℕ} (k : Fin m) {σ : Pt E g → Ext m} {P : Pt E g}
    (hσ : DifferentiableAt ℝ σ P) (v : Pt E g) :
    d01 (fun Q => wedge k (σ Q)) P v = wedge k (d01 σ P v) := by
  simp only [d01, fderiv_wedge k hσ, ← wedge_smul, ← wedge_add]

theorem nab10_wedge_eq_wedge_nab10 (h : Pt E g → ℝ) (k : Fin (n + n + g)) {σ : Pt E g → Ext (n + n + g)}
    {P : Pt E g} (hσ : DifferentiableAt ℝ σ P) (v : Pt E g) :
    pointDifference h (fun Q => wedge k (σ Q)) P v = wedge k (pointDifference h σ P v) := by
  simp only [pointDifference, dz_wedge_comm k hσ, wedge_add, wedge_smul]

theorem dzb_ne (k : Fin (n + n)) (a : Fin g) : dzb n a ≠ k.castAdd g := by
  intro e
  have := congrArg Fin.val e
  simp [dzb] at this
  omega

theorem connForm_wedge (τ : E → Matrix (Fin g) (Fin g) ℂ) (b v : E) (k : Fin (n + n))
    (w : Ext (n + n + g)) :
    connForm τ b v (wedge (k.castAdd g) w) = wedge (k.castAdd g) (connForm τ b v w) := by
  simp only [connForm, contr_wedge (dzb_ne k _), wedge_neg, wedge_wedge (dzb n _) (k.castAdd g),
    neg_neg, wedge_sum, wedge_smul]

theorem superconn_wedge (τ : E → Matrix (Fin g) (Fin g) ℂ) (h : Pt E g → ℝ) (β : Fin n → E)
    (u : ℝ) (k : Fin (n + n)) {σ : Pt E g → Ext (n + n + g)} {P : Pt E g}
    (hσ : DifferentiableAt ℝ σ P) :
    superconn τ h β u (fun Q => wedge (k.castAdd g) (σ Q)) P =
      -wedge (k.castAdd g) (superconn τ h β u σ P) := by
  have e1 : nablaE τ h β (fun Q => wedge (k.castAdd g) (σ Q)) P =
      -wedge (k.castAdd g) (nablaE τ h β σ P) := by
    simp only [nablaE, nab10_wedge_eq_wedge_nab10 h _ hσ, dbar_wedge_comm _ hσ, connForm_wedge, ← wedge_add,
      wedge_wedge (dt g _) (k.castAdd g), wedge_wedge (dtb g _) (k.castAdd g), wedge_sum,
      ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun x _ => by simp only [wedge_add]; abel
  have e2 : dbarV (fun Q => wedge (k.castAdd g) (σ Q)) P = -wedge (k.castAdd g) (dbarV σ P) := by
    simp only [dbarV, dbar_wedge_comm _ hσ, wedge_wedge (dzb n _) (k.castAdd g), wedge_sum,
      Finset.sum_neg_distrib]
  have e3 : dbarAdj τ h (fun Q => wedge (k.castAdd g) (σ Q)) P =
      -wedge (k.castAdd g) (dbarAdj τ h σ P) := by
    simp only [dbarAdj, nab10_wedge_eq_wedge_nab10 h _ hσ, contr_wedge (dzb_ne k _), smul_neg,
      Finset.sum_neg_distrib, wedge_neg, wedge_sum, wedge_smul]
  simp only [superconn, e1, e2, e3, wedge_add, wedge_smul, wedge_neg, smul_add, smul_neg, neg_add]

end GlobalTheory.TorsionForm.Odd
