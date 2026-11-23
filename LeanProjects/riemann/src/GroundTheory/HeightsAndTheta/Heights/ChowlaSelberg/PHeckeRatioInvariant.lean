import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.HeckeRatioInvariant
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open UpperHalfPlane ModularForm
open scoped MatrixGroups

noncomputable section

namespace HeckeRatioInvariant

theorem discriminant_smul (γ : SL(2, ℤ)) (z : ℍ) :
    discriminant (γ • z) = (((γ 1 0 : ℤ) : ℂ) * z + ((γ 1 1 : ℤ) : ℂ)) ^ 12 * discriminant z := by
  have h := congr_fun (SlashInvariantForm.slash_action_generators_SL2Z
    discriminant_S_invariant discriminant_T_invariant γ) z
  rw [SL_slash_apply] at h
  have hd : denom γ z = ((γ 1 0 : ℤ) : ℂ) * z + ((γ 1 1 : ℤ) : ℂ) := by
    simp [denom]
  have hne : denom γ z ≠ 0 := denom_ne_zero _ _
  rw [← hd, ← h, zpow_neg, show (12 : ℤ) = ((12 : ℕ) : ℤ) from rfl, zpow_natCast]
  field_simp

theorem discriminant_eq_of_coe_eq (a b c d : ℤ) (hdet : a * d - b * c = 1) {z w : ℍ}
    (h : (w : ℂ) = ((a : ℂ) * z + b) / ((c : ℂ) * z + d)) :
    discriminant w = ((c : ℂ) * z + d) ^ 12 * discriminant z := by
  let γ : SL(2, ℤ) := ⟨!![a, b; c, d], by simp [Matrix.det_fin_two_of, hdet]⟩
  have hw : w = γ • z := UpperHalfPlane.ext (by rw [h, coe_specialLinearGroup_apply]; simp [γ])
  rw [hw, discriminant_smul]
  simp [γ]

theorem map_range_succ_eq_cons (f : ℕ → ℂ) (m : ℕ) :
    (Multiset.range (m + 1)).map f = f 0 ::ₘ (Multiset.range m).map (fun a ↦ f (a + 1)) := by
  rw [← Multiset.coe_range, ← Multiset.coe_range, Multiset.map_coe, Multiset.map_coe,
    List.range_succ_eq_map]
  simp [Function.comp_def]

theorem map_range_shift (g : ℕ → ℂ) (m : ℕ) (h : g m = g 0) :
    (Multiset.range m).map (fun a ↦ g (a + 1)) = (Multiset.range m).map g := by
  cases m with
  | zero => rfl
  | succ m =>
    rw [map_range_succ_eq_cons g m, Multiset.range_succ, Multiset.map_cons, h]

theorem heckeRatios_alt (n : ℕ+) (τ : ℍ) :
    heckeRatios n (ModularGroup.T • τ) = heckeRatios n τ := by
  have hT : ((ModularGroup.T • τ : ℍ) : ℂ) = τ + 1 := by
    rw [modular_T_smul, coe_vadd]; simp [add_comm]
  have hn : ((n : ℕ) : ℂ) ≠ 0 := by exact_mod_cast n.ne_zero
  have h0 : discriminant (ModularGroup.T • τ) = discriminant τ := by
    rw [discriminant_eq_of_coe_eq 1 1 0 1 (by norm_num) (z := τ) (by rw [hT]; push_cast; ring)]
    simp
  have h1 : discriminant (mulPoint n (ModularGroup.T • τ)) = discriminant (mulPoint n τ) := by
    rw [discriminant_eq_of_coe_eq 1 (n : ℕ) 0 1 (by norm_num) (z := mulPoint n τ)
      (by rw [coe_mulPoint, coe_mulPoint, hT]; push_cast; ring)]
    simp
  have h2 : ∀ a : ℕ, divPoint n a (ModularGroup.T • τ) = divPoint n (a + 1) τ := fun a ↦
    UpperHalfPlane.ext (by rw [coe_divPoint, coe_divPoint, hT]; push_cast; ring)
  have h3 : discriminant (divPoint n n τ) = discriminant (divPoint n 0 τ) := by
    rw [discriminant_eq_of_coe_eq 1 1 0 1 (by norm_num) (z := divPoint n 0 τ)
      (by rw [coe_divPoint, coe_divPoint]; field_simp; push_cast; ring)]
    simp
  have h4 : (Multiset.range n).map
      (fun a : ℕ ↦ discriminant (divPoint n a (ModularGroup.T • τ)) / discriminant τ) =
      (Multiset.range n).map (fun a : ℕ ↦ discriminant (divPoint n a τ) / discriminant τ) := by
    simp_rw [h2]
    exact map_range_shift (fun a ↦ discriminant (divPoint n a τ) / discriminant τ) n (by simp [h3])
  unfold heckeRatios
  rw [h0, h1, h4]

def negInvMod (p j : ℕ) : ℕ := (-((j : ZMod p)⁻¹)).val

theorem negInvMod_spec {p : ℕ} [Fact p.Prime] {j : ℕ} (h0 : 0 < j) (hj : j < p) :
    0 < negInvMod p j ∧ negInvMod p j < p ∧ p ∣ j * negInvMod p j + 1 ∧
      negInvMod p (negInvMod p j) = j := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hj0 : ((j : ℕ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hd
    have := Nat.le_of_dvd h0 hd
    omega
  have hcast : ((negInvMod p j : ℕ) : ZMod p) = -((j : ZMod p)⁻¹) := ZMod.natCast_zmod_val _
  refine ⟨?_, ZMod.val_lt _, ?_, ?_⟩
  · rw [Nat.pos_iff_ne_zero, negInvMod, Ne, ZMod.val_eq_zero, neg_eq_zero, inv_eq_zero]
    exact hj0
  · rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    rw [hcast, mul_neg, mul_inv_cancel₀ hj0]
    ring
  · rw [negInvMod, hcast, inv_neg, neg_neg, inv_inv, ZMod.val_natCast, Nat.mod_eq_of_lt hj]

theorem coe_S_smul (τ : ℍ) : ((ModularGroup.S • τ : ℍ) : ℂ) = (-(τ : ℂ))⁻¹ := by
  rw [modular_S_smul, coe_mk]

theorem discriminant_S_smul (τ : ℍ) :
    discriminant (ModularGroup.S • τ) = (τ : ℂ) ^ 12 * discriminant τ := by
  have hτ : (τ : ℂ) ≠ 0 := τ.ne_zero
  rw [discriminant_eq_of_coe_eq 0 (-1) 1 0 (by norm_num) (z := τ)
    (by rw [coe_S_smul]; push_cast; ring)]
  simp

theorem ratio_S (n : ℕ+) (τ : ℍ) (j b k : ℕ) (h : j * b + 1 = (n : ℕ) * k) :
    discriminant (divPoint n j (ModularGroup.S • τ)) / discriminant (ModularGroup.S • τ) =
      discriminant (divPoint n b τ) / discriminant τ := by
  have hτ : (τ : ℂ) ≠ 0 := τ.ne_zero
  have hn : ((n : ℕ) : ℂ) ≠ 0 := by exact_mod_cast n.ne_zero
  have hC : (j : ℂ) * b + 1 = (n : ℕ) * k := by exact_mod_cast h
  have hZ : (j : ℤ) * (-(b : ℤ)) - (-(k : ℤ)) * ((n : ℕ) : ℤ) = 1 := by
    have : ((j * b + 1 : ℕ) : ℤ) = (((n : ℕ) * k : ℕ) : ℤ) := by rw [h]
    push_cast at this
    linarith
  have hden : (((((n : ℕ) : ℤ)) : ℂ) * (divPoint n b τ : ℂ) + ((-(b : ℤ) : ℤ) : ℂ)) = τ := by
    rw [coe_divPoint]; push_cast; field_simp; ring
  have e := discriminant_eq_of_coe_eq (j : ℤ) (-(k : ℤ)) ((n : ℕ) : ℤ) (-(b : ℤ)) hZ
    (z := divPoint n b τ) (w := divPoint n j (ModularGroup.S • τ)) (by
      rw [hden, coe_divPoint, coe_divPoint, coe_S_smul]
      push_cast
      field_simp
      linear_combination (-1 : ℂ) * hC)
  rw [e, hden, discriminant_S_smul]
  have := discriminant_ne_zero τ
  field_simp

theorem heckeRatios_S (p : ℕ) (hp : p.Prime) (τ : ℍ) :
    heckeRatios ⟨p, hp.pos⟩ (ModularGroup.S • τ) = heckeRatios ⟨p, hp.pos⟩ τ := by
  have := Fact.mk hp
  obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, by have := hp.pos; omega⟩
  set n : ℕ+ := ⟨m + 1, hp.pos⟩ with hn_def
  have hτ : (τ : ℂ) ≠ 0 := τ.ne_zero
  have hn : ((n : ℕ) : ℂ) ≠ 0 := by exact_mod_cast n.ne_zero
  have hΔ := discriminant_ne_zero τ
  set g : ℕ → ℂ := fun a ↦ discriminant (divPoint n a τ) / discriminant τ with hg
  set gS : ℕ → ℂ := fun a ↦
    discriminant (divPoint n a (ModularGroup.S • τ)) / discriminant (ModularGroup.S • τ) with hgS
  have e1 : heckeRatios n (ModularGroup.S • τ) =
      ((n : ℂ) ^ 12 * discriminant (mulPoint n (ModularGroup.S • τ)) /
        discriminant (ModularGroup.S • τ)) ::ₘ
        (gS 0 ::ₘ (Multiset.range m).map (fun a ↦ gS (a + 1))) := by
    rw [← map_range_succ_eq_cons]; rfl
  have e2 : heckeRatios n τ = ((n : ℂ) ^ 12 * discriminant (mulPoint n τ) / discriminant τ) ::ₘ
      (g 0 ::ₘ (Multiset.range m).map (fun a ↦ g (a + 1))) := by
    rw [← map_range_succ_eq_cons]; rfl
  have hA : (n : ℂ) ^ 12 * discriminant (mulPoint n (ModularGroup.S • τ)) /
      discriminant (ModularGroup.S • τ) = g 0 := by
    rw [discriminant_eq_of_coe_eq 0 (-1) 1 0 (by norm_num) (z := divPoint n 0 τ)
      (by rw [coe_mulPoint, coe_divPoint, coe_S_smul]; push_cast; ring_nf; simp only [inv_inv]; try ring),
      discriminant_S_smul, hg]
    simp only [coe_divPoint]
    push_cast
    field_simp
    try ring
  have hB : gS 0 = (n : ℂ) ^ 12 * discriminant (mulPoint n τ) / discriminant τ := by
    rw [hgS]
    dsimp only
    rw [discriminant_eq_of_coe_eq 0 (-1) 1 0 (by norm_num) (z := mulPoint n τ)
      (by rw [coe_mulPoint, coe_divPoint, coe_S_smul]; push_cast; ring),
      discriminant_S_smul, coe_mulPoint]
    push_cast
    field_simp
    try ring
  have hmid : (Multiset.range m).map (fun a ↦ gS (a + 1)) =
      (Multiset.range m).map (fun a ↦ g (a + 1)) := by
    refine Multiset.map_eq_map_of_bij_of_nodup _ _ (Multiset.nodup_range m)
      (Multiset.nodup_range m) (fun a _ ↦ negInvMod (m + 1) (a + 1) - 1) ?_ ?_ ?_ ?_
    · intro a ha
      rw [Multiset.mem_range] at ha ⊢
      have := negInvMod_spec (p := m + 1) (j := a + 1) (by omega) (by omega)
      omega
    · intro a₁ ha₁ a₂ ha₂ he
      rw [Multiset.mem_range] at ha₁ ha₂
      have s₁ := negInvMod_spec (p := m + 1) (j := a₁ + 1) (by omega) (by omega)
      have s₂ := negInvMod_spec (p := m + 1) (j := a₂ + 1) (by omega) (by omega)
      have he' : negInvMod (m + 1) (a₁ + 1) = negInvMod (m + 1) (a₂ + 1) := by omega
      have := congrArg (negInvMod (m + 1)) he'
      rw [s₁.2.2.2, s₂.2.2.2] at this
      omega
    · intro b hb
      rw [Multiset.mem_range] at hb
      have s := negInvMod_spec (p := m + 1) (j := b + 1) (by omega) (by omega)
      refine ⟨negInvMod (m + 1) (b + 1) - 1, Multiset.mem_range.2 (by omega), ?_⟩
      rw [Nat.sub_add_cancel s.1, s.2.2.2]
      rfl
    · intro a ha
      rw [Multiset.mem_range] at ha
      have s := negInvMod_spec (p := m + 1) (j := a + 1) (by omega) (by omega)
      obtain ⟨k, hk⟩ := s.2.2.1
      rw [Nat.sub_add_cancel s.1]
      exact ratio_S n τ (a + 1) (negInvMod (m + 1) (a + 1)) k hk
  rw [e1, e2, hA, hB, hmid, Multiset.cons_swap]

theorem proof : HeckeRatioInvariant.Statement := by
  intro p hp γ τ
  let H : Subgroup SL(2, ℤ) :=
    { carrier := {g | ∀ τ : ℍ, heckeRatios ⟨p, hp.pos⟩ (g • τ) = heckeRatios ⟨p, hp.pos⟩ τ}
      mul_mem' := by
        intro a b ha hb τ
        simp only [Set.mem_ofPred_eq] at ha hb
        rw [mul_smul, ha, hb]
      one_mem' := by intro τ; simp
      inv_mem' := by
        intro a ha τ
        simp only [Set.mem_ofPred_eq] at ha
        rw [← ha (a⁻¹ • τ), smul_inv_smul] }
  have hle : Subgroup.closure {ModularGroup.S, ModularGroup.T} ≤ H := by
    rw [Subgroup.closure_le]
    intro g hg
    rcases hg with rfl | rfl
    · exact heckeRatios_S p hp
    · exact heckeRatios_alt _
  have hγ : γ ∈ H := hle (by rw [SpecialLinearGroup.SL2Z_generators]; trivial)
  exact hγ τ

end HeckeRatioInvariant

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
