import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.EdgeFamOf
import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.NumericProductInequality

noncomputable section

namespace Formalism.MainNotions.Pf14

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility

theorem basis_fin {O M : Type} [CommRing O] [IsDomain O] [AddCommGroup M] [Module O M] (Sg : Submodule O M)
    {ιb : Type} (b : Module.Basis ιb O Sg) (hc : ∃ T : Submodule O M, IsCompl Sg T) (Pr : M → Prop)
    (hb : ∀ i, Pr (b i : M)) :
    ∃ B : Fin (Module.finrank O Sg) → M, (∀ i, Pr (B i)) ∧ LinearIndependent O B ∧
      ∃ T : Submodule O M, IsCompl (Submodule.span O (Set.range B)) T := by
  classical
  by_cases hfin : Finite ιb
  · have := Fintype.ofFinite ιb
    let e : ιb ≃ Fin (Module.finrank O Sg) :=
      Fintype.equivFinOfCardEq (Module.finrank_eq_card_basis b).symm
    refine ⟨fun i => (b (e.symm i) : M), fun i => hb _, ?_, ?_⟩
    · exact (b.linearIndependent.map' Sg.subtype (Submodule.ker_subtype Sg)).comp e.symm e.symm.injective
    · have hr : Set.range (fun i => (b (e.symm i) : M)) = Sg.subtype '' Set.range b := by
        rw [← Set.range_comp]
        exact e.symm.surjective.range_comp (fun j => (b j : M))
      obtain ⟨T, hT⟩ := hc
      refine ⟨T, ?_⟩
      rw [hr, Submodule.span_image, b.span_eq, Submodule.map_top, Submodule.range_subtype]
      exact hT
  · have := Module.Free.of_basis b
    have hnf : ¬ Module.Finite O Sg := fun h => hfin (Module.Finite.finite_basis b)
    rw [Module.finrank_of_not_finite hnf]
    refine ⟨Fin.elim0, fun i => i.elim0, linearIndependent_empty_type, ⊤, ?_⟩
    rw [Set.range_eq_empty, Submodule.span_empty]
    exact isCompl_bot_top

theorem flW_dom {n' m : ℕ} (d : Fin n' → ℕ) : IsDominant (flW (m := m) d) := by
  intro s i j hij
  simp only [flW, Pi.single_apply]
  by_cases hj : j = 0
  · subst hj
    have hi : i = 0 := le_antisymm hij (Fin.zero_le _)
    subst hi
    exact le_refl _
  · rw [if_neg hj]
    split_ifs <;> positivity

theorem restW_dom {n' m : ℕ} (hm : 1 ≤ m) (TT : Finset (Fin n')) (lam0 : Fin n' → Fin (m + 1) → ℤ)
    (h : IsDominant lam0) : IsDominant (restW TT lam0) := by
  intro s i j hij
  have hA := h s
  have h1v : (1 : Fin (m + 1)).val = 1 := by
    rw [Fin.val_one']
    exact Nat.mod_eq_of_lt (by omega)
  have hd : (dT TT lam0 s : ℤ) = if s ∈ TT then lam0 s 0 - lam0 s 1 else 0 := by
    unfold dT flatDeg
    split_ifs
    · exact Int.toNat_of_nonneg (sub_nonneg.mpr (hA (Fin.zero_le _)))
    · rfl
  simp only [restW, flW, Pi.sub_apply, Pi.single_apply, hd]
  by_cases hj : j = 0
  · subst hj
    have hi : i = 0 := le_antisymm hij (Fin.zero_le _)
    subst hi
    exact le_refl _
  · have h1j : (1 : Fin (m + 1)) ≤ j := by
      rw [Fin.le_def, h1v]
      have : j.val ≠ 0 := fun h0 => hj (Fin.ext h0)
      omega
    rw [if_neg hj]
    by_cases hi : i = 0
    · subst hi
      rw [if_pos rfl]
      split_ifs
      · linarith [hA h1j]
      · linarith [hA (Fin.zero_le j)]
    · rw [if_neg hi]
      linarith [hA hij]

theorem lambda_zero_eq_product {n' m : ℕ} (TT : Finset (Fin n')) (lam0 : Fin n' → Fin (m + 1) → ℤ) :
    lam0 = flW (dT TT lam0) + restW TT lam0 := by
  funext s i
  simp only [restW, Pi.add_apply, Pi.sub_apply]
  ring

theorem norm_index_count_bound (A A' x u dV Pi q : ℝ) (nb n2 : ℕ) (hA : A ≤ A') (hx : 0 ≤ x) (hu : 0 ≤ u) (hdV : 0 ≤ dV)
    (hPi : 0 ≤ Pi) (hq : 0 < q) (h1 : q⁻¹ * ((1 - A * x) * Pi) ≤ nb) (h2 : u * dV ≤ Pi * n2) :
    (1 - A' * x) * u * dV / q ≤ ((nb * n2 : ℕ) : ℝ) := by
  push_cast
  have hq' : 0 < q⁻¹ := inv_pos.mpr hq
  rcases le_or_gt 0 (1 - A' * x) with hB | hB
  · have e1 : 1 - A' * x ≤ 1 - A * x := by nlinarith
    have s1 : (1 - A' * x) * u * dV ≤ (1 - A' * x) * (Pi * n2) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left h2 hB
    have s2 : (1 - A' * x) * (Pi * n2) ≤ (1 - A * x) * (Pi * n2) :=
      mul_le_mul_of_nonneg_right e1 (by positivity)
    have s3 : q⁻¹ * ((1 - A * x) * Pi) * n2 ≤ nb * n2 :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    rw [div_eq_mul_inv]
    calc (1 - A' * x) * u * dV * q⁻¹ ≤ (1 - A * x) * (Pi * n2) * q⁻¹ :=
          mul_le_mul_of_nonneg_right (s1.trans s2) hq'.le
      _ = q⁻¹ * ((1 - A * x) * Pi) * n2 := by ring
      _ ≤ nb * n2 := s3
  · have hn : (1 - A' * x) * u * dV ≤ 0 := by
      have := mul_nonneg hu hdV
      nlinarith
    exact (div_nonpos_of_nonpos_of_nonneg hn hq.le).trans (by positivity)

theorem rank_mul_conductor_div_le_one {C : ℝ} (hC : 2 ≤ C) {p n' m r : ℕ} {TT : Finset (Fin n')} {L₁ L₂ : ℕ} {de h x : ℝ}
    {lam0 : Fin n' → Fin (m + 1) → ℤ} {aT bT : Fin n' → ℤ} {a Y : ℝ} {cpp c0 Dp cStar : ℕ}
    (H : Hyps C p n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar) :
    ((m + 1 : ℕ) : ℝ) * c0 / a ≤ 1 := by
  unfold Hyps at H
  obtain ⟨hp, hr, -, hN1, -, hY, -, -, -, -, hcS, hsz⟩ := H
  have hcard : 1 ≤ TT.card := by
    have h1 : 1 ≤ orbitWindowCount r de h x := by unfold orbitWindowCount; omega
    have h2 : 1 ≤ r * TT.card := le_trans (Nat.one_le_pow _ _ h1) hN1
    rcases Nat.eq_zero_or_pos TT.card with h0 | h0
    · rw [h0] at h2
      simp at h2
    · exact h0
  have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hY' : (2 : ℝ) ≤ Y := hr'.trans hY
  have hp' : (1 : ℝ) ≤ p := by exact_mod_cast (by omega : 1 ≤ p)
  have hQ : (1 : ℝ) ≤ (p : ℝ) ^ goodG' r de h x := one_le_pow₀ hp'
  have hcS' : (8 : ℝ) ≤ cStar := by exact_mod_cast (by omega : 8 ≤ cStar)
  have hk : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ m + 1)
  have hN : (1 : ℝ) ≤ (TT.card : ℝ) := by exact_mod_cast hcard
  obtain ⟨ha, hkc⟩ := num_size C ((m + 1 : ℕ) : ℝ) r TT.card (p ^ goodG' r de h x) cStar c0
    (2 * r * n' * cpp) Y a hC hk hr' hN hQ hcS' (Nat.cast_nonneg _) (by positivity) hY' hsz
  have hle : ((m + 1 : ℕ) : ℝ) * c0 ≤ a := by
    have h0 : 0 ≤ ((m + 1 : ℕ) : ℝ) * c0 := by positivity
    nlinarith [mul_le_mul hN (by linarith : (1 : ℝ) ≤ Y) zero_le_one (by linarith)]
  exact div_le_one_of_le₀ hle (by linarith)

private lemma mul_mul_add_le_of_abs_le (Cdeg CLa C Ct0 s s' w v N : ℝ) (h1 : |Cdeg| ≤ Ct0) (h3 : |CLa| ≤ C)
    (hs : 0 ≤ s) (hss : s ≤ s') (hw : 0 ≤ w) (hv : 0 ≤ v) (hN : 0 ≤ N) :
    Cdeg * N * (CLa * s * w + v) ≤ Ct0 * N * (C * s' * w + v) := by
  have hC0 : 0 ≤ C := (abs_nonneg _).trans h3
  have hCt0 : 0 ≤ Ct0 := (abs_nonneg _).trans h1
  have hX : |CLa * s * w + v| ≤ C * s' * w + v := by
    have hm : |CLa| * s ≤ C * s' := mul_le_mul h3 hss hs hC0
    calc |CLa * s * w + v| ≤ |CLa * s * w| + |v| := abs_add_le _ _
      _ = |CLa| * s * w + v := by rw [abs_mul, abs_mul, abs_of_nonneg hs, abs_of_nonneg hw, abs_of_nonneg hv]
      _ ≤ C * s' * w + v := by linarith [mul_le_mul_of_nonneg_right hm hw]
  calc Cdeg * N * (CLa * s * w + v) ≤ |Cdeg * N * (CLa * s * w + v)| := le_abs_self _
    _ = |Cdeg| * N * |CLa * s * w + v| := by rw [abs_mul, abs_mul, abs_of_nonneg hN]
    _ ≤ Ct0 * N * (C * s' * w + v) :=
      mul_le_mul (mul_le_mul_of_nonneg_right h1 hN) hX (abs_nonneg _) (mul_nonneg hCt0 hN)

theorem level_lower_bound_terms (Cdeg CLa C Ct0 : ℝ) (h1 : |Cdeg| ≤ Ct0) (h3 : |CLa| ≤ C)
    (p N N₁ Ns L₁ G' k : ℕ) (hNs : Ns ≤ N₁) (hp : 1 ≤ p) (hk : 1 ≤ k) (a : ℝ) (ha : 1 ≤ a) :
    Cdeg * (N : ℝ) * (CLa * (Ns : ℝ) ^ 2 * Real.log a * a / ((p : ℝ) * (k : ℝ)) + a * (p : ℝ) ^ (-(L₁ : ℤ)) +
      (k : ℝ) * (p : ℝ) ^ G') ≤ t0 C Ct0 p N N₁ L₁ G' k a := by
  unfold t0 tableLineDegreeFive.La
  have hlog : 0 ≤ Real.log a := Real.log_nonneg ha
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hNs' : (Ns : ℝ) ^ 2 ≤ (N₁ : ℝ) ^ 2 := by
    have : (Ns : ℝ) ≤ N₁ := by exact_mod_cast hNs
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) this 2
  have hw : 0 ≤ Real.log a * a / ((p : ℝ) * (k : ℝ)) := by positivity
  have hv : 0 ≤ a * (p : ℝ) ^ (-(L₁ : ℤ)) + (k : ℝ) * (p : ℝ) ^ G' := by positivity
  have key := mul_mul_add_le_of_abs_le Cdeg CLa C Ct0 ((Ns : ℝ) ^ 2) ((N₁ : ℝ) ^ 2) _ _ (N : ℝ) h1 h3 (by positivity) hNs' hw hv
    (Nat.cast_nonneg _)
  refine le_trans (le_of_eq ?_) (key.trans_eq ?_) <;> ring

end Formalism.MainNotions.Pf14
