import Formalism.LocalToGlobal.GlobalTheory.GL5.VolumeAndDsigCompatOfCompatibleData
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.GenusMassVolumes

open Formalism.BasicNotions Formalism.MainNotions.StandardLattice Finset

theorem ncPairs_card_le {N : ℕ} (s : Fin N → Bool) :
    (∑ a : Fin N, (univ.filter (fun b : Fin N => a < b ∧ s a ≠ s b)).card) ≤ nPlus s * nMinus s := by
  classical
  have h1 : (∑ a : Fin N, (univ.filter (fun b : Fin N => a < b ∧ s a ≠ s b)).card) =
      ((univ ×ˢ univ).filter (fun x : Fin N × Fin N => x.1 < x.2 ∧ s x.1 ≠ s x.2)).card := by
    rw [Finset.card_filter, Finset.sum_product]
    simp only [Finset.card_filter]
  rw [h1]
  calc ((univ ×ˢ univ).filter (fun x : Fin N × Fin N => x.1 < x.2 ∧ s x.1 ≠ s x.2)).card
      ≤ ((univ.filter fun a => s a = true) ×ˢ (univ.filter fun a => s a = false)).card := by
        refine Finset.card_le_card_of_injOn
          (fun x => if s x.1 = true then (x.1, x.2) else (x.2, x.1)) ?_ ?_
        · intro x hx
          simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and,
            Finset.mem_coe] at hx ⊢
          cases h1 : s x.1 <;> cases h2 : s x.2 <;> simp_all
        · intro x hx y hy hxy
          simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_product, Finset.mem_univ,
            true_and] at hx hy
          obtain ⟨x1, x2⟩ := x
          obtain ⟨y1, y2⟩ := y
          dsimp only at hx hy hxy
          cases h1 : s x1 <;> cases h2 : s y1 <;> simp only [h1, h2, Bool.false_eq_true, if_false,
            if_true, Prod.mk.injEq] at hxy
          · rw [hxy.1, hxy.2]
          · exact absurd (hxy.1 ▸ hxy.2 ▸ hx.1 : y2 < y1) (lt_asymm hy.1)
          · exact absurd (hxy.1 ▸ hxy.2 ▸ hx.1 : y2 < y1) (lt_asymm hy.1)
          · rw [hxy.1, hxy.2]
    _ = nPlus s * nMinus s := by
        rw [Finset.card_product]
        rfl

private theorem sub_le_lamAbs' {N : ℕ} (lam : Fin N → ℝ) (a b : Fin N) :
    lam a - lam b ≤ lamAbs lam := by
  unfold lamAbs
  calc lam a - lam b ≤ |lam a - lam b| := le_abs_self _
    _ ≤ ⨆ b' : Fin N, |lam a - lam b'| :=
        le_ciSup (f := fun b' : Fin N => |lam a - lam b'|) (Set.finite_range _).bddAbove b
    _ ≤ ⨆ a' : Fin N, ⨆ b' : Fin N, |lam a' - lam b'| :=
        le_ciSup (f := fun a' : Fin N => ⨆ b' : Fin N, |lam a' - lam b'|) (Set.finite_range _).bddAbove a

theorem lamAbs_ge_one {N : ℕ} (lam : Fin N → ℝ) (h : Formalism.QuantumDeterminants.IsHCParam lam) (hN : 2 ≤ N) :
    1 ≤ lamAbs lam := by
  obtain ⟨hanti, hint⟩ := h
  set i0 : Fin N := ⟨0, by omega⟩
  set i1 : Fin N := ⟨1, by omega⟩
  have h01 : i0 < i1 := by simp [i0, i1, Fin.lt_def]
  obtain ⟨m0, hm0⟩ := hint i0
  obtain ⟨m1, hm1⟩ := hint i1
  have hlt := hanti h01
  have hd : lam i0 - lam i1 = ((m0 - m1 : ℤ) : ℝ) := by
    push_cast
    linarith
  have hpos : (0 : ℤ) < m0 - m1 := by
    have : (0 : ℝ) < ((m0 - m1 : ℤ) : ℝ) := by rw [← hd]; linarith
    exact_mod_cast this
  have h1 : (1 : ℝ) ≤ ((m0 - m1 : ℤ) : ℝ) := by
    have : (1 : ℤ) ≤ m0 - m1 := by omega
    exact_mod_cast this
  calc (1 : ℝ) ≤ ((m0 - m1 : ℤ) : ℝ) := h1
    _ = lam i0 - lam i1 := hd.symm
    _ ≤ lamAbs lam := sub_le_lamAbs' lam i0 i1

theorem sub_le_lamAbs {N : ℕ} (lam : Fin N → ℝ) (a b : Fin N) : lam a - lam b ≤ lamAbs lam := by
  exact sub_le_lamAbs' lam a b

theorem facProd_mul_le (p q : ℕ) : facProd p * facProd q ≤ facProd (p + q) := by
  unfold facProd
  rw [Finset.prod_range_add]
  apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg fun _ _ => by positivity)
  apply Finset.prod_le_prod (fun _ _ => by positivity)
  intro j _
  exact_mod_cast Nat.factorial_le (by omega)

private theorem prod_sub_of_lt_eq_facProd (N : ℕ) :
    ∏ a : Fin N, ∏ b ∈ univ.filter (fun b : Fin N => a < b), (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) =
      facProd N := by
  have inner : ∀ a : Fin N, ∏ b ∈ univ.filter (fun b : Fin N => a < b),
      (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) = (((N - 1 - (a : ℕ)).factorial : ℕ) : ℝ) := by
    intro a
    rw [Finset.prod_filter]
    have e : ∀ b : Fin N, (if a < b then (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) else 1) =
        (fun k : ℕ => if (a : ℕ) < k then ((k : ℝ) - ((a : ℕ) : ℝ)) else 1) (b : ℕ) := fun b => by
      simp only [Fin.lt_iff_val_lt_val]
    rw [Finset.prod_congr rfl fun b _ => e b,
      Fin.prod_univ_eq_prod_range (fun k : ℕ => if (a : ℕ) < k then ((k : ℝ) - ((a : ℕ) : ℝ)) else 1) N,
      ← Finset.prod_filter]
    have hI : (range N).filter (fun k => (a : ℕ) < k) = Ico ((a : ℕ) + 1) N := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
      omega
    rw [hI, Finset.prod_Ico_eq_prod_range]
    have e2 : ∀ j ∈ range (N - ((a : ℕ) + 1)),
        ((((a : ℕ) + 1 + j : ℕ) : ℝ) - ((a : ℕ) : ℝ)) = ((j + 1 : ℕ) : ℝ) := by
      intro j _
      push_cast
      ring
    rw [Finset.prod_congr rfl e2, ← Nat.cast_prod, Finset.prod_range_add_one_eq_factorial,
      show N - ((a : ℕ) + 1) = N - 1 - (a : ℕ) by omega]
  rw [Finset.prod_congr rfl fun a _ => inner a,
    Fin.prod_univ_eq_prod_range (fun i => (((N - 1 - i).factorial : ℕ) : ℝ)) N]
  unfold facProd
  exact Finset.prod_range_reflect (fun i => ((i.factorial : ℕ) : ℝ)) N

theorem fdegHC_le_dTau {N : ℕ} (s : Fin N → Bool) (lam : Fin N → ℝ) (hlam : Formalism.QuantumDeterminants.IsHCParam lam) :
    Formalism.QuantumDeterminants.fdegHC lam ≤ dTau s lam * lamAbs lam ^ (nPlus s * nMinus s) := by
  classical
  have hanti := hlam.1
  have hL0 : 0 ≤ lamAbs lam := abs_param_sup_nonneg lam
  have hpos : ∀ a b : Fin N, a < b → 0 < lam a - lam b := fun a b h => sub_pos.2 (hanti h)
  have hrho : ∀ a b : Fin N, a < b → s a = s b → lam a - lam b ≤ (lam a + rhoN s a) - (lam b + rhoN s b) := by
    intro a b h hs
    have := rho_sub_eq_card_opposite s a b h hs
    have h0 : (0 : ℝ) ≤ ((univ.filter fun c : Fin N => a < c ∧ c < b ∧ s c ≠ s a).card : ℝ) :=
      Nat.cast_nonneg _
    linarith
  have hnum : (∏ a : Fin N, ∏ b ∈ univ.filter (fun b : Fin N => a < b), |lam a - lam b|) ≤
      (∏ a : Fin N, ∏ b ∈ univ.filter (fun b : Fin N => a < b ∧ s a = s b),
        ((lam a + rhoN s a) - (lam b + rhoN s b))) *
        lamAbs lam ^ (∑ a : Fin N, (univ.filter (fun b : Fin N => a < b ∧ s a ≠ s b)).card) := by
    rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod (fun a _ => Finset.prod_nonneg fun b _ => abs_nonneg _) fun a _ => ?_
    rw [← Finset.prod_filter_mul_prod_filter_not (univ.filter fun b : Fin N => a < b)
      (fun b => s a = s b), Finset.filter_filter, Finset.filter_filter]
    refine mul_le_mul ?_ ?_ (Finset.prod_nonneg fun b _ => abs_nonneg _)
      (Finset.prod_nonneg fun b hb => ?_)
    · refine Finset.prod_le_prod (fun b _ => abs_nonneg _) fun b hb => ?_
      have h := (Finset.mem_filter.1 hb).2
      rw [abs_of_pos (hpos a b h.1)]
      exact hrho a b h.1 h.2
    · rw [← Finset.prod_const]
      refine Finset.prod_le_prod (fun b _ => abs_nonneg _) fun b hb => ?_
      have h := (Finset.mem_filter.1 hb).2
      rw [abs_of_pos (hpos a b h.1)]
      exact sub_le_lamAbs lam a b
    · have h := (Finset.mem_filter.1 hb).2
      have := hpos a b h.1
      have := hrho a b h.1 h.2
      linarith
  have hcount := ncPairs_card_le s
  have hpq : lamAbs lam ^ (∑ a : Fin N, (univ.filter (fun b : Fin N => a < b ∧ s a ≠ s b)).card) ≤
      lamAbs lam ^ (nPlus s * nMinus s) := by
    by_cases hN : 2 ≤ N
    · exact pow_le_pow_right₀ (lamAbs_ge_one lam hlam hN) hcount
    · have h0 : nPlus s * nMinus s = 0 := by
        by_contra hne
        have hP : 0 < nPlus s := Nat.pos_of_ne_zero fun h => hne (by simp [h])
        have hM : 0 < nMinus s := Nat.pos_of_ne_zero fun h => hne (by simp [h])
        obtain ⟨a, ha⟩ := Finset.card_pos.1 hP
        obtain ⟨b, hb⟩ := Finset.card_pos.1 hM
        have ha' := (Finset.mem_filter.1 ha).2
        have hb' := (Finset.mem_filter.1 hb).2
        have hab : a ≠ b := fun h => by rw [h, hb'] at ha'; exact Bool.noConfusion ha'
        have := a.isLt
        have := b.isLt
        have : a.val ≠ b.val := fun h => hab (Fin.ext h)
        omega
      have h1 : (∑ a : Fin N, (univ.filter (fun b : Fin N => a < b ∧ s a ≠ s b)).card) = 0 := by
        omega
      rw [h0, h1]
  have hNpq : nPlus s + nMinus s = N := by
    unfold nPlus nMinus
    have := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin N)))
      (fun a : Fin N => s a = true)
    simpa using this
  have hFF : 0 < facProd (nPlus s) * facProd (nMinus s) := mul_pos (factorial_product_pos _) (factorial_product_pos _)
  have hFle : facProd (nPlus s) * facProd (nMinus s) ≤ facProd N := by
    have := facProd_mul_le (nPlus s) (nMinus s)
    rwa [hNpq] at this
  have hSame : 0 ≤ ∏ a : Fin N, ∏ b ∈ univ.filter (fun b : Fin N => a < b ∧ s a = s b),
      ((lam a + rhoN s a) - (lam b + rhoN s b)) := by
    refine Finset.prod_nonneg fun a _ => Finset.prod_nonneg fun b hb => ?_
    have h := (Finset.mem_filter.1 hb).2
    have := hpos a b h.1
    have := hrho a b h.1 h.2
    linarith
  have hFN : 0 < facProd N := factorial_product_pos N
  unfold Formalism.QuantumDeterminants.fdegHC dTau
  rw [prod_sub_of_lt_eq_facProd]
  calc (∏ a : Fin N, ∏ b ∈ univ.filter (fun b : Fin N => a < b), |lam a - lam b|) / facProd N
      ≤ ((∏ a : Fin N, ∏ b ∈ univ.filter (fun b : Fin N => a < b ∧ s a = s b),
          ((lam a + rhoN s a) - (lam b + rhoN s b))) * lamAbs lam ^ (nPlus s * nMinus s)) / facProd N := by
        apply div_le_div_of_nonneg_right _ hFN.le
        exact hnum.trans (mul_le_mul_of_nonneg_left hpq hSame)
    _ ≤ ((∏ a : Fin N, ∏ b ∈ univ.filter (fun b : Fin N => a < b ∧ s a = s b),
          ((lam a + rhoN s a) - (lam b + rhoN s b))) * lamAbs lam ^ (nPlus s * nMinus s)) /
          (facProd (nPlus s) * facProd (nMinus s)) :=
        div_le_div_of_nonneg_left (mul_nonneg hSame (pow_nonneg hL0 _)) hFF hFle
    _ = _ := by ring

theorem fdegHC_nonneg {N : ℕ} (lam : Fin N → ℝ) (hlam : Formalism.QuantumDeterminants.IsHCParam lam) :
    0 ≤ Formalism.QuantumDeterminants.fdegHC lam := by
  unfold Formalism.QuantumDeterminants.fdegHC
  refine div_nonneg (Finset.prod_nonneg fun a _ => Finset.prod_nonneg fun b _ => abs_nonneg _)
    (Finset.prod_nonneg fun a _ => Finset.prod_nonneg fun b hb => ?_)
  have := (Finset.mem_filter.1 hb).2
  rw [sub_nonneg, Nat.cast_le]
  exact this.le

theorem theorem_three_all_unitary (D : D7) (C3 : ℝ) (hC3 : 1 ≤ C3) (hc : cdScaleTie D) (hHC : HCFormalDegree D)
    (hT : FamilyMassLastLine D) : RepresentationDimensionGeneral D C3 := by
  unfold Formalism.MainNotions.StandardLattice.RepresentationDimensionGeneral
  intro N ε lam ep0 h0 H _ _ σ w p q hlam hgap hexp hep hh hDS hw
  haveI : CompleteSpace H := hDS.1
  have hF := hHC hc N ε lam hlam H σ w hDS hw
  rw [hF]
  have hF0 := fdegHC_nonneg lam hlam
  have hep0 : 0 ≤ ep0 := le_trans (Real.exp_pos _).le hexp
  refine ⟨by nlinarith, ?_⟩
  have hdim := hT N ε lam hlam H σ hDS
  have hp : p = (nPlus ε : ℝ) := rfl
  have hq : q = (nMinus ε : ℝ) := rfl
  have hk : p * q = ((nPlus ε * nMinus ε : ℕ) : ℝ) := by rw [hp, hq]; push_cast; ring
  have hd0 : (0 : ℝ) ≤ (Module.finrank ℂ (MainNotions.S.lowKSub ε lam σ) : ℝ) := Nat.cast_nonneg _
  rw [hk, Real.rpow_natCast]
  calc Formalism.QuantumDeterminants.fdegHC lam ≤ dTau ε lam * lamAbs lam ^ (nPlus ε * nMinus ε) :=
        fdegHC_le_dTau ε lam hlam
    _ = (Module.finrank ℂ (MainNotions.S.lowKSub ε lam σ) : ℝ) * lamAbs lam ^ (nPlus ε * nMinus ε) := by
        simp only [hdim.2]
    _ ≤ 4 * (Module.finrank ℂ (MainNotions.S.lowKSub ε lam σ) : ℝ) *
        (C3 * p * q * N * lamAbs lam) ^ (nPlus ε * nMinus ε) := by
        rcases Nat.eq_zero_or_pos (nPlus ε * nMinus ε) with hk0 | hk0
        · rw [hk0, pow_zero, pow_zero]
          linarith
        · have hP : 0 < nPlus ε := Nat.pos_of_ne_zero fun h => by simp [h] at hk0
          have hM : 0 < nMinus ε := Nat.pos_of_ne_zero fun h => by simp [h] at hk0
          obtain ⟨a, ha⟩ := Finset.card_pos.1 hP
          obtain ⟨b, hb⟩ := Finset.card_pos.1 hM
          have ha' := (Finset.mem_filter.1 ha).2
          have hb' := (Finset.mem_filter.1 hb).2
          have hab : a ≠ b := fun h => by rw [h, hb'] at ha'; exact Bool.noConfusion ha'
          have hN : 2 ≤ N := by
            have := a.isLt
            have := b.isLt
            have : a.val ≠ b.val := fun h => hab (Fin.ext h)
            omega
          have hL := lamAbs_ge_one lam hlam hN
          have hp1 : (1 : ℝ) ≤ p := by rw [hp]; exact_mod_cast hP
          have hq1 : (1 : ℝ) ≤ q := by rw [hq]; exact_mod_cast hM
          have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
          have hc1 : 1 ≤ C3 * p * q * N := by
            have h1 : 1 ≤ C3 * p := by nlinarith
            have h2 : 1 ≤ C3 * p * q := by nlinarith
            nlinarith
          have hX : lamAbs lam ≤ C3 * p * q * N * lamAbs lam := by nlinarith
          have hpow := pow_le_pow_left₀ (by linarith) hX (nPlus ε * nMinus ε)
          have hpos : 0 ≤ lamAbs lam ^ (nPlus ε * nMinus ε) := by positivity
          nlinarith

end Formalism.L2.GlobalTheoryTheory.GenusMassVolumes

end
