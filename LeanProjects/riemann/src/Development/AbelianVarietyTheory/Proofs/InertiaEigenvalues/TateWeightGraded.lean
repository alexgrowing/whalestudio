import Mathlib

namespace GlobalTheory

theorem tate_weight_graded : ∀ {C σ Γ : Type} [Field C] [Group Γ] [MulSemiringAction Γ C] (χ : Γ →* Cˣ),
    (∀ m : ℤ, m ≠ 0 → ∀ a : C, (∀ g : Γ, g • a = ((χ g ^ m : Cˣ) : C) * a) → a = 0) →
    ∀ (w : σ → ℤ) (J : Submodule C (σ →₀ C)),
    (∀ g : Γ, ∀ φ ∈ J, ∃ ψ ∈ J, ∀ m, ψ m = ((χ g ^ w m : Cˣ) : C) * (g • φ m)) →
    ∀ φ ∈ J, ∀ d : ℤ, φ.filter (fun m => w m = d) ∈ J := by
  intro C σ Γ _ _ _ χ hT w J hJ
  classical
  suffices H : ∀ n, ∀ φ ∈ J, φ.support.card = n → ∀ d : ℤ, φ.filter (fun m => w m = d) ∈ J by
    intro φ hφ d; exact H _ φ hφ rfl d
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro φ hφ hn
  have IH : ∀ φ' ∈ J, φ'.support.card < n → ∀ d : ℤ, φ'.filter (fun m => w m = d) ∈ J :=
    fun φ' h1 h2 d => ih _ h2 φ' h1 rfl d
  by_cases h0 : φ = 0
  · subst h0; intro d; rw [Finsupp.filter_zero]; exact J.zero_mem
  obtain ⟨m0, hm0⟩ := Finsupp.support_nonempty_iff.mpr h0
  have hc : φ m0 ≠ 0 := Finsupp.mem_support_iff.mp hm0
  set c := φ m0 with hcdef
  set φ0 : σ →₀ C := c⁻¹ • φ with hφ0def
  have hφ0 : φ0 ∈ J := J.smul_mem _ hφ
  have hsupp0 : φ0.support = φ.support := Finsupp.support_smul_eq (inv_ne_zero hc)
  have h1 : φ0 m0 = 1 := by
    simp only [φ0, Finsupp.smul_apply, smul_eq_mul]; exact inv_mul_cancel₀ hc
  have hφeq : φ = c • φ0 := by
    simp only [φ0, smul_smul, mul_inv_cancel₀ hc, one_smul]
  suffices H0 : ∀ d : ℤ, φ0.filter (fun m => w m = d) ∈ J by
    intro d; rw [hφeq, Finsupp.filter_smul]; exact J.smul_mem _ (H0 d)
  have hcard : φ0.support.card = n := by rw [hsupp0, hn]
  have hm0' : m0 ∈ φ0.support := by rw [Finsupp.mem_support_iff, h1]; exact one_ne_zero
  have hψ : ∀ g : Γ, ∃ ψ ∈ J, ∀ m, ψ m =
      ((χ g ^ (-w m0) : Cˣ) : C) * (((χ g ^ w m : Cˣ) : C) * (g • φ0 m)) - φ0 m := by
    intro g
    obtain ⟨ψ', hψ'J, hψ'⟩ := hJ g φ0 hφ0
    refine ⟨((χ g ^ (-w m0) : Cˣ) : C) • ψ' - φ0, J.sub_mem (J.smul_mem _ hψ'J) hφ0, fun m => ?_⟩
    simp only [Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul, hψ']
  choose ψ hψJ hψm using hψ
  have hψm0 : ∀ g, ψ g m0 = 0 := by
    intro g
    rw [hψm, h1, smul_one, mul_one, ← Units.val_mul, ← zpow_add, neg_add_cancel, zpow_zero,
      Units.val_one, sub_self]
  have hψ0 : ∀ g m, φ0 m = 0 → ψ g m = 0 := by
    intro g m h; rw [hψm, h, smul_zero, mul_zero, mul_zero, sub_zero]
  have hψsupp : ∀ g, (ψ g).support ⊆ φ0.support.erase m0 := by
    intro g m hm
    rw [Finset.mem_erase, Finsupp.mem_support_iff]
    rw [Finsupp.mem_support_iff] at hm
    refine ⟨?_, fun h => hm (hψ0 g m h)⟩
    rintro rfl; exact hm (hψm0 g)
  have hlt : ∀ g, (ψ g).support.card < n := fun g =>
    lt_of_le_of_lt (Finset.card_le_card (hψsupp g)) (hcard ▸ Finset.card_erase_lt_of_mem hm0')
  by_cases hall : ∀ g, ψ g = 0
  · have hw : ∀ m, φ0 m ≠ 0 → w m = w m0 := by
      intro m hm
      by_contra hne
      apply hm
      refine hT (w m0 - w m) (sub_ne_zero.mpr (Ne.symm hne)) (φ0 m) (fun g => ?_)
      have e := hψm g m
      rw [hall g, Finsupp.zero_apply, eq_comm, sub_eq_zero] at e
      have hex : w m0 - w m + -w m0 + w m = 0 := by ring
      conv_rhs => rw [← e]
      rw [← mul_assoc, ← mul_assoc, ← Units.val_mul, ← Units.val_mul, ← zpow_add, ← zpow_add,
        hex, zpow_zero, Units.val_one, one_mul]
    intro d
    by_cases hd : w m0 = d
    · rw [(Finsupp.filter_eq_self_iff _ _).mpr (fun m hm => (hw m hm).trans hd)]; exact hφ0
    · rw [(Finsupp.filter_eq_zero_iff _ _).mpr (fun m hm => by
        by_contra h; exact hd ((hw m h).symm.trans hm))]
      exact J.zero_mem
  · push_neg at hall
    obtain ⟨g, hg⟩ := hall
    obtain ⟨m1, hm1⟩ := Finsupp.support_nonempty_iff.mpr hg
    have hm1' := Finset.mem_of_mem_erase (hψsupp g hm1)
    have hψm1 : ψ g m1 ≠ 0 := Finsupp.mem_support_iff.mp hm1
    set a := φ0 m1 / ψ g m1 with hadef
    set φ' : σ →₀ C := φ0 - a • ψ g with hφ'def
    have hφ'J : φ' ∈ J := J.sub_mem hφ0 (J.smul_mem _ (hψJ g))
    have hφ'supp : φ'.support ⊆ φ0.support.erase m1 := by
      intro m hm
      rw [Finset.mem_erase, Finsupp.mem_support_iff]
      rw [Finsupp.mem_support_iff] at hm
      refine ⟨?_, fun h => hm ?_⟩
      · rintro rfl; apply hm
        simp only [φ', a, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul,
          div_mul_cancel₀ _ hψm1, sub_self]
      · simp only [φ', Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul, h, hψ0 g m h,
          mul_zero, sub_zero]
    have hlt' : φ'.support.card < n :=
      lt_of_le_of_lt (Finset.card_le_card hφ'supp) (hcard ▸ Finset.card_erase_lt_of_mem hm1')
    intro d
    have hdec : φ0 = φ' + a • ψ g := by simp only [φ', sub_add_cancel]
    rw [hdec, Finsupp.filter_add, Finsupp.filter_smul]
    exact J.add_mem (IH _ hφ'J hlt' d) (J.smul_mem _ (IH _ (hψJ g) (hlt g) d))

end GlobalTheory
