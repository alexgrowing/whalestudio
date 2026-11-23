import Mathlib
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterOverSubfieldRestrictClassFunctionOne
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.FiniteGroupFunctionPairingSelfIrreducibleAlgClos
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.StarVirtualCharacterEqApplyInv
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.VirtualCharactersMulComapConjIndLinear
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.FiniteGroupFunctionPairingEqZeroOfDistinctIrredu
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.VirtualCharacterIrreducibleExpansionNormSq
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IrreducibleOfVirtualCharacterNormOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrrCharOneMulFinsumConjMul
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
namespace GlobalTheory.IrrPi

theorem isChar_of_irr {G : Type} [Group G] {χ : G → ℂ} (h : IsIrrChar ℂ ℂ χ) : IsChar ℂ ℂ χ := by
  obtain ⟨n, ρ, _, h⟩ := h
  exact ⟨n, ρ, h⟩

theorem pair_prod {ι : Type} [Fintype ι] {G : ι → Type} [∀ i, Group (G i)] [∀ i, Finite (G i)]
    (a b : ∀ i, G i → ℂ) :
    pair (fun x : ∀ i, G i => ∏ i, a i (x i)) (fun x => ∏ i, b i (x i)) = ∏ i, pair (a i) (b i) := by
  classical
  have := fun i => Fintype.ofFinite (G i)
  simp only [pair, finsum_eq_sum_of_fintype, Finset.prod_mul_distrib, Nat.card_pi, Nat.cast_prod,
    Finset.prod_inv_distrib, Finset.prod_univ_sum, Fintype.piFinset_univ, Pi.inv_apply]

theorem irr_one {G : Type} [Group G] [Finite G] {χ : G → ℂ} (h : IsIrrChar ℂ ℂ χ) :
    ∃ n : ℕ, n ≠ 0 ∧ χ 1 = n := by
  obtain ⟨n, hn, h0⟩ := (isChar_restrict_conj_one ℂ ℂ G χ (isChar_of_irr h)).2.2
  refine ⟨n, fun h1 => ?_, hn⟩
  have := pair_self_of_isIrrChar_algClosed ℂ G χ h
  rw [h0 h1] at this
  simp [pair] at this

theorem irr_mulSingle {ι : Type} [Fintype ι] [DecidableEq ι] {G : ι → Type} [∀ i, Group (G i)]
    [∀ i, Finite (G i)] {χ : (∀ i, G i) → ℂ} (h : IsIrrChar ℂ ℂ χ) (i : ι) (a : G i) (y : ∀ i, G i)
    (hy : y i = 1) : χ 1 * χ (Pi.mulSingle i a * y) = χ (Pi.mulSingle i a) * χ y := by
  have := Fintype.ofFinite (∀ i, G i)
  have h1 := irrChar_one_mul_finsum_conj_mul _ χ h (Pi.mulSingle i a) y
  have hc := (isChar_restrict_conj_one ℂ ℂ _ χ (isChar_of_irr h)).2.1
  have h2 : ∀ k : ∀ i, G i, χ (k * Pi.mulSingle i a * k⁻¹ * y) = χ (Pi.mulSingle i a * y) := by
    intro k
    rw [← hc (Pi.mulSingle i a * y) (Pi.mulSingle i (k i)⁻¹)]
    congr 1
    funext j
    by_cases hj : j = i
    · subst hj
      simp [hy]
    · simp [Pi.mulSingle_eq_of_ne hj]
  simp only [h2, finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h1
  rw [Nat.card_eq_fintype_card] at h1
  have hN : (Fintype.card (∀ i, G i) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  apply mul_left_cancel₀ hN
  rw [← h1]
  ring

theorem irr_factor {ι : Type} [Fintype ι] [DecidableEq ι] {G : ι → Type} [∀ i, Group (G i)]
    [∀ i, Finite (G i)] {χ : (∀ i, G i) → ℂ} (h : IsIrrChar ℂ ℂ χ) (x : ∀ i, G i) :
    χ x = χ 1 * ∏ i, (χ (Pi.mulSingle i (x i)) / χ 1) := by
  obtain ⟨n, hn, h1⟩ := irr_one h
  have h0 : χ 1 ≠ 0 := by rw [h1]; exact_mod_cast hn
  have key : ∀ s : Finset ι, χ (fun j => if j ∈ s then x j else 1) =
      χ 1 * ∏ i ∈ s, (χ (Pi.mulSingle i (x i)) / χ 1) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.notMem_empty, if_false, Finset.prod_empty, mul_one]
      rfl
    | insert i s hi ih =>
      have e : (fun j => if j ∈ insert i s then x j else 1) =
          Pi.mulSingle i (x i) * (fun j => if j ∈ s then x j else 1) := by
        funext j
        by_cases hj : j = i
        · subst hj
          simp [hi]
        · simp [Pi.mulSingle_eq_of_ne hj, hj]
      have := irr_mulSingle h i (x i) (fun j => if j ∈ s then x j else 1) (by simp [hi])
      rw [e, Finset.prod_insert hi]
      apply mul_left_cancel₀ h0
      rw [this, ih]
      field_simp
  simpa using key Finset.univ

theorem exists_irr_pair_ne {G : Type} [Group G] [Finite G] {φ : G → ℂ} (h : φ ∈ Virt ℂ ℂ G)
    (h1 : φ 1 ≠ 0) : ∃ ψ, IsIrrChar ℂ ℂ ψ ∧ pair φ ψ ≠ 0 := by
  classical
  have := Fintype.ofFinite G
  obtain ⟨c, hc, hφ, -⟩ := virt_expand G φ h
  have hne : c.support.Nonempty := by
    rw [Finsupp.support_nonempty_iff]
    rintro rfl
    rw [hφ] at h1
    simp at h1
  obtain ⟨ψ, hψ⟩ := hne
  refine ⟨ψ, hc ψ hψ, ?_⟩
  have e : pair φ ψ = ∑ χ ∈ c.support, (c χ : ℂ) * pair χ ψ := by
    rw [hφ]
    simp only [pair, finsum_eq_sum_of_fintype, Finsupp.sum, Finset.sum_apply, Pi.smul_apply,
      zsmul_eq_mul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    simp only [Pi.mul_apply, Pi.intCast_apply]
    ring
  rw [e, Finset.sum_eq_single ψ]
  · rw [pair_self_of_isIrrChar_algClosed ℂ G ψ (hc ψ hψ), mul_one]
    exact_mod_cast Finsupp.mem_support_iff.1 hψ
  · intro b hb hbψ
    rw [pair_eq_zero_of_isIrrChar_ne G b ψ (hc b hb) (hc ψ hψ) hbψ, mul_zero]
  · intro h
    exact absurd hψ h

theorem prod_mem_virt {ι : Type} [Fintype ι] {G : ι → Type} [∀ i, Group (G i)]
    [∀ i, Finite (G i)] (ψ : ∀ i, G i → ℂ) (h : ∀ i, ψ i ∈ Virt ℂ ℂ (G i)) :
    (fun x : ∀ i, G i => ∏ i, ψ i (x i)) ∈ Virt ℂ ℂ (∀ i, G i) := by
  classical
  have key : ∀ s : Finset ι, (fun x : ∀ i, G i => ∏ i ∈ s, ψ i (x i)) ∈ Virt ℂ ℂ (∀ i, G i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact AddSubgroup.subset_closure (by simpa using isChar_one ℂ ℂ (∀ i, G i))
    | insert i s hi ih =>
      simp only [Finset.prod_insert hi]
      exact (virt_mul_comap_conj_ind_linear (∀ i, G i)).1 _
        ((virt_mul_comap_conj_ind_linear (G i)).2.1 _ (h i) _ (Pi.evalMonoidHom G i)) _ ih
  exact key _

end GlobalTheory.IrrPi

namespace GlobalTheory
open IrrPi

theorem irrChar_pi_eq_prod : ∀ (ι : Type) [Fintype ι] (G : ι → Type) [∀ i, Group (G i)] [∀ i, Finite (G i)] (χ : (∀ i, G i) → ℂ), IsIrrChar ℂ ℂ χ → ∃ ψ : ∀ i, G i → ℂ, (∀ i, IsIrrChar ℂ ℂ (ψ i)) ∧ ∀ x, χ x = ∏ i, ψ i (x i) := by
  intro ι _ G _ _ χ h
  classical
  obtain ⟨n, hn, h1⟩ := irr_one h
  have h0 : χ 1 ≠ 0 := by rw [h1]; exact_mod_cast hn
  have hφ : ∀ i, ∃ ψ, IsIrrChar ℂ ℂ ψ ∧ pair (fun a : G i => χ (Pi.mulSingle i a)) ψ ≠ 0 := by
    intro i
    refine exists_irr_pair_ne (AddSubgroup.subset_closure
      ((isChar_restrict_conj_one ℂ ℂ _ χ (isChar_of_irr h)).1 _ (MonoidHom.mulSingle G i))) ?_
    simpa using h0
  choose ψ hψ hp using hφ
  refine ⟨ψ, hψ, ?_⟩
  have hV := prod_mem_virt ψ fun i => AddSubgroup.subset_closure (isChar_of_irr (hψ i))
  set Ψ : (∀ i, G i) → ℂ := fun x => ∏ i, ψ i (x i) with hΨ
  have hN : (Nat.card (∀ i, G i) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hnorm : ∑ᶠ g, Ψ g * star (Ψ g) = (Nat.card (∀ i, G i) : ℂ) := by
    have : pair Ψ Ψ = 1 := by
      rw [hΨ, pair_prod]
      exact Finset.prod_eq_one fun i _ => pair_self_of_isIrrChar_algClosed ℂ _ _ (hψ i)
    simp only [star_virt_eq_inv _ Ψ hV]
    unfold pair at this
    field_simp at this
    exact this
  have hpair : pair χ Ψ ≠ 0 := by
    have e : pair χ Ψ = χ 1 * pair (fun x : ∀ i, G i => ∏ i, χ (Pi.mulSingle i (x i)) / χ 1) Ψ := by
      unfold pair
      have := Fintype.ofFinite (∀ i, G i)
      simp only [finsum_eq_sum_of_fintype, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [irr_factor h x]
      ring
    rw [e, hΨ, pair_prod (fun i (a : G i) => χ (Pi.mulSingle i a) / χ 1) ψ]
    refine mul_ne_zero h0 (Finset.prod_ne_zero_iff.2 fun i _ => ?_)
    have e2 : pair (fun a => χ (Pi.mulSingle i a) / χ 1) (ψ i) =
        pair (fun a : G i => χ (Pi.mulSingle i a)) (ψ i) / χ 1 := by
      unfold pair
      have := Fintype.ofFinite (G i)
      simp only [finsum_eq_sum_of_fintype, Finset.mul_sum, Finset.sum_div]
      refine Finset.sum_congr rfl fun x _ => ?_
      ring
    rw [e2]
    exact div_ne_zero (hp i) h0
  rcases (irr_of_norm_one _ Ψ hV hnorm).1 with hI | hI
  · by_contra hne
    exact hpair (pair_eq_zero_of_isIrrChar_ne _ χ Ψ h hI fun e => hne fun x => congrFun e x)
  · exfalso
    choose m hm hm1 using fun i => irr_one (hψ i)
    obtain ⟨k, hk, hk1⟩ := irr_one hI
    have : ((k + ∏ i, m i : ℕ) : ℂ) = 0 := by
      push_cast
      rw [← hk1]
      simp [hΨ, hm1]
    have : k + ∏ i, m i = 0 := by exact_mod_cast this
    omega

end GlobalTheory
