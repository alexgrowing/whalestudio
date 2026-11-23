import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GlobSpecOfExists
import Formalism.GradedWeylDivisibility.FinalD
import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PosOkId
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GenMDetNeZeroOfNontrivial

open MvPolynomial NumberField IsDedekindDomain Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.GO GlobalTheory.ValCmp

namespace GlobalTheory.ValCmp

theorem initMinor_mem_dualWeyl_ind (R : Type) [CommRing R] {r n s : ℕ} (hs : s ≤ n) (I : Fin s → Fin r) :
    initMinor R I hs ∈ dualWeyl R r n (fun t => if t.val < s then 1 else 0) := by
  have h := bidetMem R r n 1 (fun _ => s) (fun _ => hs) (fun _ => I)
  have e1 : bideterminant R (fun _ : Fin 1 => s) (fun _ => hs) (fun _ => I) = initMinor R I hs := by
    simp [bideterminant]
  have e2 : (shapeDeg (fun _ : Fin 1 => s) : Fin n → ℕ) = fun t => if t.val < s then 1 else 0 := by
    funext t
    by_cases ht : t.val < s <;> simp [shapeDeg, ht]
  rwa [e1, e2] at h

private lemma one_mem_dualWeyl_zero (R : Type) [CommRing R] (r n : ℕ) :
    (1 : MvPolynomial (Fin r × Fin n) R) ∈ dualWeyl R r n 0 := by
  simp only [dualWeyl, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    AlgHom.toLinearMap_apply, sub_eq_zero, mem_weightedHomogeneousSubmodule]
  exact ⟨isWeightedHomogeneous_one R _, fun l j _ => by rw [map_one, map_one]⟩

private lemma mul_mem_dualWeyl_add (R : Type) [CommRing R] {r n : ℕ} {ν₁ ν₂ : Fin n → ℕ}
    {f g : MvPolynomial (Fin r × Fin n) R} (hf : f ∈ dualWeyl R r n ν₁) (hg : g ∈ dualWeyl R r n ν₂) :
    f * g ∈ dualWeyl R r n (ν₁ + ν₂) := by
  simp only [dualWeyl, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    AlgHom.toLinearMap_apply, sub_eq_zero, mem_weightedHomogeneousSubmodule] at hf hg ⊢
  refine ⟨hf.1.mul hg.1, fun l j hlj => ?_⟩
  rw [map_mul, map_mul, hf.2 l j hlj, hg.2 l j hlj]

theorem prod_mem_dualWeyl_sum (R : Type) [CommRing R] {r n : ℕ} {ι : Type} (S : Finset ι) (w : ι → Fin n → ℕ)
    (g : ι → MvPolynomial (Fin r × Fin n) R) (hg : ∀ k, g k ∈ dualWeyl R r n (w k)) :
    ∏ k ∈ S, g k ∈ dualWeyl R r n (∑ k ∈ S, w k) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using one_mem_dualWeyl_zero R r n
  | insert a S ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact mul_mem_dualWeyl_add R (hg a) ih

theorem exists_cofAct_initMinor (R : Type) [CommRing R] [IsDomain R] {n s : ℕ} (hs : s ≤ n) (I : Fin s → Fin n) :
    ∃ g ∈ dualWeyl R n n (fun t => if 0 < s ∧ t.val < n - s then 1 else 0),
      (genM R n).det ^ (s - 1) * g = cofAct R n (initMinor R I hs) := by
  classical
  rcases Nat.eq_zero_or_pos s with rfl | h1
  · refine ⟨1, ?_, ?_⟩
    · convert one_mem_dualWeyl_zero R n n using 2
      funext t
      simp
    · simp [initMinor]
  by_cases hI : Function.Injective I
  · obtain ⟨σ, hσ⟩ : ∃ σ : Equiv.Perm (Fin n), ∀ a, σ (Fin.castLE hs a) = I a := by
      let e : {x // x ∈ Set.range (Fin.castLE hs)} ≃ {x // x ∈ Set.range I} :=
        (Equiv.ofInjective _ (Fin.castLE_injective hs)).symm.trans (Equiv.ofInjective I hI)
      refine ⟨e.extendSubtype, fun a => ?_⟩
      rw [Equiv.extendSubtype_apply_of_mem e _ ⟨a, rfl⟩]
      simp only [e, Equiv.trans_apply]
      rw [Equiv.ofInjective_symm_apply]
      rfl
    obtain ⟨ε, hε⟩ := cofAct_initMinor R n s hs h1 σ
    have hIσ : (fun a : Fin s => σ (Fin.castLE hs a)) = I := funext hσ
    rw [hIσ] at hε
    refine ⟨(ε : ℤ) • initMinor R (fun a : Fin (n - s) => σ (Fin.rev (Fin.castLE (Nat.sub_le n s) a)))
      (Nat.sub_le n s), ?_, ?_⟩
    · have hm := initMinor_mem_dualWeyl_ind R (Nat.sub_le n s)
        (fun a : Fin (n - s) => σ (Fin.rev (Fin.castLE (Nat.sub_le n s) a)))
      have hw : (fun t : Fin n => if 0 < s ∧ t.val < n - s then 1 else 0) =
          fun t : Fin n => if t.val < n - s then 1 else 0 := by
        funext t
        simp [h1]
      rw [hw]
      exact zsmul_mem hm _
    · rw [hε, mul_smul_comm]
  · refine ⟨0, zero_mem _, ?_⟩
    simp only [Function.Injective, not_forall, exists_prop] at hI
    obtain ⟨a, b, hab, hne⟩ := hI
    have h0 : initMinor R I hs = 0 := by
      unfold initMinor
      exact Matrix.det_zero_of_row_eq hne (by funext q; simp [hab])
    rw [h0, map_zero, mul_zero]

theorem nuDual_shapeDeg {m K : ℕ} (sz : Fin K → ℕ) :
    nuDual (shapeDeg sz : Fin (m + 1) → ℕ) =
      ∑ k, fun t : Fin (m + 1) => if 0 < sz k ∧ t.val < m + 1 - sz k then 1 else 0 := by
  funext t
  have key : ∀ k, ((if t.rev.val < sz k then 1 else 0) +
      (if 0 < sz k ∧ t.val < m + 1 - sz k then 1 else 0) : ℕ) =
        if (0 : Fin (m + 1)).val < sz k then 1 else 0 := by
    intro k
    have := t.isLt
    rw [Fin.val_rev]
    split_ifs <;> (try simp only [Fin.val_zero] at *) <;> omega
  have hsum : ∑ k, (if t.rev.val < sz k then 1 else 0) +
      ∑ k, (if 0 < sz k ∧ t.val < m + 1 - sz k then 1 else 0) =
        ∑ k, (if (0 : Fin (m + 1)).val < sz k then 1 else 0) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => key k
  simp only [nuDual, shapeDeg, Finset.sum_apply, Finset.card_filter]
  omega

private lemma card_filter_fin_val_lt_eq_of_le {N a : ℕ} (h : a ≤ N) :
    (Finset.univ.filter fun i : Fin N => i.val < a).card = a := by
  have e : (Finset.univ.filter fun i : Fin N => i.val < a) = Finset.univ.map (Fin.castLEEmb h) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, Fin.castLEEmb_apply]
    constructor
    · intro hi
      exact ⟨⟨i.val, hi⟩, rfl⟩
    · rintro ⟨j, rfl⟩
      exact j.isLt
  rw [e, Finset.card_map, Finset.card_univ, Fintype.card_fin]

theorem sum_shapeDeg_sub {m K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ m + 1) :
    ∑ i, (shapeDeg sz : Fin (m + 1) → ℕ) i - (shapeDeg sz : Fin (m + 1) → ℕ) 0 = ∑ k, (sz k - 1) := by
  have h1 : ∑ i, (shapeDeg sz : Fin (m + 1) → ℕ) i = ∑ k, sz k := by
    simp only [shapeDeg, Finset.card_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.card_filter]
    exact card_filter_fin_val_lt_eq_of_le (hsz k)
  have h0 : (shapeDeg sz : Fin (m + 1) → ℕ) 0 = ∑ k, (if (0 : Fin (m + 1)).val < sz k then 1 else 0) := by
    simp only [shapeDeg, Finset.card_filter]
  have h2 : ∑ k, (sz k - 1) + ∑ k, (if (0 : Fin (m + 1)).val < sz k then 1 else 0) = ∑ k, sz k := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by
      split_ifs <;> (try simp only [Fin.val_zero] at *) <;> omega
  rw [h1, h0]
  omega

theorem exists_cofRel_dualWeyl : ∀ (R : Type) [CommRing R] [IsDomain R] (m : ℕ) (ν : Fin (m + 1) → ℕ), Antitone ν → ν (Fin.last m) = 0 → ∀ f ∈ dualWeyl R (m + 1) (m + 1) ν, ∃ g ∈ dualWeyl R (m + 1) (m + 1) (nuDual ν), CofRel R m ν f g := by
  intro R _ _ m ν _ _ f hf
  obtain ⟨b, ⟨_, hspan, _⟩, hb⟩ := sSBasis R (m + 1) (m + 1) ν
  rw [← hspan] at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    obtain ⟨K, sz, hsz, I, hsh, -, hbi⟩ := (hb i).2.2
    rw [hbi]
    choose g hg hgeq using fun k => exists_cofAct_initMinor R (hsz k) (I k)
    refine ⟨∏ k, g k, ?_, ?_⟩
    · have hm := prod_mem_dualWeyl_sum R Finset.univ _ g hg
      rwa [← nuDual_shapeDeg sz, hsh] at hm
    · show (genM R (m + 1)).det ^ (∑ i, ν i - ν 0) * ∏ k, g k = cofAct R (m + 1) (bideterminant R sz hsz I)
      rw [← hsh, sum_shapeDeg_sub sz hsz, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib, bideterminant,
        map_prod]
      exact Finset.prod_congr rfl fun k _ => hgeq k
  | zero => exact ⟨0, zero_mem _, by simp [CofRel]⟩
  | add x y _ _ hx hy =>
    obtain ⟨g₁, h₁, e₁⟩ := hx
    obtain ⟨g₂, h₂, e₂⟩ := hy
    refine ⟨g₁ + g₂, add_mem h₁ h₂, ?_⟩
    unfold CofRel at e₁ e₂ ⊢
    rw [mul_add, e₁, e₂, map_add]
  | smul a x _ hx =>
    obtain ⟨g, h, e⟩ := hx
    refine ⟨a • g, Submodule.smul_mem _ a h, ?_⟩
    unfold CofRel at e ⊢
    rw [mul_smul_comm, e, map_smul]

end GlobalTheory.ValCmp
