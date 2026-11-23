import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PFlagIntProjection
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial Equiv

namespace BlockAltUnique

theorem sum_range_card_le (S : Finset ℕ) :
    ∑ x ∈ Finset.range S.card, x ≤ ∑ x ∈ S, x ∧
      ((∃ x ∈ S, S.card ≤ x) → ∑ x ∈ Finset.range S.card, x < ∑ x ∈ S, x) := by
  induction S using Finset.induction_on_max with
  | empty => simp
  | insert a s ha ih =>
    have has : a ∉ s := fun h => lt_irrefl a (ha a h)
    have hcard : s.card ≤ a := by
      have : s ⊆ Finset.range a := fun x hx => Finset.mem_range.2 (ha x hx)
      simpa using Finset.card_le_card this
    rw [Finset.card_insert_of_notMem has, Finset.sum_insert has, Finset.sum_range_succ]
    have h1 := ih.1
    refine ⟨by omega, fun ⟨x, hx, hxc⟩ => ?_⟩
    rcases Finset.mem_insert.1 hx with rfl | hx
    · omega
    · have := ih.2 ⟨x, hx, by omega⟩
      omega

theorem sum_le_of_injOn {ι : Type*} (B : Finset ι) (f g : ι → ℕ) (hf : Set.InjOn f B)
    (hg : Set.InjOn g B) (hgB : ∀ i ∈ B, g i < B.card) :
    ∑ i ∈ B, g i ≤ ∑ i ∈ B, f i ∧ ((∃ i ∈ B, B.card ≤ f i) → ∑ i ∈ B, g i < ∑ i ∈ B, f i) := by
  classical
  have hgi : B.image g = Finset.range B.card := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hx
      exact Finset.mem_range.2 (hgB i hi)
    · rw [Finset.card_range, Finset.card_image_of_injOn hg]
  have hfc : (B.image f).card = B.card := Finset.card_image_of_injOn hf
  have e1 : ∑ i ∈ B, g i = ∑ x ∈ B.image g, x := (Finset.sum_image (f := fun x => x) hg).symm
  have e2 : ∑ i ∈ B, f i = ∑ x ∈ B.image f, x := (Finset.sum_image (f := fun x => x) hf).symm
  rw [e1, e2, hgi]
  have := sum_range_card_le (B.image f)
  rw [hfc] at this
  exact ⟨this.1, fun ⟨i, hi, hci⟩ => this.2 ⟨f i, Finset.mem_image_of_mem f hi, hci⟩⟩

variable (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ)

omit [Fintype Ψ] [DecidableEq Ψ] in
theorem weylAct_injective (w : Ψ → Perm (Fin N)) : Function.Injective (weylAct Ψ N w) := by
  rintro ⟨a, i⟩ ⟨b, k⟩ h
  simp only [weylAct, Prod.mk.injEq] at h
  obtain ⟨rfl, h⟩ := h
  exact Prod.ext rfl ((w a).injective h)

omit [Fintype Ψ] [DecidableEq Ψ] in
theorem mapDomain_weylAct_apply (w : Ψ → Perm (Fin N)) (b : Ψ × Fin N →₀ ℕ) (τ : Ψ) (i : Fin N) :
    Finsupp.mapDomain (weylAct Ψ N w) b (τ, w τ i) = b (τ, i) :=
  Finsupp.mapDomain_apply (weylAct_injective Ψ N w) b (τ, i)

omit [DecidableEq Ψ] in
theorem rhoBlock_apply (τ : Ψ) (i : Fin N) :
    rhoBlock Ψ N j (τ, i) = if (i : ℕ) < j then j - 1 - (i : ℕ) else N - 1 - (i : ℕ) := by
  simp [rhoBlock]

omit [DecidableEq Ψ] in

theorem rhoBlock_inj (τ : Ψ) (i k : Fin N) (hik : ((i : ℕ) < j ↔ (k : ℕ) < j))
    (h : rhoBlock Ψ N j (τ, i) = rhoBlock Ψ N j (τ, k)) : i = k := by
  have := i.isLt
  have := k.isLt
  apply Fin.ext
  by_cases h1 : (i : ℕ) < j
  · have h2 : (k : ℕ) < j := hik.1 h1
    simp only [rhoBlock_apply, h1, h2, if_true] at h
    omega
  · have h2 : ¬ (k : ℕ) < j := fun h2 => h1 (hik.2 h2)
    simp only [rhoBlock_apply, h1, h2, if_false] at h
    omega

omit [DecidableEq Ψ] in

theorem blockPerm_unique (b : Ψ × Fin N →₀ ℕ) (w w' : Ψ → Perm (Fin N)) (hw : IsBlockPerm Ψ N j w)
    (hw' : IsBlockPerm Ψ N j w') (h : Finsupp.mapDomain (weylAct Ψ N w) b = rhoBlock Ψ N j)
    (h' : Finsupp.mapDomain (weylAct Ψ N w') b = rhoBlock Ψ N j) : w = w' := by
  funext τ
  refine Equiv.ext fun i => ?_
  have e1 := congrArg (fun c => c (τ, w τ i)) h
  have e2 := congrArg (fun c => c (τ, w' τ i)) h'
  simp only [mapDomain_weylAct_apply] at e1 e2
  exact rhoBlock_inj Ψ N j τ _ _ ((hw τ i).trans (hw' τ i).symm) (e1.symm.trans e2)

omit [Fintype Ψ] [DecidableEq Ψ] in
theorem card_low (hj : j ≤ N) : (Finset.univ.filter fun i : Fin N => (i : ℕ) < j).card = j := by
  rw [Fin.card_filter_val_lt]
  omega

omit [Fintype Ψ] [DecidableEq Ψ] in
theorem card_high (hj : j ≤ N) : (Finset.univ.filter fun i : Fin N => ¬ (i : ℕ) < j).card = N - j := by
  have := Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun i : Fin N => (i : ℕ) < j)
  rw [card_low N j hj, Finset.card_univ, Fintype.card_fin] at this
  omega

omit [DecidableEq Ψ] in

theorem bounds (hj : j ≤ N) (b : Ψ × Fin N →₀ ℕ)
    (hinj : ∀ τ (i k : Fin N), ((i : ℕ) < j ↔ (k : ℕ) < j) → b (τ, i) = b (τ, k) → i = k)
    (hdeg : b.degree = (rhoBlock Ψ N j).degree) (τ : Ψ) (i : Fin N) :
    b (τ, i) < if (i : ℕ) < j then j else N - j := by
  by_contra hlt
  push Not at hlt
  set lo := Finset.univ.filter fun i : Fin N => (i : ℕ) < j with hlo_def
  set hi := Finset.univ.filter fun i : Fin N => ¬ (i : ℕ) < j with hhi_def
  have hlo : lo.card = j := card_low N j hj
  have hhi : hi.card = N - j := card_high N j hj
  have split : ∀ f : Fin N → ℕ, ∑ k, f k = ∑ k ∈ lo, f k + ∑ k ∈ hi, f k := fun f =>
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have klo : ∀ σ, ∑ k ∈ lo, rhoBlock Ψ N j (σ, k) ≤ ∑ k ∈ lo, b (σ, k) ∧
      ((∃ k ∈ lo, lo.card ≤ b (σ, k)) → ∑ k ∈ lo, rhoBlock Ψ N j (σ, k) < ∑ k ∈ lo, b (σ, k)) := by
    intro σ
    refine sum_le_of_injOn lo _ _ ?_ ?_ ?_
    · intro x hx y hy hxy
      simp only [hlo_def, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hx hy
      exact hinj σ x y (iff_of_true hx hy) hxy
    · intro x hx y hy hxy
      simp only [hlo_def, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hx hy
      exact rhoBlock_inj Ψ N j σ x y (iff_of_true hx hy) hxy
    · intro k hk
      simp only [hlo_def, Finset.mem_filter, Finset.mem_univ, true_and] at hk
      rw [hlo, rhoBlock_apply, if_pos hk]
      omega
  have khi : ∀ σ, ∑ k ∈ hi, rhoBlock Ψ N j (σ, k) ≤ ∑ k ∈ hi, b (σ, k) ∧
      ((∃ k ∈ hi, hi.card ≤ b (σ, k)) → ∑ k ∈ hi, rhoBlock Ψ N j (σ, k) < ∑ k ∈ hi, b (σ, k)) := by
    intro σ
    refine sum_le_of_injOn hi _ _ ?_ ?_ ?_
    · intro x hx y hy hxy
      simp only [hhi_def, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hx hy
      exact hinj σ x y (iff_of_false hx hy) hxy
    · intro x hx y hy hxy
      simp only [hhi_def, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hx hy
      exact rhoBlock_inj Ψ N j σ x y (iff_of_false hx hy) hxy
    · intro k hk
      simp only [hhi_def, Finset.mem_filter, Finset.mem_univ, true_and] at hk
      have := k.isLt
      rw [hhi, rhoBlock_apply, if_neg hk]
      omega
  have hlt' : ∑ p, rhoBlock Ψ N j p < ∑ p, b p := by
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    refine Finset.sum_lt_sum (fun σ _ => ?_) ⟨τ, Finset.mem_univ _, ?_⟩
    · rw [split, split]
      have := (klo σ).1
      have := (khi σ).1
      omega
    · rw [split, split]
      by_cases h : (i : ℕ) < j
      · rw [if_pos h] at hlt
        have := (klo τ).2 ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩, by rw [hlo]; exact hlt⟩
        have := (khi τ).1
        omega
      · rw [if_neg h] at hlt
        have := (khi τ).2 ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩, by rw [hhi]; exact hlt⟩
        have := (klo τ).1
        omega
  rw [Finsupp.degree_eq_sum, Finsupp.degree_eq_sum] at hdeg
  omega

omit [Fintype Ψ] [DecidableEq Ψ] in

def matchIndex (hj : j ≤ N) (b : Ψ × Fin N →₀ ℕ) (τ : Ψ) (i : Fin N) : Fin N :=
  ⟨if (i : ℕ) < j then j - 1 - b (τ, i) else N - 1 - b (τ, i), by
    have := i.isLt
    split_ifs <;> omega⟩

theorem exists_blockPerm (hj : j ≤ N) (b : Ψ × Fin N →₀ ℕ)
    (hinj : ∀ τ (i k : Fin N), ((i : ℕ) < j ↔ (k : ℕ) < j) → b (τ, i) = b (τ, k) → i = k)
    (hdeg : b.degree = (rhoBlock Ψ N j).degree) :
    ∃ w, IsBlockPerm Ψ N j w ∧ Finsupp.mapDomain (weylAct Ψ N w) b = rhoBlock Ψ N j := by
  have hb := bounds Ψ N j hj b hinj hdeg
  have hf_blk : ∀ τ i, ((matchIndex Ψ N j hj b τ i : ℕ) < j ↔ (i : ℕ) < j) := by
    intro τ i
    have := hb τ i
    have := i.isLt
    simp only [matchIndex]
    split_ifs at * <;> omega
  have hf_rho : ∀ τ i, rhoBlock Ψ N j (τ, matchIndex Ψ N j hj b τ i) = b (τ, i) := by
    intro τ i
    have := hb τ i
    have := i.isLt
    rw [rhoBlock_apply]
    simp only [matchIndex]
    split_ifs at * <;> omega
  have hf_inj : ∀ τ, Function.Injective (matchIndex Ψ N j hj b τ) := by
    intro τ i k hik
    apply hinj τ i k (by rw [← hf_blk τ i, ← hf_blk τ k, hik])
    rw [← hf_rho τ i, ← hf_rho τ k, hik]
  refine ⟨fun τ => Equiv.ofBijective _ (Finite.injective_iff_bijective.1 (hf_inj τ)), fun τ i => hf_blk τ i, ?_⟩
  ext ⟨τ, m⟩
  obtain ⟨i, rfl⟩ := (Finite.injective_iff_bijective.1 (hf_inj τ)).2 m
  have := mapDomain_weylAct_apply Ψ N
    (fun τ => Equiv.ofBijective _ (Finite.injective_iff_bijective.1 (hf_inj τ))) b τ i
  simp only [Equiv.ofBijective_apply] at this
  rw [this, hf_rho]

theorem alt_eq_zero_of_repeat (L : RootPoly Ψ N →ₗ[ℚ] ℚ)
    (hL : ∀ w, IsBlockPerm Ψ N j w → ∀ P, L (rename (weylAct Ψ N w) P) = weylSign Ψ N w * L P)
    (b : Ψ × Fin N →₀ ℕ) (τ : Ψ) (i k : Fin N) (hik : ((i : ℕ) < j ↔ (k : ℕ) < j)) (hne : i ≠ k)
    (hb : b (τ, i) = b (τ, k)) : L (monomial b 1) = 0 := by
  let w : Ψ → Perm (Fin N) := fun σ => if σ = τ then swap i k else 1
  have hwτ : w τ = swap i k := if_pos rfl
  have hwσ : ∀ σ, σ ≠ τ → w σ = 1 := fun σ hσ => if_neg hσ
  have hw : IsBlockPerm Ψ N j w := by
    intro σ m
    by_cases hσ : σ = τ
    · subst hσ
      rw [hwτ, swap_apply_def]
      split_ifs with h1 h2
      · subst h1; exact hik.symm
      · subst h2; exact hik
      · exact Iff.rfl
    · rw [hwσ σ hσ, Perm.one_apply]
  have hsign : weylSign Ψ N w = -1 := by
    unfold weylSign
    rw [Finset.prod_eq_single τ]
    · simp [hwτ, Perm.sign_swap hne]
    · intro σ _ hσ
      simp [hwσ σ hσ]
    · intro h
      exact absurd (Finset.mem_univ τ) h
  have hfix : Finsupp.mapDomain (weylAct Ψ N w) b = b := by
    ext ⟨σ, m⟩
    obtain ⟨m', rfl⟩ := (w σ).surjective m
    rw [mapDomain_weylAct_apply]
    by_cases hσ : σ = τ
    · subst hσ
      rw [hwτ, swap_apply_def]
      split_ifs with h1 h2
      · rw [h1, hb]
      · rw [h2, hb]
      · rfl
    · rw [hwσ σ hσ, Perm.one_apply]
  have := hL w hw (monomial b 1)
  rw [rename_monomial, hfix, hsign] at this
  linarith

theorem blockInt_monomial (b : Ψ × Fin N →₀ ℕ) (a : ℚ) :
    blockInt Ψ N j (monomial b a) = ∑ w ∈ Finset.univ.filter (IsBlockPerm Ψ N j),
      weylSign Ψ N w * (if Finsupp.mapDomain (weylAct Ψ N w) b = rhoBlock Ψ N j then a else 0) := by
  unfold blockInt
  rw [coeff_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [coeff_smul, rename_monomial, coeff_monomial, smul_eq_mul]

theorem blockInt_add (P Q : RootPoly Ψ N) :
    blockInt Ψ N j (P + Q) = blockInt Ψ N j P + blockInt Ψ N j Q := by
  simp only [blockInt, map_add, smul_add, Finset.sum_add_distrib, coeff_add]

theorem monomial_case (hj : j ≤ N) (L : RootPoly Ψ N →ₗ[ℚ] ℚ)
    (hL : ∀ w, IsBlockPerm Ψ N j w → ∀ P, L (rename (weylAct Ψ N w) P) = weylSign Ψ N w * L P)
    (hdeg0 : ∀ b : Ψ × Fin N →₀ ℕ, b.degree ≠ (rhoBlock Ψ N j).degree → L (monomial b 1) = 0)
    (b : Ψ × Fin N →₀ ℕ) :
    L (monomial b 1) = L (monomial (rhoBlock Ψ N j) 1) * blockInt Ψ N j (monomial b 1) := by
  rw [blockInt_monomial]
  by_cases hex : ∃ w, IsBlockPerm Ψ N j w ∧ Finsupp.mapDomain (weylAct Ψ N w) b = rhoBlock Ψ N j
  · obtain ⟨w0, hw0, h0⟩ := hex
    rw [Finset.sum_eq_single w0]
    · have := hL w0 hw0 (monomial b 1)
      rw [rename_monomial, h0] at this
      rw [if_pos h0, this]
      linear_combination (-L (monomial b 1)) * FlagIntProjection.weylSign_mul_self Ψ N w0
    · intro w hw hne
      rw [if_neg, mul_zero]
      intro h
      exact hne (blockPerm_unique Ψ N j b w w0 (Finset.mem_filter.1 hw).2 hw0 h h0)
    · intro h
      exact absurd (Finset.mem_filter.2 ⟨Finset.mem_univ _, hw0⟩) h
  · rw [Finset.sum_eq_zero, mul_zero]
    · by_cases hd : b.degree = (rhoBlock Ψ N j).degree
      · by_cases hinj : ∀ τ (i k : Fin N), ((i : ℕ) < j ↔ (k : ℕ) < j) → b (τ, i) = b (τ, k) → i = k
        · exact absurd (exists_blockPerm Ψ N j hj b hinj hd) hex
        · push Not at hinj
          obtain ⟨τ, i, k, hik, hb, hne⟩ := hinj
          exact alt_eq_zero_of_repeat Ψ N j L hL b τ i k hik hne hb
      · exact hdeg0 b hd
    · intro w hw
      rw [if_neg, mul_zero]
      intro h
      exact hex ⟨w, (Finset.mem_filter.1 hw).2, h⟩

end BlockAltUnique

open BlockAltUnique in

theorem BlockAltUnique.proof : BlockAltUnique.Statement := by
  intro Ψ _ _ N j hj L hL hdeg P
  induction P using MvPolynomial.induction_on' with
  | monomial u a =>
    have e : monomial u a = a • (monomial u 1 : RootPoly Ψ N) := by
      rw [smul_monomial, smul_eq_mul, mul_one]
    have hb : blockInt Ψ N j (monomial u a) = a * blockInt Ψ N j (monomial u 1) := by
      simp only [blockInt_monomial, Finset.mul_sum]
      refine Finset.sum_congr rfl fun w _ => ?_
      split_ifs <;> ring
    rw [hb, e, map_smul, smul_eq_mul, monomial_case Ψ N j hj L hL hdeg u]
    ring
  | add p q hp hq =>
    rw [map_add, blockInt_add, hp, hq, mul_add]

end GroundTheory.Heights₂.Heights.LowerBoundFree
