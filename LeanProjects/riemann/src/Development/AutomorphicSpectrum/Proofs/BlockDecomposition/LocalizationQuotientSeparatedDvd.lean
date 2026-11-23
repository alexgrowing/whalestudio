import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.TwistedConjugationNorms.LocalMatchingOfAssemblyHypotheses

noncomputable section

open NumberField IsDedekindDomain Polynomial Matrix
open GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open PositivityTheory.Rg.Bc.ArchbcB.B PositivityTheory.Rg.Bc.ArchbcB.B.M4 PositivityTheory.Rg.Bc.ArchbcB.B.M4.Tw

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.SymmetricIndexRegularity

theorem orderEmb_rev {n m : ℕ} (S : Finset (Fin n)) (h : S.card = m) (hS : ∀ i ∈ S, i.rev ∈ S) (j : Fin m) :
    S.orderEmbOfFin h j.rev = (S.orderEmbOfFin h j).rev := by
  have key : (fun j : Fin m => (S.orderEmbOfFin h j.rev).rev) = S.orderEmbOfFin h := by
    apply Finset.orderEmbOfFin_unique h
    · intro j
      exact hS _ (Finset.orderEmbOfFin_mem S h _)
    · intro i j hij
      exact Fin.rev_lt_rev.mpr ((S.orderEmbOfFin h).strictMono (Fin.rev_lt_rev.mpr hij))
  have := congrFun key j
  rw [← this, Fin.rev_rev]

theorem diff_injective {n : ℕ} {x : Fin n → ℤ} (hx : StrictAnti x) :
    Function.Injective fun i : Fin n => x i - x i.rev := by
  have : StrictAnti fun i : Fin n => x i - x i.rev := by
    intro i j hij
    have h1 := hx hij
    have h2 := hx (Fin.rev_lt_rev.mpr hij)
    show x j - x j.rev < x i - x i.rev
    omega
  exact this.injective

theorem nv_restr {n m : ℕ} (x : Fin n → ℤ) (S : Finset (Fin n)) (h : S.card = m) (hS : ∀ i ∈ S, i.rev ∈ S)
    (j : Fin m) : nv (restr x S h) j = x (S.orderEmbOfFin h j) - x (S.orderEmbOfFin h j).rev := by
  simp only [nv, restr, orderEmb_rev S h hS]

theorem restr_strictAnti {n m : ℕ} {x : Fin n → ℤ} (hx : StrictAnti x) (S : Finset (Fin n)) (h : S.card = m) :
    StrictAnti (restr x S h) :=
  fun _ _ hij => hx ((S.orderEmbOfFin h).strictMono hij)

theorem mem_symIdx {n : ℕ} {mid : Prop} [Decidable mid] {s : Finset (Fin (n / 2))} {i : Fin n} :
    i ∈ symIdx n mid s ↔ (∃ h : i.val < n / 2, (⟨i.val, h⟩ : Fin (n / 2)) ∈ s) ∨
      (∃ h : n - 1 - i.val < n / 2, (⟨n - 1 - i.val, h⟩ : Fin (n / 2)) ∈ s) ∨ (mid ∧ n % 2 = 1 ∧ i.val = n / 2) := by
  simp [symIdx]

theorem symIdx_rev (n : ℕ) (mid : Prop) [Decidable mid] (s : Finset (Fin (n / 2))) :
    ∀ i ∈ symIdx n mid s, i.rev ∈ symIdx n mid s := by
  intro i hi
  have hv : i.rev.val = n - 1 - i.val := by
    have := i.isLt
    rw [Fin.val_rev]; omega
  have hv' : n - 1 - i.rev.val = i.val := by
    have := i.isLt
    omega
  rw [mem_symIdx] at hi ⊢
  rcases hi with ⟨h, hs⟩ | ⟨h, hs⟩ | ⟨hm, ho, he⟩
  · right; left
    refine ⟨by omega, ?_⟩
    simpa only [hv'] using hs
  · left
    refine ⟨by omega, ?_⟩
    simpa only [hv] using hs
  · right; right
    exact ⟨hm, ho, by omega⟩

theorem symIdx_disj (n : ℕ) (m₁ m₂ : Prop) [Decidable m₁] [Decidable m₂] (s : Finset (Fin (n / 2)))
    (hm : n % 2 = 1 → ¬ (m₁ ∧ m₂)) (i : Fin n) (h₁ : i ∈ symIdx n m₁ s) (h₂ : i ∈ symIdx n m₂ sᶜ) : False := by
  have hi := i.isLt
  rw [mem_symIdx] at h₁ h₂
  rcases h₁ with ⟨h, hs⟩ | ⟨h, hs⟩ | ⟨hm₁, ho, he⟩ <;> rcases h₂ with ⟨h', hs'⟩ | ⟨h', hs'⟩ | ⟨hm₂, ho', he'⟩
  · exact (Finset.mem_compl.mp hs') hs
  · omega
  · omega
  · omega
  · exact (Finset.mem_compl.mp hs') hs
  · omega
  · omega
  · omega
  · exact hm ho ⟨hm₁, hm₂⟩

theorem localization_quotient_separated_dvd {F : Type} [Field F] (ord : F → ℤ) {n a b : ℕ} {x : Fin n → ℤ} (hx : StrictAnti x)
    (S₁ S₂ : Finset (Fin n)) (h₁ : S₁.card = a) (h₂ : S₂.card = b) (y₁ : ∀ i ∈ S₁, i.rev ∈ S₁)
    (y₂ : ∀ i ∈ S₂, i.rev ∈ S₂) (hd : ∀ i, i ∈ S₁ → i ∈ S₂ → False) (u₁ : Fin a → F) (u₂ : Fin b → F)
    (hu₁ : ∀ j, ord (u₁ j) = nv (restr x S₁ h₁) j) (hu₂ : ∀ j, ord (u₂ j) = nv (restr x S₂ h₂) j) :
    ((∏ i, (X - C (u₁ i))) * ∏ i, (X - C (u₂ i))).Separable := by
  have hprod : (∏ i, (X - C (u₁ i))) * (∏ i, (X - C (u₂ i))) = ∏ i, (X - C (Sum.elim u₁ u₂ i)) := by
    rw [Fintype.prod_sum_type]; simp
  rw [hprod, separable_prod_X_sub_C_iff]
  have hinj := diff_injective hx
  have e₁ : ∀ i j, u₁ i = u₁ j → i = j := by
    intro i j hij
    have := congrArg ord hij
    rw [hu₁, hu₁, nv_restr x S₁ h₁ y₁, nv_restr x S₁ h₁ y₁] at this
    exact (S₁.orderEmbOfFin h₁).injective (hinj this)
  have e₂ : ∀ i j, u₂ i = u₂ j → i = j := by
    intro i j hij
    have := congrArg ord hij
    rw [hu₂, hu₂, nv_restr x S₂ h₂ y₂, nv_restr x S₂ h₂ y₂] at this
    exact (S₂.orderEmbOfFin h₂).injective (hinj this)
  have e₃ : ∀ i j, u₁ i = u₂ j → False := by
    intro i j hij
    have := congrArg ord hij
    rw [hu₁, hu₂, nv_restr x S₁ h₁ y₁, nv_restr x S₂ h₂ y₂] at this
    have h := hinj this
    refine hd _ (Finset.orderEmbOfFin_mem S₁ h₁ i) ?_
    rw [show S₁.orderEmbOfFin h₁ i = S₂.orderEmbOfFin h₂ j from h]
    exact Finset.orderEmbOfFin_mem S₂ h₂ j
  rintro (i | i) (j | j) hij
  · exact congrArg _ (e₁ _ _ hij)
  · exact (e₃ _ _ hij).elim
  · exact (e₃ _ _ hij.symm).elim
  · exact congrArg _ (e₂ _ _ hij)

theorem main : TwistedDoubleCosetStrictDiagonal → P_asmReg := by
  intro hs1 E _ _ _ hU w hw n a ha b hb ϖ hϖ x hx hc y hy
  obtain ⟨s, -, hs⟩ := Finset.exists_ne_zero_of_sum_ne_zero hy
  by_cases h0 : s.card = a / 2 ∧ sᶜ.card = (n - a) / 2 ∧ a % 2 + (n - a) % 2 = n % 2
  swap
  · exact absurd (dif_neg h0) hs
  rw [dif_pos h0] at hs
  by_cases h1 : (symIdx n (a % 2 = 1) s).card = a
  swap
  · exact absurd (dif_neg h1) hs
  rw [dif_pos h1] at hs
  by_cases h2 : (symIdx n ((n - a) % 2 = 1) sᶜ).card = n - a
  swap
  · exact absurd (dif_neg h2) hs
  rw [dif_pos h2] at hs
  have hd1 : dcos a w (tdiag ϖ (restr x _ h1)) y.1 ≠ 0 := fun h => hs (by rw [h]; simp)
  have hd2 : dcos (n - a) w (tdiag ϖ (restr x _ h2)) y.2 ≠ 0 := fun h => hs (by rw [h]; simp)
  obtain ⟨-, -, u₁, hQ₁, hu₁⟩ := hs1 hU w hw ϖ hϖ a _ (restr_strictAnti hx _ h1) y.1 ⟨1, by simpa using hd1⟩
  obtain ⟨-, -, u₂, hQ₂, hu₂⟩ := hs1 hU w hw ϖ hϖ (n - a) _ (restr_strictAnti hx _ h2) y.2 ⟨1, by simpa using hd2⟩
  rw [hQ₁, hQ₂]
  exact localization_quotient_separated_dvd (fun z => ordL z) hx _ _ h1 h2 (symIdx_rev n _ s) (symIdx_rev n _ sᶜ)
    (symIdx_disj n _ _ s (by have := h0.2.2; omega)) u₁ u₂ (fun j => (hu₁ j).2) (fun j => (hu₂ j).2)

end GlobalTheory.CompanionTheory.SymmetricIndexRegularity
