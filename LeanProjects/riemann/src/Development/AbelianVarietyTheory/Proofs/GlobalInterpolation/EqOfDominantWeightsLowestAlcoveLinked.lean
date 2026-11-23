import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodTopBot
import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.WeylDualWeylLatticesAgreeOfLowestAlcove

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc

namespace GlobalTheory.Alc

theorem natCast_eq_le_prime {p n m : ℕ} (hp : 0 < p) (hn : n ≤ p) (hm : m ≤ p)
    (h : (n : ZMod p) = (m : ZMod p)) : n = m ∨ (n = 0 ∧ m = p) ∨ (n = p ∧ m = 0) := by
  have h' : n % p = m % p := (ZMod.natCast_eq_natCast_iff' n m p).1 h
  rcases hn.eq_or_lt with rfl | hn' <;> rcases hm.eq_or_lt with rfl | hm'
  · exact Or.inl rfl
  · rw [Nat.mod_self, Nat.mod_eq_of_lt hm'] at h'
    exact Or.inr (Or.inr ⟨rfl, h'.symm⟩)
  · rw [Nat.mod_self, Nat.mod_eq_of_lt hn'] at h'
    exact Or.inr (Or.inl ⟨h', rfl⟩)
  · rw [Nat.mod_eq_of_lt hn', Nat.mod_eq_of_lt hm'] at h'
    exact Or.inl h'

theorem eq_of_shifted_residues_eq :
    ∀ (p N : ℕ), p.Prime → ∀ (ν μ : Fin N → ℕ), Antitone ν → Antitone μ →
      (∀ h : 0 < N, ν ⟨N - 1, by omega⟩ = 0 ∧ μ ⟨0, h⟩ ≤ ν ⟨0, h⟩ ∧ ν ⟨0, h⟩ + (N - 1) ≤ p) →
      (∀ x : ZMod p, (Finset.univ.filter fun i : Fin N => ((ν i + (N - 1 - i.val) : ℕ) : ZMod p) = x).card
        = (Finset.univ.filter fun i : Fin N => ((μ i + (N - 1 - i.val) : ℕ) : ZMod p) = x).card) →
      μ = ν := by
  intro p N hp ν μ hν hμ h hc
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · funext i; exact i.elim0
  obtain ⟨h1, h2, h3⟩ := h hN
  have hp0 : 0 < p := hp.pos
  let a : Fin N → ℕ := fun i => ν i + (N - 1 - i.val)
  let b : Fin N → ℕ := fun i => μ i + (N - 1 - i.val)
  have hc' : ∀ x : ZMod p, (Finset.univ.filter fun i : Fin N => ((a i : ℕ) : ZMod p) = x).card
      = (Finset.univ.filter fun i : Fin N => ((b i : ℕ) : ZMod p) = x).card := hc
  have ha : StrictAnti a := by
    intro i j hij
    have h4 := hν hij.le
    have h5 : i.val < j.val := hij
    have h6 := j.isLt
    show ν j + (N - 1 - j.val) < ν i + (N - 1 - i.val)
    omega
  have hb : StrictAnti b := by
    intro i j hij
    have h4 := hμ hij.le
    have h5 : i.val < j.val := hij
    have h6 := j.isLt
    show μ j + (N - 1 - j.val) < μ i + (N - 1 - i.val)
    omega
  let z : Fin N := ⟨0, hN⟩
  let l : Fin N := ⟨N - 1, by omega⟩
  have hal : a l = 0 := by
    show ν ⟨N - 1, _⟩ + (N - 1 - (N - 1)) = 0
    rw [h1]; omega
  have haz : a z ≤ p := by
    show ν ⟨0, hN⟩ + (N - 1 - 0) ≤ p
    omega
  have hbz : b z ≤ a z := by
    show μ ⟨0, hN⟩ + (N - 1 - 0) ≤ ν ⟨0, hN⟩ + (N - 1 - 0)
    omega
  have hzle : ∀ i : Fin N, z ≤ i := fun i => Nat.zero_le _
  have hap : ∀ i, a i ≤ p := fun i => (ha.antitone (hzle i)).trans haz
  have hbp : ∀ i, b i ≤ p := fun i => (hb.antitone (hzle i)).trans (hbz.trans haz)

  have two : ∀ i, a i = p → (∃ j, b j = 0) ∧ (∃ j, b j = p) := by
    intro i hi
    have hne : i ≠ l := by
      rintro rfl
      omega
    have h1lt : 1 < (Finset.univ.filter fun i : Fin N => ((a i : ℕ) : ZMod p) = 0).card := by
      refine Finset.one_lt_card.2 ⟨i, ?_, l, ?_, hne⟩
      · simp [hi]
      · simp [hal]
    rw [hc' 0] at h1lt
    obtain ⟨j₁, hj₁, j₂, hj₂, hj⟩ := Finset.one_lt_card.1 h1lt
    have e₁ : ((b j₁ : ℕ) : ZMod p) = ((0 : ℕ) : ZMod p) := by simpa using hj₁
    have e₂ : ((b j₂ : ℕ) : ZMod p) = ((0 : ℕ) : ZMod p) := by simpa using hj₂
    have r₁ := natCast_eq_le_prime hp0 (hbp j₁) hp0.le e₁
    have r₂ := natCast_eq_le_prime hp0 (hbp j₂) hp0.le e₂
    have hbne : b j₁ ≠ b j₂ := fun e => hj (hb.injective e)
    have s₁ : b j₁ = 0 ∨ b j₁ = p := by omega
    have s₂ : b j₂ = 0 ∨ b j₂ = p := by omega
    rcases s₁ with s₁ | s₁ <;> rcases s₂ with s₂ | s₂
    · exact absurd (s₁.trans s₂.symm) hbne
    · exact ⟨⟨j₁, s₁⟩, ⟨j₂, s₂⟩⟩
    · exact ⟨⟨j₂, s₂⟩, ⟨j₁, s₁⟩⟩
    · exact absurd (s₁.trans s₂.symm) hbne

  have sub : ∀ i, ∃ j, b j = a i := by
    intro i
    have hpos : 0 < (Finset.univ.filter fun k : Fin N => ((a k : ℕ) : ZMod p) = (a i : ZMod p)).card :=
      Finset.card_pos.2 ⟨i, by simp⟩
    rw [hc' (a i : ZMod p)] at hpos
    obtain ⟨j, hj⟩ := Finset.card_pos.1 hpos
    have ej : ((b j : ℕ) : ZMod p) = ((a i : ℕ) : ZMod p) := by simpa using hj
    rcases natCast_eq_le_prime hp0 (hbp j) (hap i) ej with e | ⟨e₁, e₂⟩ | ⟨e₁, e₂⟩
    · exact ⟨j, e⟩
    · obtain ⟨k, hk⟩ := (two i e₂).2
      exact ⟨k, hk.trans e₂.symm⟩
    · have hbz' : b z = p := le_antisymm (hbp z) (e₁ ▸ hb.antitone (hzle j))
      have haz' : a z = p := le_antisymm haz (hbz' ▸ hbz)
      obtain ⟨k, hk⟩ := (two z haz').1
      exact ⟨k, hk.trans e₂.symm⟩
  have himg : Finset.univ.image a = Finset.univ.image b := by
    apply Finset.eq_of_subset_of_card_le
    · intro v hv
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hv
      obtain ⟨j, hj⟩ := sub i
      exact Finset.mem_image.2 ⟨j, Finset.mem_univ _, hj⟩
    · rw [Finset.card_image_of_injective _ ha.injective,
        Finset.card_image_of_injective _ hb.injective]
  have hrange : Set.range b = Set.range a := by
    have := congrArg (fun s : Finset ℕ => (s : Set ℕ)) himg
    simpa using this.symm
  have hab : b = a := (StrictAnti.range_inj hb ha).1 hrange
  funext i
  have e : b i = a i := congrFun hab i
  have e' : μ i + (N - 1 - i.val) = ν i + (N - 1 - i.val) := e
  omega

end GlobalTheory.Alc
