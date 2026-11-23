import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.PosULeIff
import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.PosTLSurj

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.Proposition5Numerics

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords
open Formalism.MainNotions.G.WittFrameLocaliserOrders Formalism.MainNotions.G.symbolGeneratorData

namespace XXb

section Fr

variable {n' r : ℕ} [NeZero n'] {Fr : Frames n' r} {L₁ N₁ : ℕ}

private theorem fr_lt_fr_of_lt (hV : Fr.Valid L₁ N₁) (j : ℤ) :
    ∀ i i', i < i' → i' < r → Fr.fr j i < Fr.fr j i' := by
  intro i i' hii' hi'
  induction i' with
  | zero => omega
  | succ k ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp hii' with h | h
    · exact (ih h (by omega)).trans (hV.2.2.1 j k hi')
    · subst h
      exact hV.2.2.1 j i hi'

private theorem fr_le_fr_of_le (hV : Fr.Valid L₁ N₁) (j : ℤ) (i : ℕ) (hi : i < r) :
    Fr.fr j 0 ≤ Fr.fr j i := by
  rcases Nat.eq_zero_or_pos i with h | h
  · rw [h]
  · exact (fr_lt_fr_of_lt hV j 0 i h hi).le

theorem exists_posU (hV : Fr.Valid L₁ N₁) (hr : 1 ≤ r) (j : ℤ) (N : ℕ) (hN : N = (Fr.LLset j).card) (x : ℤ)
    (hx : x ∈ Fr.letters j) (hW : ¬ Fr.IsW j x) : ∃ u, u < N + r ∧ posU Fr N j u = x := by
  have hlen : ((Fr.LLset j).sort (· ≤ ·)).length = N := by rw [Finset.length_sort, hN]
  simp only [Frames.letters, Finset.mem_filter, Finset.mem_Icc] at hx
  unfold Frames.IsW at hW
  push_neg at hW
  obtain ⟨⟨hx1, hx2⟩, hxT⟩ := hx
  rcases lt_or_ge x (Fr.fr j 0) with hlt | hge
  · have hxL : x ∈ Fr.LLset j := by
      simp only [Frames.LLset, Finset.mem_filter, Finset.mem_Ioo]
      exact ⟨⟨hW, hlt⟩, hxT⟩
    obtain ⟨u, hu, hux⟩ := List.mem_iff_getElem.mp ((Finset.mem_sort (· ≤ ·)).mpr hxL)
    refine ⟨u, by omega, ?_⟩
    unfold posU llPos
    rw [if_pos (by omega), List.getD_eq_getElem _ _ hu, hux]
  · have key : ∃ i, i < r ∧ Fr.fr j i = x := by
      by_contra hne
      push_neg at hne
      have hall : ∀ i, i < r → Fr.fr j i < x := by
        intro i
        induction i with
        | zero => intro h0; exact lt_of_le_of_ne hge (hne 0 h0)
        | succ k ih =>
          intro hk
          have h1 := ih (by omega)
          by_contra h2
          push_neg at h2
          have h3 : x < Fr.fr j (k + 1) := lt_of_le_of_ne h2 (fun h' => hne (k + 1) hk h'.symm)
          exact hV.2.2.2.2.2.1 j k x hk h1 h3 hxT
      have h4 := hall (r - 1) (by omega)
      omega
    obtain ⟨i, hi, hix⟩ := key
    refine ⟨N + i, by omega, ?_⟩
    unfold posU
    rw [if_neg (by omega), Nat.add_sub_cancel_left, hix]

theorem posU_even (hV : Fr.Valid L₁ N₁) (j : ℤ) (N u : ℕ) (h1 : N ≤ u) (h2 : u < N + r) : Even (posU Fr N j u) := by
  unfold posU
  rw [if_neg (by omega)]
  exact (hV.2.2.2.2.1 j (u - N) (by omega)).2

theorem posU_letter (hV : Fr.Valid L₁ N₁) (hr : 1 ≤ r) (j : ℤ) (N : ℕ) (hN : N = (Fr.LLset j).card) (u : ℕ)
    (hu : u ≤ N) : posU Fr N j u ∈ Fr.letters j ∧ ¬ Fr.IsW j (posU Fr N j u) := by
  have hmemLL : ∀ x ∈ Fr.LLset j, x ∈ Fr.letters j ∧ ¬ Fr.IsW j x := by
    intro x hx
    simp only [Frames.LLset, Finset.mem_filter, Finset.mem_Ioo] at hx
    refine ⟨?_, ?_⟩
    · simp only [Frames.letters, Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨?_, ?_⟩, hx.2⟩
      · exact (fr_le_fr_of_le hV (j - 1) (r - 1) (by omega)).trans hx.1.1.le
      · exact hx.1.2.le.trans (fr_le_fr_of_le hV j (r - 1) (by omega))
    · unfold Frames.IsW
      push_neg
      exact hx.1.1
  unfold posU
  rcases Nat.lt_or_ge u N with hu' | hu'
  · rw [if_pos hu']
    apply hmemLL
    unfold llPos
    have hlen : u < ((Fr.LLset j).sort (· ≤ ·)).length := by rw [Finset.length_sort]; omega
    rw [List.getD_eq_getElem _ _ hlen]
    exact (Finset.mem_sort _).mp (List.getElem_mem _)
  · have hu'' : u = N := le_antisymm hu hu'
    rw [if_neg (by omega), hu'', Nat.sub_self]
    have hg := hV.2.2.2.1 (j - 1)
    rw [sub_add_cancel] at hg
    refine ⟨?_, ?_⟩
    · simp only [Frames.letters, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨(fr_le_fr_of_le hV (j - 1) (r - 1) (by omega)).trans hg.le, fr_le_fr_of_le hV j (r - 1) (by omega)⟩,
        (hV.2.2.2.2.1 j 0 (by omega)).1⟩
    · unfold Frames.IsW
      push_neg
      exact hg

end Fr

section Th

variable {n' r : ℕ} [NeZero n'] (Fr : Frames n' r) (p : ℕ) (deg : Fin n' → ℕ) (Y : ℝ) (k : ℕ) (mS : ℕ)
  {J : ℕ} (nL : ZMod J → ℕ) (K : ℕ) [NeZero K] (ka : ZMod J → ℕ → Fin K → ℤ) (j : ZMod J) (u : ℕ)

theorem th_ge_B : Bo p Fr deg (segZ j) (posU Fr (nL j) (segZ j) u) / 2 ≤ thStar Fr p deg Y k mS nL K ka j u := by
  unfold thStar
  exact le_max_left _ _

theorem threshold_ge_even_position (h : Even (posU Fr (nL j) (segZ j) u)) :
    (ka j (u + 1) 0 : ℝ) + mS + slU Fr p deg Y k nL j u ≤ thStar Fr p deg Y k mS nL K ka j u := by
  unfold thStar slU
  dsimp only
  rw [if_pos h]
  exact le_max_of_le_right (le_max_left _ _)

theorem threshold_ge_odd_position (h : ¬ Even (posU Fr (nL j) (segZ j) u)) :
    (ka j u 0 : ℝ) + mS + slU Fr p deg Y k nL j (u + 1) ≤ thStar Fr p deg Y k mS nL K ka j (u + 1) := by
  unfold thStar slU
  dsimp only
  have hc : 1 ≤ u + 1 ∧ ¬ Even (posU Fr (nL j) (segZ j) u) := ⟨by omega, h⟩
  rw [add_tsub_cancel_right, if_pos hc]
  exact le_max_of_le_right (le_max_right _ _)

end Th

theorem int_le_val {z : ℤ} {t : ℝ} {v : WithTop ℤ} (h1 : (z : ℝ) ≤ t) (h2 : ((⌈t⌉ : ℤ) : WithTop ℤ) ≤ v) :
    ((z : ℤ) : WithTop ℤ) ≤ v := by
  have h3 : z ≤ ⌈t⌉ := by
    have h4 : (z : ℝ) ≤ ((⌈t⌉ : ℤ) : ℝ) := h1.trans (Int.le_ceil t)
    exact_mod_cast h4
  exact (WithTop.coe_le_coe.mpr h3).trans h2

theorem geR_of_ceil {s t : ℝ} {v : WithTop ℤ} (h1 : s ≤ t) (h2 : ((⌈t⌉ : ℤ) : WithTop ℤ) ≤ v) : geR v s := by
  intro z hz
  rw [hz] at h2
  have h3 : ⌈t⌉ ≤ z := WithTop.coe_le_coe.mp h2
  exact h1.trans (Int.ceil_le.mp h3)

theorem ar1 (T a m s c : ℝ) (h1 : a + m + s ≤ T) (h2 : 128 * c ≤ s) : a + 4 * c + m ≤ T - s / 2 - 60 * c := by
  linarith

theorem ar3 (T B s c : ℝ) (h1 : B / 2 ≤ T) (h2 : 128 * c ≤ s) (hc : 0 ≤ c) : B / 2 - s ≤ T - s / 2 - 60 * c := by
  linarith

section Sup

variable {O : Type} [CommRing O] {r K : ℕ}

theorem exists_of_rename {σ τ : Type} (f : σ → τ) (A : MvPolynomial σ O) (a : τ →₀ ℕ) (ha : a ∈ (rename f A).support) :
    ∃ u ∈ A.support, Finsupp.mapDomain f u = a := by
  by_contra hc
  push_neg at hc
  have h0 : (rename f A).coeff a = 0 := MvPolynomial.coeff_rename_eq_zero f A a (fun u hu => by
    by_contra hu0
    exact hc u (MvPolynomial.mem_support_iff.mpr hu0) hu)
  exact (MvPolynomial.mem_support_iff.mp ha) h0

theorem deg_mul (A : MvPolynomial (ℤ × Fin r) O) (B : MvPolynomial (ℤ × Fin K) O) (mm : ℤ × Fin (r + K) →₀ ℕ)
    (hmm : mm ∈ (plEmb O r K A * nmEmb O r K B).support) :
    ∃ ua ∈ A.support, ∃ ub ∈ B.support, ∀ x, (∀ c : Fin r, mm (x, Fin.castAdd K c) = ua (x, c)) ∧
      ∀ c : Fin K, mm (x, Fin.natAdd r c) = ub (x, c) := by
  obtain ⟨a', ha', b', hb', rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul _ _ hmm)
  obtain ⟨ua, hua, rfl⟩ := exists_of_rename (fun v : ℤ × Fin r => (v.1, Fin.castAdd K v.2)) A a' ha'
  obtain ⟨ub, hub, rfl⟩ := exists_of_rename (fun v : ℤ × Fin K => (v.1, Fin.natAdd r v.2)) B b' hb'
  have hinj1 : Function.Injective (fun v : ℤ × Fin r => (v.1, Fin.castAdd K v.2)) := by
    rintro ⟨a1, a2⟩ ⟨b1, b2⟩ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext h.1 (Fin.castAdd_injective _ _ h.2)
  have hinj2 : Function.Injective (fun v : ℤ × Fin K => (v.1, Fin.natAdd r v.2)) := by
    rintro ⟨a1, a2⟩ ⟨b1, b2⟩ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext h.1 (Fin.natAdd_injective _ _ h.2)
  refine ⟨ua, hua, ub, hub, fun x => ⟨fun c => ?_, fun c => ?_⟩⟩
  · have e1 := Finsupp.mapDomain_apply hinj1 ua (x, c)
    simp only at e1
    have e2 : Finsupp.mapDomain (fun v : ℤ × Fin K => (v.1, Fin.natAdd r v.2)) ub (x, Fin.castAdd K c) = 0 := by
      apply Finsupp.mapDomain_notin_range
      rintro ⟨⟨y, d⟩, hyd⟩
      simp only [Prod.mk.injEq] at hyd
      have h5 := congrArg Fin.val hyd.2
      simp only [Fin.coe_natAdd, Fin.coe_castAdd] at h5
      omega
    rw [Finsupp.add_apply, e1, e2, add_zero]
  · have e1 := Finsupp.mapDomain_apply hinj2 ub (x, c)
    simp only at e1
    have e2 : Finsupp.mapDomain (fun v : ℤ × Fin r => (v.1, Fin.castAdd K v.2)) ua (x, Fin.natAdd r c) = 0 := by
      apply Finsupp.mapDomain_notin_range
      rintro ⟨⟨y, d⟩, hyd⟩
      simp only [Prod.mk.injEq] at hyd
      have h5 := congrArg Fin.val hyd.2
      simp only [Fin.coe_natAdd, Fin.coe_castAdd] at h5
      omega
    rw [Finsupp.add_apply, e1, e2, zero_add]

end Sup

end XXb

end Formalism.MainNotions.Proposition5Numerics
