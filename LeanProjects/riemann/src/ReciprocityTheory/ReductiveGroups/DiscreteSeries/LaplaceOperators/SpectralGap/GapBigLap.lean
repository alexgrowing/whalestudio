import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.SpectralGap.NonvanishingHypotheses
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.SpectralGap.GapNum

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.Lap

open ReciprocityTheory.ChartRestriction.DS

theorem parabolicSign_false_iff (k r : ℕ) (hk : 1 ≤ k) (i : Fin (2 * r + k + 1)) :
    Formalism.MainNotions.CayleySignature.eps48 k r i = false ↔ k ≤ i.val ∧ (i.val - k) % 2 = 0 := by
  unfold Formalism.MainNotions.CayleySignature.eps48
  split_ifs with h1
  · simp; omega
  · simp; omega

theorem noncompactCount_parabolicSign (k r : ℕ) (hk : 1 ≤ k) : qOf (Formalism.MainNotions.CayleySignature.eps48 k r) = r + 1 := by
  unfold qOf
  have hs : (Finset.univ.filter fun a : Fin (2 * r + k + 1) => Formalism.MainNotions.CayleySignature.eps48 k r a = false) =
      Finset.univ.image (fun j : Fin (r + 1) => (⟨k + 2 * j.val, by omega⟩ : Fin (2 * r + k + 1))) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, parabolicSign_false_iff k r hk]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨⟨(i.val - k) / 2, by omega⟩, ?_⟩
      ext; simp only; omega
    · rintro ⟨j, rfl⟩
      simp only
      omega
  rw [hs, Finset.card_image_of_injective]
  · simp
  · intro x y hxy
    simp only [Fin.mk.injEq] at hxy
    ext; omega

theorem compactCount_parabolicSign (k r : ℕ) (hk : 1 ≤ k) :
    pOf (Formalism.MainNotions.CayleySignature.eps48 k r) = 2 * r + k + 1 - (r + 1) := by
  have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin (2 * r + k + 1))))
    (fun a => Formalism.MainNotions.CayleySignature.eps48 k r a = true)
  simp only [Finset.card_univ, Fintype.card_fin, Bool.not_eq_true] at this
  have hq := noncompactCount_parabolicSign k r hk
  unfold qOf at hq
  unfold pOf
  omega

theorem gapBound_parabolicSign (k r : ℕ) (hk : 1 ≤ k) :
    hNeed (Formalism.MainNotions.CayleySignature.eps48 k r) = hNum (2 * r + k + 1) (r + 1) := by
  unfold hNeed hNum
  rw [compactCount_parabolicSign k r hk, noncompactCount_parabolicSign k r hk]
  simp only [Nat.cast_min]

theorem parabolicWeight_sub_succ (k r : ℕ) (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ) (hk : 1 ≤ k)
    (y : Fin (2 * r + k + 1)) (hy : k ≤ y.val) :
    Formalism.MainNotions.CayleySignature.lam48 k r v b ⟨y.val - 1, by omega⟩ - Formalism.MainNotions.CayleySignature.lam48 k r v b y =
      b ⟨y.val - k + 1, by omega⟩ - b ⟨y.val - k, by omega⟩ := by
  unfold Formalism.MainNotions.CayleySignature.lam48
  rw [dif_neg (by simp only; omega), dif_neg (by omega)]
  have e1 : b ⟨y.val - 1 - (k - 1), by omega⟩ = b ⟨y.val - k, by omega⟩ :=
    congrArg b (Fin.ext (by simp only; omega))
  have e2 : b ⟨y.val - (k - 1), by omega⟩ = b ⟨y.val - k + 1, by omega⟩ :=
    congrArg b (Fin.ext (by simp only; omega))
  simp only at e1 e2 ⊢
  rw [e1, e2]; ring

theorem gapAtLeast_parabolicWeight (k r : ℕ) (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ) (hk : 1 ≤ k) (h : ℝ)
    (hanti : StrictAnti (Formalism.MainNotions.CayleySignature.lam48 k r v b)) (hlow : Formalism.MainNotions.CayleySignature.LowGapGe h r b) :
    GapAtLeast (Formalism.MainNotions.CayleySignature.eps48 k r) (Formalism.MainNotions.CayleySignature.lam48 k r v b) h := by
  have key : ∀ x y : Fin (2 * r + k + 1), x < y →
      Formalism.MainNotions.CayleySignature.eps48 k r x ≠ Formalism.MainNotions.CayleySignature.eps48 k r y →
      h ≤ Formalism.MainNotions.CayleySignature.lam48 k r v b x - Formalism.MainNotions.CayleySignature.lam48 k r v b y := by
    intro x y hxy hne
    have hy : k ≤ y.val := by
      by_contra hcon
      apply hne
      have hx : ¬ (Formalism.MainNotions.CayleySignature.eps48 k r x = false) := by
        rw [parabolicSign_false_iff k r hk]; have := Fin.lt_def.mp hxy; omega
      have hy' : ¬ (Formalism.MainNotions.CayleySignature.eps48 k r y = false) := by
        rw [parabolicSign_false_iff k r hk]; omega
      simp only [Bool.not_eq_false] at hx hy'
      rw [hx, hy']
    have hst := parabolicWeight_sub_succ k r v b hk y hy
    have hle : Formalism.MainNotions.CayleySignature.lam48 k r v b ⟨y.val - 1, by omega⟩ ≤ Formalism.MainNotions.CayleySignature.lam48 k r v b x :=
      hanti.antitone (show x ≤ (⟨y.val - 1, by omega⟩ : Fin (2 * r + k + 1)) from by
        rw [Fin.le_def]; have := Fin.lt_def.mp hxy; simp only; omega)
    have hl := hlow ⟨y.val - k, by omega⟩ (by simp only; omega)
    simp only at hl
    linarith
  intro a a' hne
  rcases lt_trichotomy a a' with h1 | h1 | h1
  · exact le_trans (key a a' h1 hne) (le_abs_self _)
  · exact absurd (h1 ▸ rfl) hne
  · rw [abs_sub_comm]; exact le_trans (key a' a h1 (Ne.symm hne)) (le_abs_self _)

theorem gapBig_gapLap : GapBigLapStatement := by
  intro k r z c u v b hS
  obtain ⟨hk, hev, hz, hT, hc, hu, hlam, hint, hhalf, t, ht, htn, ht1801, hgap⟩ := hS
  let g : Fin (2 * r + 1) → ℝ := fun j => b ⟨j.val + 1, by omega⟩ - b ⟨j.val, by omega⟩
  let h : ℝ := Finset.univ.inf' Finset.univ_nonempty g
  have hlow : Formalism.MainNotions.CayleySignature.LowGapGe h r b := by
    intro j hj
    exact Finset.inf'_le g (Finset.mem_univ (⟨j.val, by omega⟩ : Fin (2 * r + 1)))
  have hX : 2 * ((Formalism.MainNotions.CayleySignature.rk48 k r + (2 * r + 2) * t : ℕ) : ℝ) ^ 3 + (t : ℝ) + 3 < h := by
    rw [Finset.lt_inf'_iff]
    intro j _
    exact hgap ⟨j.val, by omega⟩ (by simp only; omega)
  have hN : hNeed (Formalism.MainNotions.CayleySignature.eps48 k r) < h := by
    rw [gapBound_parabolicSign k r hk]
    refine gapNum (2 * r + k + 1) (r + 1) t h (by omega) (by omega) (by omega)
      (by unfold Formalism.MainNotions.CayleySignature.rk48 at htn; omega) ?_
    have e : (2 * r + k + 1 + 2 * (r + 1) * t : ℕ) = Formalism.MainNotions.CayleySignature.rk48 k r + (2 * r + 2) * t := by
      unfold Formalism.MainNotions.CayleySignature.rk48; ring
    rw [e]; exact hX
  exact ⟨h, hk, hev, hz, hT, hc, hu, hlam, hint, hhalf, hlow,
    hlam.1, gapAtLeast_parabolicWeight k r v b hk h hlam.1 hlow, hN⟩

end ReciprocityTheory.ChartRestriction.DS.Lap
