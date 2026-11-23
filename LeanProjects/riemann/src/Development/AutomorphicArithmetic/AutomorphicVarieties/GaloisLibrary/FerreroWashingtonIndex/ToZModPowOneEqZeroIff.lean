import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.TwSingle

open UpperTheory.V.FW

private theorem toZModPow_one_eq_zero_iff {l : ℕ} [Fact l.Prime] (x : ℤ_[l]) :
    PadicInt.toZModPow 1 x = 0 ↔ ‖x‖ < 1 := by
  rw [PadicInt.norm_lt_one_iff_dvd, ← RingHom.mem_ker, PadicInt.ker_toZModPow,
    Ideal.mem_span_singleton, pow_one]

private theorem exists_root_lift {l : ℕ} [Fact l.Prime] (u : (ZMod (l ^ 1))ˣ) :
    ∃ ζ ∈ rootsOfUnity (Nat.totient (l ^ 1)) ℤ_[l], redU l 1 ζ = u := by
  have hl : l.Prime := Fact.out
  haveI : NeZero (l ^ 1) := ⟨pow_ne_zero _ hl.ne_zero⟩
  haveI : Fact (1 < l ^ 1) := ⟨by rw [pow_one]; exact hl.one_lt⟩
  have ht : Nat.totient (l ^ 1) = l - 1 := by rw [pow_one, Nat.totient_prime hl]
  have hu : u ^ (l - 1) = 1 := by
    rw [← ht, ← ZMod.card_units_eq_totient]
    exact pow_card_eq_one
  have hn : l - 1 ≠ 0 := by have := hl.two_le; omega
  obtain ⟨a, ha⟩ : ∃ a : ℤ_[l], PadicInt.toZModPow 1 a = (u : ZMod (l ^ 1)) :=
    ⟨((u : ZMod (l ^ 1)).val : ℤ_[l]), by simp⟩
  set F : Polynomial ℤ := Polynomial.X ^ (l - 1) - 1 with hF
  have hFa : ‖F.aeval a‖ < 1 := by
    rw [← toZModPow_one_eq_zero_iff]
    have : ((u : ZMod (l ^ 1))) ^ (l - 1) = 1 := by
      rw [← Units.val_pow_eq_pow_val, hu, Units.val_one]
    simp [hF, ha, this]
  have hdF : ‖(Polynomial.derivative F).aeval a‖ = 1 := by
    refine le_antisymm (PadicInt.norm_le_one _) (not_lt.mp fun h => ?_)
    rw [← toZModPow_one_eq_zero_iff] at h
    have hmul : PadicInt.toZModPow 1 ((Polynomial.derivative F).aeval a) =
        ((l - 1 : ℕ) : ZMod (l ^ 1)) * ((u : ZMod (l ^ 1))) ^ (l - 1 - 1) := by
      rw [hF, Polynomial.derivative_sub, Polynomial.derivative_one, sub_zero,
        Polynomial.derivative_X_pow]
      simp [ha]
    have hcast : ((l - 1 : ℕ) : ZMod (l ^ 1)) = -1 := by
      rw [Nat.cast_sub hl.one_le, Nat.cast_one, pow_one, ZMod.natCast_self, zero_sub]
    rw [hmul, hcast, neg_one_mul, neg_eq_zero, ← Units.val_pow_eq_pow_val] at h
    exact Units.ne_zero _ h
  obtain ⟨z, hz, hza, -, -⟩ := hensels_lemma (F := F) (a := a) (by rw [hdF]; simpa using hFa)
  rw [hdF, ← toZModPow_one_eq_zero_iff, map_sub, sub_eq_zero, ha] at hza
  have hz1 : z ^ (l - 1) = 1 := by
    simpa [hF, sub_eq_zero] using hz
  refine ⟨Units.ofPowEqOne z (l - 1) hz1 hn, ?_, ?_⟩
  · rw [ht, mem_rootsOfUnity]
    exact Units.pow_ofPowEqOne _ _
  · exact Units.ext (by simp [redU, hza])

private theorem units_four (u : (ZMod (2 ^ 2))ˣ) : u = 1 ∨ u = -1 := by
  revert u
  decide

theorem UpperTheory.V.FW.teich :
    ∀ (l : ℕ) [Fact l.Prime], Function.Bijective ((redU l (ee l)).comp (WW l).subtype) := by
  intro l _
  have hl : l.Prime := Fact.out
  have hsurj : Function.Surjective ((redU l (ee l)).comp (WW l).subtype) := by
    by_cases h2 : l = 2
    · subst h2
      intro u
      have ht : Nat.totient (2 ^ ee 2) = 2 := by decide
      rcases units_four u with h | h
      · exact ⟨1, by simp [h] <;> rfl⟩
      · refine ⟨⟨-1, ?_⟩, ?_⟩
        · show (-1 : ℤ_[2]ˣ) ∈ rootsOfUnity (Nat.totient (2 ^ ee 2)) ℤ_[2]
          rw [ht, mem_rootsOfUnity]
          simp
        · rw [h]
          exact Units.ext (by simp [redU] <;> rfl)
    · have he : ee l = 1 := if_neg h2
      have key : ∀ u : (ZMod (l ^ 1))ˣ, ∃ a : WW l, (redU l 1) a = u := by
        intro u
        obtain ⟨ζ, hζ, hred⟩ := exists_root_lift u
        exact ⟨⟨ζ, by simpa [WW, he] using hζ⟩, hred⟩
      rw [he]
      intro u
      obtain ⟨a, ha⟩ := key u
      exact ⟨a, ha⟩
  have hfin : Finite (WW l) := by
    show Finite (rootsOfUnity _ ℤ_[l])
    infer_instance
  haveI : NeZero (l ^ ee l) := ⟨pow_ne_zero _ hl.ne_zero⟩
  have hc := card_rootsOfUnity ℤ_[l] (Nat.totient (l ^ ee l))
  refine hsurj.bijective_of_nat_card_le (le_trans hc (le_of_eq ?_))
  rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
