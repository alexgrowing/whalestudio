import Mathlib

namespace ReciprocityTheory.ChartRestriction.G.T0

namespace KrullColonIdeal

variable {R : Type*} [CommRing R]

def colonI (s c : R) : Ideal R where
  carrier := {r | r * c ∈ Ideal.span {s}}
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_ofPred_eq] at *
    rw [add_mul]
    exact Ideal.add_mem _ hx hy
  zero_mem' := by simp
  smul_mem' := by
    intro r x hx
    simp only [Set.mem_ofPred_eq, smul_eq_mul] at *
    rw [mul_assoc]
    exact Ideal.mul_mem_left _ _ hx

theorem mem_colonI {s c r : R} : r ∈ colonI s c ↔ r * c ∈ Ideal.span {s} := Iff.rfl

theorem exists_prime_colon [IsNoetherianRing R] (s a : R) (ha : a ∉ Ideal.span {s}) :
    ∃ b : R, b ∉ Ideal.span {s} ∧ colonI s a ≤ colonI s b ∧
      ∀ q1 q2 : R, q1 * q2 ∈ colonI s b → q1 ∈ colonI s b ∨ q2 ∈ colonI s b := by
  classical
  have hS : ({J : Ideal R | ∃ b : R, b ∉ Ideal.span {s} ∧ colonI s a ≤ colonI s b ∧
      colonI s b = J} : Set (Ideal R)).Nonempty := ⟨colonI s a, a, ha, le_rfl, rfl⟩
  obtain ⟨M, hM, hmax⟩ : ∃ M ∈ ({J : Ideal R | ∃ b : R, b ∉ Ideal.span {s} ∧
      colonI s a ≤ colonI s b ∧ colonI s b = J} : Set (Ideal R)),
      ∀ I ∈ ({J : Ideal R | ∃ b : R, b ∉ Ideal.span {s} ∧
      colonI s a ≤ colonI s b ∧ colonI s b = J} : Set (Ideal R)), ¬ M < I := by
    first
    | exact set_has_maximal_iff_noetherian.mpr inferInstance _ hS
    | exact WellFounded.has_min (wellFounded_submodule_gt R R) _ hS
  obtain ⟨b, hb, hab, rfl⟩ := hM
  refine ⟨b, hb, hab, fun q1 q2 h => ?_⟩
  by_cases h1 : q1 ∈ colonI s b
  · exact Or.inl h1
  · right

    have hle : colonI s b ≤ colonI s (q1 * b) := by
      intro r hr
      rw [mem_colonI] at hr ⊢
      have e : r * (q1 * b) = q1 * (r * b) := by ring
      rw [e]
      exact Ideal.mul_mem_left _ q1 hr
    have hnot : q1 * b ∉ Ideal.span {s} := fun h' => h1 (mem_colonI.2 h')
    have heq : colonI s b = colonI s (q1 * b) := by
      by_contra hne
      exact hmax _ ⟨q1 * b, hnot, hab.trans hle, rfl⟩ (lt_of_le_of_ne hle hne)
    rw [heq, mem_colonI]
    have h' := mem_colonI.1 h
    have e : q2 * (q1 * b) = q1 * q2 * b := by ring
    rw [e]
    exact h'

end KrullColonIdeal

open KrullColonIdeal in

theorem mem_of_mem_heightOne_localizations {R K : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] [Field K] [Algebra R K] [IsFractionRing R K] (x : K)
    (hx : ∀ p : Ideal R, p.IsPrime → p.height = 1 →
      ∃ a s : R, s ∉ p ∧ x * algebraMap R K s = algebraMap R K a) :
    ∃ r : R, algebraMap R K r = x := by
  classical

  obtain ⟨a, b, hb0, hxab⟩ : ∃ a b : R, b ≠ 0 ∧ x * algebraMap R K b = algebraMap R K a := by
    obtain ⟨⟨a, ⟨b, hb⟩⟩, hx'⟩ := IsLocalization.mk'_surjective (nonZeroDivisors R) x
    refine ⟨a, b, nonZeroDivisors.ne_zero hb, ?_⟩
    rw [← hx']
    exact IsLocalization.mk'_spec K a ⟨b, hb⟩
  have hbK : algebraMap R K b ≠ 0 := by
    intro h
    apply hb0
    apply IsFractionRing.injective R K
    rw [h, map_zero]
  by_contra hne
  have ha : a ∉ Ideal.span {b} := by
    intro h
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 h
    apply hne
    refine ⟨r, ?_⟩
    apply mul_right_cancel₀ hbK
    rw [hxab, ← hr, map_mul]
  obtain ⟨c, hc, hac, hprime⟩ := exists_prime_colon b a ha
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hc (Ideal.zero_mem _)
  have hbP : b ∈ colonI b c := mem_colonI.2 (Ideal.mul_mem_right c _ (Ideal.mem_span_singleton_self b))
  have hPne : colonI b c ≠ ⊥ := by
    intro h
    have hb' := hbP
    rw [h, Ideal.mem_bot] at hb'
    exact hb0 hb'
  have hPprime : (colonI b c).IsPrime := by
    refine ⟨?_, fun h => hprime _ _ h⟩
    refine (Ideal.ne_top_iff_one _).2 (fun h1 => hc ?_)
    have h1' := mem_colonI.1 h1
    rwa [one_mul] at h1'

  have key : ∃ q0 ∈ colonI b c, ∃ u : R, u ∉ colonI b c ∧ u * b = q0 * c := by
    by_contra hcon
    push_neg at hcon
    apply hc
    have hint : IsIntegral R (algebraMap R K c / algebraMap R K b) := by
      refine isIntegral_of_smul_mem_submodule
        (Submodule.map (Algebra.linearMap R K) (colonI b c)) ?_ ?_ _ ?_
      · intro hbot
        have hmem : algebraMap R K b ∈ Submodule.map (Algebra.linearMap R K) (colonI b c) :=
          Submodule.mem_map_of_mem hbP
        rw [hbot, Submodule.mem_bot] at hmem
        exact hbK hmem
      · exact (IsNoetherian.noetherian (colonI b c)).map _
      · intro n hn
        obtain ⟨q, hq, rfl⟩ := Submodule.mem_map.1 hn
        obtain ⟨v, hv⟩ := Ideal.mem_span_singleton'.1 (mem_colonI.1 hq)
        have hvP : v ∈ colonI b c := by
          by_contra hv'
          exact hcon q hq v hv' hv
        refine Submodule.mem_map.2 ⟨v, hvP, ?_⟩
        have hv2 : algebraMap R K v * algebraMap R K b = algebraMap R K q * algebraMap R K c := by
          rw [← map_mul, ← map_mul, hv]
        simp only [Algebra.linearMap_apply, smul_eq_mul]
        first
        | (rw [div_mul_eq_mul_div, eq_div_iff hbK]; linear_combination hv2)
        | (field_simp; linear_combination hv2)
        | (field_simp; linear_combination -hv2)
    obtain ⟨r, hr⟩ : ∃ r : R, algebraMap R K r = algebraMap R K c / algebraMap R K b := by
      first
      | exact IsIntegrallyClosed.isIntegral_iff.1 hint
      | exact IsIntegrallyClosed.algebraMap_eq_of_integral hint
    have hrc : r * b = c := by
      apply IsFractionRing.injective R K
      rw [map_mul, hr]
      first
      | exact div_mul_cancel₀ _ hbK
      | field_simp
    exact Ideal.mem_span_singleton'.2 ⟨r, hrc⟩
  obtain ⟨q0, hq0, u, hu, huq⟩ := key
  have huP : ∀ q ∈ colonI b c, u * q ∈ Ideal.span {q0} := by
    intro q hq
    obtain ⟨v, hv⟩ := Ideal.mem_span_singleton'.1 (mem_colonI.1 hq)
    refine Ideal.mem_span_singleton'.2 ⟨v, ?_⟩
    apply mul_right_cancel₀ hc0
    linear_combination (-v) * huq + u * hv

  have hmin : colonI b c ∈ (Ideal.span {q0}).minimalPrimes := by
    refine ⟨⟨hPprime, ?_⟩, fun Q hQ hQP => ?_⟩
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      exact hq0
    · intro q hq
      have huq' : u * q ∈ Q := hQ.2 (huP q hq)
      rcases hQ.1.mem_or_mem huq' with h | h
      · exact absurd (hQP h) hu
      · exact h
  haveI : Submodule.IsPrincipal (Ideal.span {q0}) := ⟨⟨q0, rfl⟩⟩
  have hle1 : (colonI b c).height ≤ 1 :=
    Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {q0}) _ hmin
  have hge1 : (1 : ℕ∞) ≤ (colonI b c).height := by
    unfold Ideal.height
    refine le_iInf₂ (fun J hJ => ?_)
    have hJP : colonI b c ≤ J := hJ.1.2
    have hJne : J ≠ ⊥ := fun h => hPne (eq_bot_iff.2 (h ▸ hJP))
    haveI : J.IsPrime := hJ.1.1
    show 1 ≤ Order.height (⟨J, hJ.1.1⟩ : PrimeSpectrum R)
    rw [ENat.one_le_iff_ne_zero, Ne, Order.height_eq_zero]
    intro hmin
    have hlt : (⟨⊥, inferInstance⟩ : PrimeSpectrum R) < ⟨J, hJ.1.1⟩ := by
      refine lt_of_le_of_ne ?_ ?_
      · first
        | exact (bot_le : (⊥ : Ideal R) ≤ J)
        | exact (PrimeSpectrum.asIdeal_le_asIdeal _ _).1 bot_le
      · intro h
        exact hJne (congrArg PrimeSpectrum.asIdeal h).symm
    exact hmin.not_lt hlt
  have hheight : (colonI b c).height = 1 := le_antisymm hle1 hge1
  obtain ⟨a', s', hs', hs'x⟩ := hx (colonI b c) hPprime hheight
  apply hs'
  apply hac
  rw [mem_colonI]
  refine Ideal.mem_span_singleton'.2 ⟨a', ?_⟩
  apply IsFractionRing.injective R K
  rw [map_mul, map_mul, ← hs'x, ← hxab]
  ring

end ReciprocityTheory.ChartRestriction.G.T0
