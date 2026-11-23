import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.UniversalOrdinaryDeterminantRing
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.IsUnitOrIsUnitOfAddOne

open IsLocalRing Polynomial Matrix UpperTheory.V

private theorem UpperTheory.V.Ws.tendsto_pow_prime_pow_one (l : ℕ) [Fact l.Prime] (x : ℤ_[l]) (hx : ¬ IsUnit (x - 1)) :
    Filter.Tendsto (fun n : ℕ => x ^ l ^ n) Filter.atTop (nhds 1) := by
  have hd : (l : ℤ_[l]) ∣ x - 1 :=
    (PadicInt.norm_lt_one_iff_dvd _).mp (PadicInt.mem_nonunits.mp (mem_nonunits_iff.mpr hx))
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hb : ∀ n : ℕ, ‖x ^ l ^ n - 1‖ ≤ ((l : ℝ)⁻¹) ^ (n + 1) := by
    intro n
    obtain ⟨c, hc⟩ := dvd_sub_pow_of_dvd_sub hd n
    rw [one_pow] at hc
    rw [hc, norm_mul, norm_pow, PadicInt.norm_p]
    calc _ ≤ (l : ℝ)⁻¹ ^ (n + 1) * 1 :=
          mul_le_mul_of_nonneg_left (PadicInt.norm_le_one c) (by positivity)
      _ = _ := mul_one _
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have h0 : Filter.Tendsto (fun n : ℕ => ((l : ℝ)⁻¹) ^ (n + 1)) Filter.atTop (nhds 0) := by
    have := tendsto_pow_atTop_nhds_zero_of_lt_one (r := (l : ℝ)⁻¹) (by positivity)
      (inv_lt_one_of_one_lt₀ hl)
    exact this.comp (Filter.tendsto_add_atTop_nat 1)
  exact squeeze_zero (fun n => norm_nonneg _) hb h0

theorem UpperTheory.V.Ws.sign_char_eq_one_of_cyclotomic_sub_one_not_isUnit :
    ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
      (ε : G →* ℤ_[l]ˣ), Continuous ε → ∀ η : G →* ℤˣ, IsOpen (η.ker : Set G) → ε.ker ≤ η.ker →
      ∀ g, ¬ IsUnit ((ε g : ℤ_[l]) - 1) → η g = 1 := by
  intro l _ hl2 G _ _ _ _ ε hε η hopen hker g hg
  rcases Int.units_eq_one_or (η g) with h | h
  · exact h
  exfalso
  have hodd : Odd l := (Fact.out : l.Prime).odd_of_ne_two hl2
  let C : Set G := ((η.ker : Set G))ᶜ
  have hCc : IsCompact C := (isClosed_compl_iff.mpr hopen).isCompact
  let f : G → ℤ_[l] := fun h => (ε h : ℤ_[l])
  have hf : Continuous f := Units.continuous_val.comp hε
  have hK : IsClosed (f '' C) := (hCc.image hf).isClosed
  have hmem : ∀ n : ℕ, f (g ^ l ^ n) ∈ f '' C := by
    intro n
    refine ⟨g ^ l ^ n, ?_, rfl⟩
    show g ^ l ^ n ∉ η.ker
    rw [MonoidHom.mem_ker, map_pow, h, (hodd.pow).neg_one_pow]
    decide
  have hlim : Filter.Tendsto (fun n : ℕ => f (g ^ l ^ n)) Filter.atTop (nhds 1) := by
    have := tendsto_pow_prime_pow_one l (ε g : ℤ_[l]) hg
    refine this.congr fun n => ?_
    simp [f, map_pow]
  have h1 : (1 : ℤ_[l]) ∈ f '' C := hK.mem_of_tendsto hlim (Filter.Eventually.of_forall hmem)
  obtain ⟨k, hkC, hk1⟩ := h1
  apply hkC
  apply hker
  rw [MonoidHom.mem_ker]
  exact Units.ext hk1
