import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.AscSeedOfLocSub
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL1SpectralBounds.CuspOrTwoAlt

open NumberField IsDedekindDomain MeasureTheory Polynomial Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.F UpperTheory.V.Z.Tf.GOne

open PositivityTheory.Rg.Rs.PExpFin in

private theorem cusp_or_exp {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {N : ℕ}
    (V : Submodule ℂ (Sm E N)) (hV : IsDiscrete V) :
    (∃ P : CuspSub E N, P.V = V) ∨ ∃ r, 0 < r ∧ r < N ∧ (ExpV r V).Nonempty := by
  obtain ⟨-, -, -, hDct⟩ := dict_holds E N
  by_cases hex : ∃ r, 0 < r ∧ r < N ∧ ∃ φ ∈ V, An.ctn r φ.1 ≠ 0
  · right
    obtain ⟨r, hr, hrN, φ, hφ, hne⟩ := hex
    obtain ⟨hct, -⟩ := hDct φ (hV.aut φ hφ) r hr hrN
    have hcont : ∀ g, Continuous fun t => An.ctn r φ.1 (aT E N r t * g) := by
      let _ : MeasurableSpace (BlockIx N r → Ad E) := _root_.borel _
      have _ : BorelSpace (BlockIx N r → Ad E) := ⟨rfl⟩
      obtain ⟨μ, 𝓕, hμ, h𝓕, e⟩ := hct
      obtain ⟨F, hF, -⟩ := GlobalTheory.CompanionTheory.CTSmooth.ct_smooth E N r φ (hV.aut φ hφ).left (hV.aut φ hφ).level μ 𝓕 hμ h𝓕
      have e2 : An.ctn r φ.1 = F.1 := e.trans (funext fun g => (hF g).symm)
      intro g
      rw [e2]
      exact PDich.continuous_aT F r g
    obtain ⟨p, hp, hk, hroot⟩ := killPoly_holds (GA E N) (aT E N r) (An.ctn r φ.1) (fun u v => aT_add r u v) hcont
      (finTr_holds E N φ (hV.aut φ hφ) r hr hrN _ hct)
    have hdeg : 0 < p.degree := hp.degree_pos.2 fun h1 => hne (funext fun g => by
      have := hk g
      rw [h1] at this
      simpa [aT_zero] using this)
    obtain ⟨z, hz⟩ := Complex.exists_root hdeg
    obtain ⟨c, -, F, hF, hF0, hFe⟩ := hroot z hz
    exact ⟨r, hr, hrN, c, φ, hφ, An.ctn r φ.1, hct, F, hF, hF0, hFe⟩
  · left
    push Not at hex
    have hcusp : ∀ φ ∈ V, IsCuspForm φ := fun φ hφ => ⟨hV.aut φ hφ, by
      intro r hr hrN inst1 inst2 μ 𝓕 hμ hF g
      obtain rfl : inst1 = _root_.borel _ := inst2.measurable_eq
      obtain ⟨c, -, e⟩ := (hDct φ (hV.aut φ hφ) r hr hrN).2 _ ⟨μ, 𝓕, hμ, hF, rfl⟩
      have := congrFun e g
      rw [hex r hr hrN φ hφ] at this
      simpa [PositivityTheory.Affgl.CT.ct] using this⟩
    exact ⟨⟨V, hcusp, hV.stable, hV.ne_bot, hV.irred⟩, rfl⟩

private theorem pos_of_ascEmb {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {r a d : ℕ}
    {V : Submodule ℂ (Sm E r)} {π : CuspSub E a} (hr : 0 < r) (h : AscEmb V π d) : 0 < a ∧ 0 < d := by
  obtain ⟨hs, -⟩ := h
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hs
  subst hs
  exact ⟨Nat.pos_of_mul_pos_left hr, Nat.pos_of_mul_pos_right hr⟩

private theorem two_of_exp {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {N : ℕ}
    (V : Submodule ℂ (Sm E N)) (hV : IsDiscrete V) (τ : E →+* ℂ) (hτ : RegInt V τ)
    (hne : ∃ r, 0 < r ∧ r < N ∧ (ExpV r V).Nonempty) :
    ∃ (a d : ℕ) (P : CuspSub E a), 1 ≤ a ∧ 2 ≤ d ∧ P.IsUnitary ∧ IsNormalised P ∧ AscEmb V P d := by
  obtain ⟨r, c, lam, hr0, hrN, hc, hlam, hpc, hbd⟩ :=
    PAscAll.exists_extremal (expFin_of dict_holds finTr_holds) expNeg_holds V hV hne
  obtain ⟨s, rfl⟩ : ∃ s, N = r + s := ⟨N - r, by omega⟩
  have hs0 : 0 < s := by omega
  have hd : (0 : ℝ) < (Module.finrank ℚ E : ℝ) := by exact_mod_cast Module.finrank_pos
  have hdC : (Module.finrank ℚ E : ℂ) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
  have hpc' : pE E (r + s) r c = -lam * (r * s) := by rw [hpc]; push_cast; ring
  obtain ⟨T, hT⟩ := slice_of dict_holds finTr_holds E r s hr0 hs0 V hV c hc
  have hL2 := chord_of expTw_holds sqIntCrit_holds E r s hr0 hs0 V c T lam hlam hT hpc' hbd
  obtain ⟨V₁, V₂, hV₁, hV₂, hemb⟩ :=
    proj_of pr_holds sliceTens_holds indMap_holds E r s hr0 hs0 V hV c _ _ T hT hL2
  obtain ⟨m, hm, hnd, hint⟩ := hτ
  obtain ⟨m₁, m₂, hm₁, hm₂, he⟩ := infInd2_holds E r s V V₁ V₂ _ _ hV hV₁ hV₂ hemb τ m hm
  have hτ₁ : RegInt V₁ τ := PAscAll.regInt_of_le hnd hint (he ▸ Multiset.le_add_right _ _) hm₁
  have hτ₂ : RegInt V₂ τ := PAscAll.regInt_of_le hnd hint (he ▸ Multiset.le_add_left _ _) hm₂
  obtain ⟨a₁, d₁, π₁, hu₁, hn₁, h₁⟩ := ascAll_holds E r hr0 V₁ hV₁ τ hτ₁
  obtain ⟨a₂, d₂, π₂, hu₂, hn₂, h₂⟩ := ascAll_holds E s hs0 V₂ hV₂ τ hτ₂
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
  have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
  have hsum : (r : ℂ) * (c / (r * (Module.finrank ℚ E : ℂ))) + s * (-c / (s * (Module.finrank ℚ E : ℂ))) = 0 := by
    field_simp; ring
  have hre : (c / (r * (Module.finrank ℚ E : ℂ))).re < (s : ℝ) / 2 := by
    have e : (r : ℂ) * (Module.finrank ℚ E : ℂ) = (((r : ℝ) * (Module.finrank ℚ E : ℝ) : ℝ) : ℂ) := by push_cast; ring
    have hrR : (0 : ℝ) < r := by exact_mod_cast hr0
    rw [e, Complex.div_ofReal_re, div_lt_iff₀ (mul_pos hrR hd)]
    have h3 : c.re / (Module.finrank ℚ E : ℝ) < (r : ℝ) * s / 2 := by
      have h4 := hpc'
      unfold pE at h4
      push_cast at h4
      nlinarith [mul_pos hlam (mul_pos hrR (show (0 : ℝ) < s by exact_mod_cast hs0))]
    rw [div_lt_iff₀ hd] at h3
    nlinarith
  have hsS : StringStep := stringStep_of PositivityTheory.AdelicQuotientData.jacquetShalika.1 PositivityTheory.AdelicQuotientData.jacquetShalika.2 infInd2_holds
    infAsc_holds satInd2_holds satAsc_holds satHerm_holds gap_holds
  have e₁ := h₁ π₁ (Setoid.refl π₁)
  have e₂ := h₂ π₂ (Setoid.refl π₂)
  obtain ⟨ha₁, hd₁⟩ := pos_of_ascEmb hr0 e₁
  obtain ⟨-, hd₂⟩ := pos_of_ascEmb hs0 e₂
  obtain ⟨hsig, hz₁, hz₂⟩ := hsS E r s hr0 hs0 V V₁ V₂ _ _ hV hV₁ hV₂ hemb τ ⟨m, hm, hnd, hint⟩ hsum hre
    a₁ d₁ a₂ d₂ π₁ π₂ hu₁ hn₁ e₁ hu₂ hn₂ e₂
  obtain ⟨rfl, hq⟩ := Sigma.mk.inj_iff.mp hsig
  have hiso : π₁.Iso π₂ := Quotient.exact (eq_of_heq hq)
  rw [hz₁, hz₂] at hemb
  refine ⟨a₁, d₁ + d₂, π₁, ha₁, by omega, hu₁, hn₁, ?_⟩
  exact stages_of indMap_holds E r s a₁ d₁ d₂ V V₁ V₂ π₁ hV hV₁ hV₂ hemb e₁
    (h₂ π₁ ((CuspSub.setoid E a₁).iseqv.symm hiso))

theorem UpperTheory.V.Z.Tf.GOne.cuspOrTwo :
    CuspOrTwo := by
  intro E _ _ _ N _ V hV τ hτ
  rcases cusp_or_exp V hV with h | hne
  · exact Or.inl h
  · exact Or.inr (two_of_exp V hV τ hτ hne)
