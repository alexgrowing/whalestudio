import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
import Development.AbelianVarietyTheory.Definitions.Divisors.ScalesBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GodementSummableHeightRpowRepresentativesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousLeviBlock
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemDoublingSiegelParabolicIffChartMemSiegelUnnStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardUnitaryChartSiegelLeviDetEqStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledSpaceMaximalLevelLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactLevelHeightScalesIsotropicFrameStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittFrameRankLeAndExistsRationalSwapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureHeightShellLeIsotropicFrameQuotientStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicEisensteinSeriesRationalPointsPermuteTeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulLintegralRpowLeOfShellBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SetLIntegralTsumUnfoldOfCosetRepresentativesStatement
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.LeftInvOfIsSection
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledSpaceMaximalLevelLattice
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSelfDualAtSumLattice
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelSectionLeviMulEqAbsDetPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittDecompositionIsotropicFrameEisensteinDictionStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StabilizerInductionLaw
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledBasisSkewColumnMatrixGramInverseStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSiegelParabolicConjDoubledCompact

noncomputable section
open scoped Matrix NNReal ENNReal TensorProduct Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.SphPole

theorem setLIntegral_le_of_disjoint {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] [SecondCountableTopology G] (μ : Measure G) [μ.IsMulLeftInvariant] (Γ : Subgroup G) [Countable Γ] (𝓕 U : Set G)
    (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (hU : MeasurableSet U) (hd : ∀ γ ∈ Γ, ∀ x ∈ U, γ * x ∈ U → γ = 1)
    (f : G → ℝ≥0∞) (hinv : ∀ γ ∈ Γ, ∀ g, f (γ * g) = f g) : ∫⁻ g in U, f g ∂μ ≤ ∫⁻ g in 𝓕, f g ∂μ := by
  rw [h𝓕.setLIntegral_eq_tsum' f U]
  have e : ∀ γ : Γ, ∫⁻ x in γ • U ∩ 𝓕, f (γ⁻¹ • x) ∂μ = ∫⁻ x in γ • U ∩ 𝓕, f x ∂μ := fun γ => by
    refine lintegral_congr fun x => ?_
    rw [Subgroup.smul_def, smul_eq_mul]
    exact hinv _ (γ⁻¹).2 x
  simp only [e]
  have hm : ∀ γ : Γ, NullMeasurableSet (γ • U ∩ 𝓕) μ := fun γ =>
    ((hU.const_smul γ).nullMeasurableSet).inter h𝓕.nullMeasurableSet
  have hdis : Pairwise (Function.onFun (AEDisjoint μ) fun γ : Γ => γ • U ∩ 𝓕) := by
    intro γ γ' hne
    refine Disjoint.aedisjoint (Set.disjoint_left.2 ?_)
    rintro y ⟨⟨u, hu, rfl⟩, -⟩ ⟨⟨u', hu', e⟩, -⟩
    apply hne
    simp only [Subgroup.smul_def, smul_eq_mul] at e
    have h2 : ((γ⁻¹ * γ' : Γ) : G) * u' = u := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc]
      rw [e, inv_mul_cancel_left]
    have h3 := hd _ (γ⁻¹ * γ').2 u' hu' (h2 ▸ hu)
    have h4 : γ⁻¹ * γ' = 1 := Subtype.ext h3
    exact (inv_mul_eq_one.1 h4)
  rw [← lintegral_iUnion₀ hm hdis]
  exact lintegral_mono_set (Set.iUnion_subset fun γ => Set.inter_subset_right)

theorem exists_compact_nhds_separated {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    (Γ : Subgroup G) [DiscreteTopology Γ] : ∃ U : Set G, IsCompact U ∧ U ∈ nhds (1 : G) ∧ ∀ γ ∈ Γ, ∀ x ∈ U, γ * x ∈ U → γ = 1 := by
  obtain ⟨O, hO, hO1⟩ := isOpen_induced_iff.1 (isOpen_discrete ({1} : Set Γ))
  have h1 : (1 : G) ∈ O := by
    have : (1 : Γ) ∈ Subtype.val ⁻¹' O := by rw [hO1]; rfl
    exact this
  have hc : Continuous fun p : G × G => p.2 * p.1⁻¹ := continuous_snd.mul continuous_fst.inv
  have hn : (fun p : G × G => p.2 * p.1⁻¹) ⁻¹' O ∈ nhds ((1 : G), (1 : G)) :=
    hc.continuousAt.preimage_mem_nhds (by simpa using hO.mem_nhds h1)
  obtain ⟨V, hV, W, hW, hVW⟩ := mem_nhds_prod_iff.1 hn
  obtain ⟨U, hU, hUs, hUc⟩ := local_compact_nhds (Filter.inter_mem hV hW)
  refine ⟨U, hUc, hU, fun γ hγ x hx hy => ?_⟩
  have h2 : (x, γ * x) ∈ V ×ˢ W := ⟨(hUs hx).1, (hUs hy).2⟩
  have h3 := hVW h2
  simp only [Set.mem_preimage, mul_inv_cancel_right] at h3
  have h4 : (⟨γ, hγ⟩ : Γ) ∈ Subtype.val ⁻¹' O := h3
  rw [hO1] at h4
  exact congrArg Subtype.val h4

theorem frame_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E))
    (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ), GlobalTheory.ResidueEisenstein.DataJ σ J X Y L a h → ∀ T, GlobalTheory.ResidueEisenstein.IsRepsJ σ J X T →
    ∃ B : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ε * ∑' t : T, h t.1.1 ^ (((n : ℝ) - (r + 1)) + ε) ≤ B := by
  intro F E _ _ _ _ _ σ n J r X Y L a h hD T hT
  obtain ⟨hK, hht, -⟩ := GlobalTheory.T.isCompact_level_height_scales_isotropicFrame F E σ n J r X Y L a h hD
  obtain ⟨hperm, -, hinv, hrep⟩ := GlobalTheory.T.isotropicEisensteinSeries_rationalPoints_permute_terms F E σ n J r X Y L a h hD T hT
  obtain ⟨hn, -⟩ := GlobalTheory.T.wittFrame_rank_le_and_exists_rational_swap F E σ n J r X Y hD.cm hD.herm hD.witt
  set d : ℝ := (n : ℝ) - (r + 1) with hdd
  have hd : (0 : ℝ) < d := by
    have : (2 * ((r : ℝ) + 1)) ≤ n := by exact_mod_cast hn
    have : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    rw [hdd]; linarith
  let μ : Measure (GAd σ J) := Measure.haar
  let Λ : Subgroup (GAd σ J) := ratPts σ J ⊓ GlobalTheory.StdPar.frameStab σ J X ⊤
  haveI : DiscreteTopology Λ := inferInstance
  haveI : Countable (ratPts σ J) := inferInstance
  have h𝓕 := GlobalTheory.AutomorphicL2Unitary.isFundamentalDomain_stdDom (ratPts σ J) μ
  have hDom := GlobalTheory.AutomorphicL2Unitary.isFundamentalDomain_stdDom Λ μ
  obtain ⟨B₀, hB₀, hsh⟩ := GlobalTheory.T.measure_heightShell_le_isotropicFrame_quotient F E σ n J r X Y L a h hD μ _ inferInstance hDom
  have hm : Measurable h := hht.cont.measurable

  obtain ⟨U, hUc, hU1, hUd⟩ := exists_compact_nhds_separated (ratPts σ J)
  have hKU := hK.prod hUc
  have hc1 : Continuous fun u : GAd σ J × GAd σ J => h (u.1 * u.2) := hht.cont.comp (continuous_fst.mul continuous_snd)
  have hc2 : Continuous fun u : GAd σ J × GAd σ J => (h (u.1 * u.2))⁻¹ := hc1.inv₀ fun u => (hht.pos _).ne'
  obtain ⟨M₀, hM₀⟩ := hKU.exists_bound_of_continuousOn hc1.continuousOn
  obtain ⟨m₀, hm₀⟩ := hKU.exists_bound_of_continuousOn hc2.continuousOn
  set M : ℝ := max M₀ 1 with hM
  set m : ℝ := max m₀ 1 with hmm
  have hM1 : 1 ≤ M := le_max_right _ _
  have hm1 : 1 ≤ m := le_max_right _ _
  have hM0 : 0 < M := by linarith
  have hm0 : 0 < m := by linarith
  have hup : ∀ g, ∀ u ∈ U, h (g * u) ≤ M * h g := by
    intro g u hu
    obtain ⟨k, hk, e⟩ := hht.iw g
    rw [e u]
    have h1 := hM₀ (k, u) ⟨hk, hu⟩
    have h2 : h (k * u) ≤ M := ((le_abs_self _).trans h1).trans (le_max_left _ _)
    have := hht.pos g
    nlinarith
  have hlow : ∀ g, ∀ u ∈ U, h g ≤ m * h (g * u) := by
    intro g u hu
    obtain ⟨k, hk, e⟩ := hht.iw g
    rw [e u]
    have h1 := hm₀ (k, u) ⟨hk, hu⟩
    have h2 : (h (k * u))⁻¹ ≤ m := ((le_abs_self _).trans h1).trans (le_max_left _ _)
    have hp := hht.pos (k * u)
    have hg := hht.pos g
    have h3 : 1 ≤ m * h (k * u) := by
      have := (inv_le_iff_one_le_mul₀ hp).1 h2
      linarith
    nlinarith

  let f : ℝ → GAd σ J → ℝ≥0∞ := fun ε x => if h x ≤ 1 then ENNReal.ofReal (h x ^ (d + ε)) else 0
  have hf : ∀ ε : ℝ, Measurable (f ε) := fun ε =>
    Measurable.ite (measurableSet_le hm measurable_const) (hm.pow_const _).ennreal_ofReal measurable_const
  let Φ : ℝ → GAd σ J → ℝ≥0∞ := fun ε g => ∑' t : T, f ε (t.1.1 * g)
  have hΦ : ∀ ε, ∀ γ ∈ ratPts σ J, ∀ g, Φ ε (γ * g) = Φ ε g := by
    intro ε γ hγ g
    obtain ⟨π, hπ⟩ := hperm γ hγ
    have : ∀ i : T, f ε (i.1.1 * (γ * g)) = f ε ((π i).1.1 * g) := fun i => by
      simp only [f, hπ i g]
    simp only [Φ, this]
    exact π.tsum_eq fun t : T => f ε (t.1.1 * g)
  have hint : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ENNReal.ofReal ε * ∫⁻ g in GlobalTheory.AutomorphicL2Unitary.stdDom (ratPts σ J), Φ ε g ∂μ ≤ 2 * B₀ := by
    intro ε h0 h1
    have hu := GlobalTheory.T.setLIntegral_tsum_unfold_of_cosetRepresentatives (GAd σ J) μ (ratPts σ J) Λ T _ _ inferInstance inf_le_left hrep h𝓕 hDom _ (hf ε)
      (fun γ hγ g => by simp only [f, hinv γ hγ g])
    simp only [Φ]
    rw [hu]
    exact GlobalTheory.T.mul_lintegral_rpow_le_of_shell_bound' _ _ h _ B₀ hm hht.pos hd hsh ε h0 h1
  have hUm : MeasurableSet U := hUc.measurableSet
  have hμU : 0 < μ U := lt_of_lt_of_le
    ((isOpen_interior.measure_pos μ ⟨1, mem_interior_iff_mem_nhds.2 hU1⟩)) (measure_mono interior_subset)
  have hμU' : μ U ≠ ⊤ := hUc.measure_ne_top
  set c₀ : ℝ := (m ^ (d + 1))⁻¹ with hc₀
  have hc₀0 : 0 < c₀ := by positivity

  let b : ℝ → T → ℝ := fun ε t => if h t.1.1 ≤ M⁻¹ then h t.1.1 ^ (d + ε) else 0
  have hb0 : ∀ ε t, 0 ≤ b ε t := fun ε t => by
    simp only [b]; split_ifs
    · exact Real.rpow_nonneg (hht.pos _).le _
    · exact le_rfl
  have hpt : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ u ∈ U, ENNReal.ofReal c₀ * ∑' t : T, ENNReal.ofReal (b ε t) ≤ Φ ε u := by
    intro ε h0 h1 u hu
    rw [← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum fun t => ?_
    simp only [b, f]
    by_cases ht : h t.1.1 ≤ M⁻¹
    · have hle : h (t.1.1 * u) ≤ 1 := by
        have := hup t.1.1 u hu
        have h3 : M * h t.1.1 ≤ 1 := by
          have := mul_le_mul_of_nonneg_left ht hM0.le
          rwa [mul_inv_cancel₀ hM0.ne'] at this
        linarith
      rw [if_pos ht, if_pos hle, ← ENNReal.ofReal_mul hc₀0.le]
      refine ENNReal.ofReal_le_ofReal ?_
      have hp := hht.pos t.1.1
      have hq := hht.pos (t.1.1 * u)
      have hx : 0 ≤ d + ε := by linarith
      have h4 : h t.1.1 ^ (d + ε) ≤ (m * h (t.1.1 * u)) ^ (d + ε) :=
        Real.rpow_le_rpow hp.le (hlow _ u hu) hx
      rw [Real.mul_rpow hm0.le hq.le] at h4
      have h5 : m ^ (d + ε) ≤ m ^ (d + 1) := Real.rpow_le_rpow_of_exponent_le hm1 (by linarith)
      have h6 : 0 ≤ h (t.1.1 * u) ^ (d + ε) := Real.rpow_nonneg hq.le _
      have h7 : 0 < m ^ (d + 1) := by positivity
      rw [hc₀, inv_mul_le_iff₀ h7]
      exact h4.trans (mul_le_mul_of_nonneg_right h5 h6)
    · rw [if_neg ht]; simp
  have hB₁ : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ENNReal.ofReal ε * (μ U * (ENNReal.ofReal c₀ * ∑' t : T, ENNReal.ofReal (b ε t))) ≤ 2 * B₀ := by
    intro ε h0 h1
    refine le_trans (mul_le_mul_right ?_ _) (hint ε h0 h1)
    calc μ U * (ENNReal.ofReal c₀ * ∑' t : T, ENNReal.ofReal (b ε t))
        = ∫⁻ _ in U, ENNReal.ofReal c₀ * ∑' t : T, ENNReal.ofReal (b ε t) ∂μ := by
          rw [setLIntegral_const, mul_comm]
      _ ≤ ∫⁻ g in U, Φ ε g ∂μ := setLIntegral_mono' hUm (hpt ε h0 h1)
      _ ≤ _ := setLIntegral_le_of_disjoint μ (ratPts σ J) _ U h𝓕 hUm hUd _ (hΦ ε)
  have hw0 : μ U * ENNReal.ofReal c₀ ≠ 0 := mul_ne_zero hμU.ne' (by simpa using hc₀0)
  have hwt : μ U * ENNReal.ofReal c₀ ≠ ⊤ := ENNReal.mul_ne_top hμU' ENNReal.ofReal_ne_top
  set B₁ : ℝ≥0∞ := 2 * B₀ / (μ U * ENNReal.ofReal c₀) with hB₁d
  have hB₁t : B₁ ≠ ⊤ := ENNReal.div_ne_top (ENNReal.mul_ne_top (by simp) hB₀) hw0
  have hS : ∀ e : ℝ, d < e → Summable fun t : T => h t.1.1 ^ e := fun e he => by
    simpa using GlobalTheory.T.godement_summable_height_rpow_representatives F E σ n J r X Y L a h hD T hT 1 e he
  set S₁ : ℝ := ∑' t : T, h t.1.1 ^ (d + 1) with hS₁
  have hS₁0 : 0 ≤ S₁ := tsum_nonneg fun t => Real.rpow_nonneg (hht.pos _).le _
  refine ⟨B₁.toReal + M * S₁, fun ε h0 h1 => ?_⟩
  have hSε := hS (d + ε) (by linarith)
  have hS1 := hS (d + 1) (by linarith)
  have hbS : ∀ t, b ε t ≤ h t.1.1 ^ (d + ε) := fun t => by
    simp only [b]; split_ifs
    · exact le_rfl
    · exact Real.rpow_nonneg (hht.pos _).le _
  have hbs : Summable (b ε) := Summable.of_nonneg_of_le (hb0 ε) hbS hSε
  have hA : ENNReal.ofReal (ε * ∑' t : T, b ε t) ≤ B₁ := by
    rw [ENNReal.ofReal_mul h0.le, ENNReal.ofReal_tsum_of_nonneg (hb0 ε) hbs, hB₁d, ENNReal.le_div_iff_mul_le (Or.inl hw0) (Or.inl hwt)]
    refine le_trans (le_of_eq ?_) (hB₁ ε h0 h1)
    ring
  have hA' : ε * ∑' t : T, b ε t ≤ B₁.toReal := (ENNReal.ofReal_le_iff_le_toReal hB₁t).1 hA
  have hsplit : ∀ t : T, h t.1.1 ^ (d + ε) ≤ b ε t + M * h t.1.1 ^ (d + 1) := by
    intro t
    have hp := hht.pos t.1.1
    simp only [b]
    split_ifs with ht
    · have : 0 ≤ M * h t.1.1 ^ (d + 1) := by positivity
      linarith
    · have ht' : M⁻¹ < h t.1.1 := not_le.1 ht
      have e1 : h t.1.1 ^ (d + ε) = h t.1.1 ^ (d + 1) * h t.1.1 ^ (ε - 1) := by
        rw [← Real.rpow_add hp]; congr 1; ring
      have e2 : h t.1.1 ^ (ε - 1) ≤ M := by
        have h2 : h t.1.1 ^ (ε - 1) ≤ (M⁻¹) ^ (ε - 1) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) ht'.le (by linarith)
        have h3 : (M⁻¹) ^ (ε - 1) = M ^ (1 - ε) := by
          rw [Real.inv_rpow hM0.le, ← Real.rpow_neg hM0.le]; congr 1; ring
        have h4 : M ^ (1 - ε) ≤ M ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hM1 (by linarith)
        rw [Real.rpow_one] at h4
        linarith
      have h5 : 0 ≤ h t.1.1 ^ (d + 1) := by positivity
      rw [e1, zero_add, mul_comm M]
      exact mul_le_mul_of_nonneg_left e2 h5
  have hsum : ∑' t : T, h t.1.1 ^ (d + ε) ≤ ∑' t : T, b ε t + M * S₁ := by
    rw [hS₁, ← tsum_mul_left, ← (hbs.tsum_add (hS1.mul_left M))]
    exact hSε.tsum_le_tsum hsplit (hbs.add (hS1.mul_left M))
  calc ε * ∑' t : T, h t.1.1 ^ (d + ε) ≤ ε * (∑' t : T, b ε t + M * S₁) := mul_le_mul_of_nonneg_left hsum h0.le
    _ = ε * ∑' t : T, b ε t + ε * (M * S₁) := by ring
    _ ≤ B₁.toReal + 1 * (M * S₁) := add_le_add hA' (mul_le_mul_of_nonneg_right h1 (by positivity))
    _ = _ := by ring

theorem continuous_chart_symm (D : D7) (A : HSp D) (μ : D.host.E) (hμ : IsSkew μ) (κ : GA D (dblSp A) ≃* G D A.rank)
    (hκ : IsChart A μ κ) : Continuous κ.symm := by
  haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  obtain ⟨-, hdet, -⟩ := GlobalTheory.T.doubledBasisSkewColumnMatrix_gram_inverse D A μ hμ
  have hTi' : rat (Tm A μ) * rat (Tm A μ)⁻¹ = 1 := by
    rw [← rat_mul, Matrix.mul_nonsing_inv _ hdet, rat_one]
  have e : ∀ g : G D A.rank, mt (dblSp A) (κ.symm g) = rat (Tm A μ) * (mat g * rat (Tm A μ)⁻¹) := by
    intro g
    have h := hκ (κ.symm g)
    rw [MulEquiv.apply_symm_apply] at h
    rw [← Matrix.mul_assoc, h, Matrix.mul_assoc, hTi', Matrix.mul_one]
  have hm : Continuous fun g : G D A.rank => rat (Tm A μ) * (mat g * rat (Tm A μ)⁻¹) :=
    continuous_const.matrix_mul (HeightExists.continuous_mat.matrix_mul continuous_const)
  refine (isEmbedding_matHom (AF D.host.F) D.sp.cm.sig (dblSp A).gram).continuous_iff.2 (Units.continuous_iff.2 ⟨?_, ?_⟩)
  · exact hm.congr fun g => (e g).symm
  · refine (hm.comp continuous_inv).congr fun g => ?_
    have := e g⁻¹
    rw [map_inv] at this
    rw [Function.comp_apply, ← this]
    simp only [Function.comp_apply, map_inv]
    rfl

theorem height_bound : ∀ (D : D7) (r : ℕ), ∃ H' : G D (r + 1) → ℝ≥0, PositivityTheory.Rg.Rsw.IsHt H' ∧ ∃ B : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
    Summable (fun q : GlobalTheory.Eis.Cosets (P D (r + 1)) (GF D (r + 1)) => (H' (q.out : GF D (r + 1)) : ℝ) ^ (((r + 1 : ℕ) : ℝ) + ε)) ∧
    ε * ∑' q : GlobalTheory.Eis.Cosets (P D (r + 1)) (GF D (r + 1)), (H' (q.out : GF D (r + 1)) : ℝ) ^ (((r + 1 : ℕ) : ℝ) + ε) ≤ B := by
  intro D r
  let A : HSp D := Formalism.BasicNotions.Examples₂.posSpace (E := D.host.E) Formalism.BasicNotions.Examples₂.star_isIntegral (r + 1)
  obtain ⟨μ, hμ, -⟩ := ConjElt.exists_isConj D
  obtain ⟨κ, hκ⟩ : ∃ κ : GA D (dblSp A) ≃* G D (r + 1), IsChart A μ κ := chart_exists D A μ hμ
  let d : HypDec (dblSp A) (GlobalTheory.Core.Rk.SWLaw.zeroSp D) (r + 1) := GlobalTheory.Core.Rk.SWLaw.dblDec A
  obtain ⟨l, hl⟩ := GlobalTheory.RegSch.Inhab.exists_good (dblSp A)
  have hIw := GlobalTheory.Published.SiegelSectionIwasawa.hasIw_of_good d l hl
  obtain ⟨hD, -, -⟩ := GlobalTheory.T.wittDecomposition_isotropicFrameEisenstein_dictionary D (dblSp A) (GlobalTheory.Core.Rk.SWLaw.zeroSp D) r d (GlobalTheory.EisCont.isAniso_zeroSp D) l hl hIw
  have hstabS : siegel A = GlobalTheory.RegSW.stab d := (GlobalTheory.T.doubled_space_maximal_level_lattice D A).1
  have hsc : ∀ q : GlobalTheory.RegSW.stab d, GlobalTheory.ResidueEisenstein.ScalesBy D.sp.cm.sig (dblSp A).gram d.e (q : GA D (dblSp A)) (GlobalTheory.RegSW.onX d q) :=
    fun q => GlobalTheory.RegSW.mul_jX d q
  have hstab := (GlobalTheory.EisCont.parFlag_stab_leftInv D (dblSp A) _ (r + 1) d).2.2.1
  have hPs : ∀ x : GA D (dblSp A), x ∈ GlobalTheory.RegSW.stab d ↔ κ x ∈ P D (r + 1) := fun x => by
    rw [← hstabS]; exact GlobalTheory.T.mem_doublingSiegelParabolic_iff_chart_mem_siegelUnn D A μ hμ κ hκ x
  have hiff : ∀ x : GA D (dblSp A), (∃ β, GlobalTheory.ResidueEisenstein.ScalesBy D.sp.cm.sig (dblSp A).gram d.e x β) ↔ κ x ∈ P D (r + 1) := fun x =>
    ⟨fun ⟨β, e⟩ => (hPs x).1 (hstab x β e).1, fun hx => ⟨_, hsc ⟨x, (hPs x).2 hx⟩⟩⟩
  have hG : ∀ g, g ∈ GQ (dblSp A) ↔ κ g ∈ GF D (r + 1) := chart_mem_GF_iff D A μ hμ κ hκ
  let t : GlobalTheory.Eis.Cosets (P D (r + 1)) (GF D (r + 1)) → ratPts D.sp.cm.sig (dblSp A).gram := fun q =>
    ⟨κ.symm (q.out : GF D (r + 1)), (hG _).2 (by simp)⟩
  have ht_inj : Function.Injective t := fun q q' e => by
    have h1 : κ.symm (q.out : GF D (r + 1)) = κ.symm (q'.out : GF D (r + 1)) := congrArg Subtype.val e
    have h2 : q.out = q'.out := Subtype.ext (κ.symm.injective h1)
    exact Quotient.out_injective h2
  have hmk : ∀ u v : GF D (r + 1), GlobalTheory.AutomorphicL2Unitary.mk ((P D (r + 1)).subgroupOf (GF D (r + 1))) u =
      GlobalTheory.AutomorphicL2Unitary.mk ((P D (r + 1)).subgroupOf (GF D (r + 1))) v ↔ ((v * u⁻¹ : GF D (r + 1)) : G D (r + 1)) ∈ P D (r + 1) := fun u v => by
    rw [GlobalTheory.AutomorphicL2Unitary.mk_eq_iff]
    constructor
    · rintro ⟨δ, hδ⟩
      have : (v * u⁻¹ : GF D (r + 1)) = δ := by rw [← hδ]; group
      rw [this]; exact δ.2
    · intro h
      exact ⟨⟨v * u⁻¹, h⟩, by simp⟩
  let T : Set (ratPts D.sp.cm.sig (dblSp A).gram) := Set.range t
  have hκt : ∀ (γ : ratPts D.sp.cm.sig (dblSp A).gram) (q : GlobalTheory.Eis.Cosets (P D (r + 1)) (GF D (r + 1))),
      κ ((γ * (t q)⁻¹ : ratPts D.sp.cm.sig (dblSp A).gram) : GA D (dblSp A)) = κ γ.1 * ((q.out : GF D (r + 1)) : G D (r + 1))⁻¹ := by
    intro γ q
    simp [t, map_mul, map_inv]
  have hT : GlobalTheory.ResidueEisenstein.IsRepsJ D.sp.cm.sig (dblSp A).gram d.e T := by
    intro γ
    let g₀ : GF D (r + 1) := ⟨κ γ.1, (hG _).1 γ.2⟩
    let q₀ : GlobalTheory.Eis.Cosets (P D (r + 1)) (GF D (r + 1)) := GlobalTheory.AutomorphicL2Unitary.mk _ g₀
    refine ⟨t q₀, ⟨⟨q₀, rfl⟩, (hiff _).2 ?_⟩, ?_⟩
    · rw [hκt]
      exact (hmk q₀.out g₀).1 (Quotient.out_eq _)
    · rintro _ ⟨⟨q, rfl⟩, hs⟩
      have h1 := (hiff _).1 hs
      rw [hκt] at h1
      have e := (hmk q.out g₀).2 h1
      have e2 : q = q₀ := (Quotient.out_eq q).symm.trans e
      rw [e2]
  obtain ⟨B, hB⟩ := frame_bound _ _ _ _ _ _ _ _ _ _ _ hD T hT
  obtain ⟨-, hht, hlaw⟩ := GlobalTheory.T.isCompact_level_height_scales_isotropicFrame _ _ _ _ _ _ _ _ _ _ _ hD
  have hNc : Continuous fun g : GA D (dblSp A) => GlobalTheory.Doubling.iwAbs (GlobalTheory.RegSW.absDet d) l.K g := by
    have := continuous_real_toNNReal.comp hht.cont
    refine this.congr fun g => ?_
    simp
  let H' : G D (r + 1) → ℝ≥0 := fun g => GlobalTheory.Doubling.iwAbs (GlobalTheory.RegSW.absDet d) l.K (κ.symm g)
  refine ⟨H', ⟨hNc.comp (continuous_chart_symm D A μ hμ κ hκ), fun g => ?_, fun q hq a ha g => ?_⟩, B, fun ε h0 h1 => ?_⟩
  · exact NNReal.coe_pos.1 (hht.pos _)
  · have hq1 : κ.symm q ∈ siegel A := (GlobalTheory.T.mem_doublingSiegelParabolic_iff_chart_mem_siegelUnn D A μ hμ κ hκ _).2 (show κ (κ.symm q) ∈ P D (r + 1) by rw [κ.apply_symm_apply]; exact hq)
    have hq2 : κ.symm q ∈ GlobalTheory.RegSW.stab d := hstabS ▸ hq1
    have h1 := hlaw _ _ (hsc ⟨_, hq2⟩) (κ.symm g)
    have h2 := (GlobalTheory.T.doubled_space_maximal_level_lattice D A).2.1 _ hq1 hq2
    have hk : blkA (mat (κ (κ.symm q))) = a.1 := by rw [κ.apply_symm_apply]; exact ha
    have h3 := GlobalTheory.T.standardUnitaryChart_siegelLeviDet_eq D A μ hμ κ hκ ⟨_, hq1⟩ a hk
    apply NNReal.coe_injective
    show ((GlobalTheory.Doubling.iwAbs (GlobalTheory.RegSW.absDet d) l.K (κ.symm (q * g)) : ℝ≥0) : ℝ) = _
    rw [map_mul, h1]
    have h4 : Matrix.GeneralLinearGroup.det (GlobalTheory.RegSW.onX d ⟨_, hq2⟩) = Matrix.GeneralLinearGroup.det a := h2.symm.trans h3
    rw [h4]
    push_cast
    rfl
  · have hn : ((dblSp A).rank : ℝ) - ((r : ℝ) + 1) + ε = ((r + 1 : ℕ) : ℝ) + ε := by
      have : ((dblSp A).rank : ℝ) = ((r + 1 + (r + 1) : ℕ) : ℝ) := rfl
      rw [this]; push_cast; ring
    have hs := GlobalTheory.T.godement_summable_height_rpow_representatives _ _ _ _ _ _ _ _ _ _ _ hD T hT 1 (((dblSp A).rank : ℝ) - ((r : ℝ) + 1) + ε) (by linarith)
    have hb := hB ε h0 h1
    rw [hn] at hs hb
    let e : GlobalTheory.Eis.Cosets (P D (r + 1)) (GF D (r + 1)) ≃ T := Equiv.ofInjective t ht_inj
    have he : ∀ q, (e q).1.1 = κ.symm (q.out : GF D (r + 1)) := fun q => rfl
    constructor
    · have := (e.summable_iff).2 hs
      refine this.congr fun q => ?_
      simp only [Function.comp_apply, mul_one, he]
      rfl
    · rw [← e.tsum_eq] at hb
      simpa only [he] using hb

theorem sphBound_of_htExist : HtExist → SphBound := by
  intro hE D p hp H hH C hC
  obtain ⟨r, rfl⟩ : ∃ r, p = r + 1 := ⟨p - 1, by omega⟩
  obtain ⟨H', hH', B, hB⟩ := height_bound D r
  obtain ⟨-, C₀, hC₀, hcov⟩ := hE D (r + 1)
  have hHc : Continuous fun g : G D (r + 1) => (H g : ℝ) := NNReal.continuous_coe.comp hH.1
  have hHc' : Continuous fun g : G D (r + 1) => (H' g : ℝ) := NNReal.continuous_coe.comp hH'.1
  have hpos' : ∀ g, (0 : ℝ) < H' g := fun g => NNReal.coe_pos.2 (hH'.2.1 g)
  have hcont : Continuous (fun u : G D (r + 1) × G D (r + 1) => (H (u.1 * u.2) : ℝ) / (H' u.1 : ℝ)) :=
    (hHc.comp (continuous_fst.mul continuous_snd)).div (hHc'.comp continuous_fst) fun u => (hpos' _).ne'
  obtain ⟨c, hc⟩ := (hC₀.prod hC).exists_bound_of_continuousOn hcont.continuousOn
  set c₁ : ℝ := max c 1 with hc₁
  have hc₁1 : 1 ≤ c₁ := le_max_right _ _
  have hc₁0 : 0 < c₁ := by linarith
  have key : ∀ γ : G D (r + 1), ∀ h ∈ C, (H (γ * h) : ℝ) ≤ c₁ * H' γ := by
    intro γ h hh
    obtain ⟨q, hq, c₀, hc₀, rfl⟩ := hcov γ
    let a := HeightExists.leviBlock (D := D) (n := r + 1) ⟨q, hq⟩
    have e1 : H (q * c₀ * h) = absA D (Matrix.GeneralLinearGroup.det a) * H (c₀ * h) := by
      rw [mul_assoc]; exact hH.2.2 q hq a rfl _
    have e2 : H' (q * c₀) = absA D (Matrix.GeneralLinearGroup.det a) * H' c₀ := hH'.2.2 q hq a rfl _
    have h3 : (H (c₀ * h) : ℝ) ≤ c₁ * H' c₀ := by
      have := hc (c₀, h) ⟨hc₀, hh⟩
      have h4 : (H (c₀ * h) : ℝ) / H' c₀ ≤ c₁ := ((le_abs_self _).trans this).trans (le_max_left _ _)
      exact (div_le_iff₀ (hpos' _)).1 h4
    rw [e1, e2]
    push_cast
    have : (0 : ℝ) ≤ absA D (Matrix.GeneralLinearGroup.det a) := NNReal.coe_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left h3 this]
  set c₂ : ℝ := c₁ ^ (((r + 1 : ℕ) : ℝ) + 1) with hc₂
  have hc₂0 : 0 ≤ c₂ := by positivity
  refine ⟨c₂ * B, fun σ hσ h hh => ?_⟩
  obtain ⟨hσ1, hσ2⟩ := hσ
  set ε : ℝ := σ - ((r + 1 : ℕ) : ℝ) / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  have hε1 : ε ≤ 1 := by rw [hε]; linarith
  have hx : σ + ((r + 1 : ℕ) : ℝ) / 2 = ((r + 1 : ℕ) : ℝ) + ε := by rw [hε]; ring
  rw [hx]
  obtain ⟨hS, hle⟩ := hB ε hε0 hε1
  have hterm : ∀ q : GlobalTheory.Eis.Cosets (P D (r + 1)) (GF D (r + 1)),
      (H ((q.out : GF D (r + 1)) * h) : ℝ) ^ (((r + 1 : ℕ) : ℝ) + ε) ≤
        c₂ * (H' (q.out : GF D (r + 1)) : ℝ) ^ (((r + 1 : ℕ) : ℝ) + ε) := by
    intro q
    have hx0 : 0 ≤ ((r + 1 : ℕ) : ℝ) + ε := by positivity
    calc _ ≤ (c₁ * H' (q.out : GF D (r + 1))) ^ (((r + 1 : ℕ) : ℝ) + ε) :=
          Real.rpow_le_rpow (NNReal.coe_nonneg _) (key _ h hh) hx0
      _ = c₁ ^ (((r + 1 : ℕ) : ℝ) + ε) * (H' (q.out : GF D (r + 1)) : ℝ) ^ (((r + 1 : ℕ) : ℝ) + ε) :=
          Real.mul_rpow hc₁0.le (NNReal.coe_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hc₁1 (by linarith))
          (by positivity)
  have hS2 := hS.mul_left c₂
  have hs : Summable fun q : GlobalTheory.Eis.Cosets (P D (r + 1)) (GF D (r + 1)) =>
      (H ((q.out : GF D (r + 1)) * h) : ℝ) ^ (((r + 1 : ℕ) : ℝ) + ε) :=
    Summable.of_nonneg_of_le (fun _ => by positivity) hterm hS2
  refine ⟨hs, ?_⟩
  calc _ ≤ ε * ∑' q : GlobalTheory.Eis.Cosets (P D (r + 1)) (GF D (r + 1)),
        c₂ * (H' (q.out : GF D (r + 1)) : ℝ) ^ (((r + 1 : ℕ) : ℝ) + ε) :=
        mul_le_mul_of_nonneg_left (hs.tsum_le_tsum hterm hS2) hε0.le
    _ = c₂ * (ε * ∑' q : GlobalTheory.Eis.Cosets (P D (r + 1)) (GF D (r + 1)),
        (H' (q.out : GF D (r + 1)) : ℝ) ^ (((r + 1 : ℕ) : ℝ) + ε)) := by
        rw [tsum_mul_left]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hle hc₂0

end GlobalTheory.CompanionTheory.SphPole

end
