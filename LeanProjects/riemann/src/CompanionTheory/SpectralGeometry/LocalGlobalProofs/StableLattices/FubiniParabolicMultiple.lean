import Mathlib
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.LineFormulas.Fub2
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ParabolicSubgroupEquality
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FlagFacts
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HaarExistence
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParabolicMeasureModulus

noncomputable section

open MeasureTheory Matrix
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.FubNM

open CompanionTheory.RgExh CompanionTheory.RgExh.Dec CompanionTheory.RgExh.Dec.N.S ReciprocityTheory.ChartRestriction.DS GlobalTheory.FlagMeas Formalism.MainNotions.S

section General

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

theorem lintegral_prodMul_eq (M : Set G) (μM μN : Measure G) [SFinite μM] [SFinite μN] (hM : μM Mᶜ = 0)
    (δ : G → ℝ≥0∞) (hmod : ∀ m ∈ M, μN.map (fun u => m * u * m⁻¹) = δ m • μN)
    (C : Set G) (hCm : MeasurableSet C) (hC0 : μN C ≠ 0) (hC1 : μN C ≠ ⊤)
    (F : G → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ x, F x ∂(GlobalTheory.ParabModulus.prodMul μM μN) = ∫⁻ u, ∫⁻ m, δ m * F (u * m) ∂μM ∂μN := by
  have aM : ∀ᵐ m ∂μM, m ∈ M := mem_ae_iff.2 hM
  have cm : ∀ m : G, Measurable fun u : G => m * u * m⁻¹ := fun m => (measurable_const_mul m).mul_const _
  set δ' : G → ℝ≥0∞ := fun m => μN ((fun u => m * u * m⁻¹) ⁻¹' C) / μN C with hδ'
  have hm' : Measurable δ' := by
    refine Measurable.div_const ?_ _
    exact measurable_measure_prodMk_left (s := (fun z : G × G => z.1 * z.2 * z.1⁻¹) ⁻¹' C)
      ((measurable_mul.mul measurable_fst.inv) hCm)
  have he : ∀ m ∈ M, δ' m = δ m := by
    intro m hm
    simp only [hδ']
    rw [← Measure.map_apply (cm m) hCm, hmod m hm, Measure.smul_apply, smul_eq_mul, mul_div_assoc,
      ENNReal.div_self hC0 hC1, mul_one]
  have hFm : Measurable fun z : G × G => δ' z.1 * F (z.2 * z.1) :=
    (hm'.comp measurable_fst).mul (hF.comp (measurable_snd.mul measurable_fst))
  rw [GlobalTheory.ParabModulus.lintegral_prodMul _ _ _ hF]
  have step : ∀ᵐ m ∂μM, ∫⁻ u, F (m * u) ∂μN = ∫⁻ u, δ' m * F (u * m) ∂μN := by
    filter_upwards [aM] with m hm
    have h := lintegral_map (μ := μN) (hF.comp (measurable_mul_const m)) (cm m)
    rw [hmod m hm, lintegral_smul_measure, smul_eq_mul] at h
    have h2 : ∫⁻ u, δ' m * F (u * m) ∂μN = δ' m * ∫⁻ u, F (u * m) ∂μN :=
      lintegral_const_mul _ (hF.comp (measurable_mul_const m))
    rw [h2, he m hm]
    simp only [Function.comp_apply, inv_mul_cancel_right] at h
    exact h.symm
  rw [lintegral_congr_ae step,
    lintegral_lintegral_swap (f := fun m u => δ' m * F (u * m)) hFm.aemeasurable]
  refine lintegral_congr fun u => lintegral_congr_ae ?_
  filter_upwards [aM] with m hm
  rw [he m hm]

end General

variable {n : ℕ} {ε : Fin n → Bool}

theorem muPar_facts (A : Matrix (Fin n) (Fin n) ℂ) (ν : Measure (PSub ε A)) [ν.IsHaarMeasure] :
    SigmaFinite (muPar ε A ν) ∧ muPar ε A ν (PSub ε A : Set (S7.UJ ε))ᶜ = 0 ∧
      (∀ s ∈ PSub ε A, (muPar ε A ν).map (fun g => s * g) = muPar ε A ν) ∧ muPar ε A ν ≠ 0 := by
  have hcl := GlobalTheory.CompanionTheory.ParabolicHaar.isClosed_pSub ε A
  have hv : Measurable (Subtype.val : PSub ε A → S7.UJ ε) := measurable_subtype_coe
  refine ⟨⟨⟨⟨compactCovering (S7.UJ ε), fun _ => trivial, fun i => ?_, iUnion_compactCovering _⟩⟩⟩, ?_, ?_, ?_⟩
  · have hK := isCompact_compactCovering (S7.UJ ε) i
    rw [muPar, Measure.map_apply hv hK.measurableSet]
    exact (hcl.isClosedEmbedding_subtypeVal.isCompact_preimage hK).measure_lt_top
  · rw [muPar, Measure.map_apply hv hcl.measurableSet.compl]
    have : (Subtype.val : PSub ε A → S7.UJ ε) ⁻¹' (PSub ε A : Set (S7.UJ ε))ᶜ = ∅ := by
      ext x
      simp
    rw [this, measure_empty]
  · intro s hs
    have e : (fun g : S7.UJ ε => s * g) ∘ (Subtype.val : PSub ε A → S7.UJ ε) =
        Subtype.val ∘ (fun g : PSub ε A => (⟨s, hs⟩ : PSub ε A) * g) := rfl
    rw [muPar, Measure.map_map (measurable_const_mul s) hv, e,
      ← Measure.map_map hv (measurable_const_mul _), map_mul_left_eq_self]
  · intro h
    have h1 : muPar ε A ν Set.univ = 0 := by rw [h]; simp
    rw [muPar, Measure.map_apply hv MeasurableSet.univ, Set.preimage_univ] at h1
    exact (Measure.IsHaarMeasure.toIsOpenPosMeasure (μ := ν)).open_pos _ isOpen_univ Set.univ_nonempty h1

theorem fub2 : Fub2 := by
  intro n ε A hA
  have hW : IsIsoFlag ε (fun _ : Fin 1 => rk A) (W A) := GlobalTheory.CompanionTheory.PSubFlag.isoFlag hA
  have hj : ∀ i : Fin 1, 1 ≤ (fun _ : Fin 1 => rk A) i := fun _ => (GlobalTheory.CompanionTheory.GradFlag.flagFacts n ε A hA).1
  obtain ⟨⟨μN, sN, hN⟩, ⟨μM, sM, hM⟩, μK, hK0, hK1, hKi⟩ := GlobalTheory.T.exists_gauge_measures_isotropicFlag_parabolic n ε 1 _ (W A) hj hW
  have hmod := GlobalTheory.T.isotropicFlag_levi_conj_haar_modulus n ε 1 _ (W A) hj hW μN hN
  refine ⟨μN, μM, inferInstance, inferInstance, hM.1, ?_, ?_, ?_⟩
  · intro a ha hc
    have e : μM.map (· * a) = μM.map (a * ·) :=
      Measure.map_congr (Filter.Eventually.mono (mem_ae_iff.2 hM.1 : ∀ᵐ m ∂μM, m ∈ flagM ε (W A)) fun m hm => hc m hm)
    rw [e]
    exact hM.2.1 a ha
  · obtain ⟨κ, k0, k1, hκ⟩ := GlobalTheory.T.iwasawa_integration_formula_up_to_constant n ε _ _ rfl rfl 1 _ hj (W A) hW μN μM μK hN hM hK0 hK1 hKi
    refine ⟨κ, k0, k1, fun F hF hinv => ?_⟩
    rw [hκ F hF]
    congr 1
    refine lintegral_congr fun u => lintegral_congr fun m => ?_
    have aK : ∀ᵐ k ∂μK, k ∈ maxK ε := mem_ae_iff.2 hK0
    have e : ∫⁻ k, F (u * m * k) ∂μK = F (u * m) := by
      rw [lintegral_congr_ae (g := fun _ => F (u * m)) (aK.mono fun k hk => hinv _ k (by
        rw [← SetLike.mem_coe, GlobalTheory.IwasawaShape.coe_KG]; exact hk))]
      simp [lintegral_const, hK1]
    rw [e]
    rfl
  · intro ν hν
    obtain ⟨⟨N, eN⟩, cN, -⟩ := GlobalTheory.FlagMeas.UnipRad.flagN_subgroup_closed_keeps n ε 1 _ (W A) hW
    obtain ⟨⟨M, eM⟩, cM, -, -, hnorm⟩ := GlobalTheory.FlagLeviGroup.levi_compact_subgroups n ε 1 (W A)
    have huniq := (GlobalTheory.RealIwasawa.iwasawa n ε 1 _ (W A) hW).2
    have mN : ∀ v, v ∈ N ↔ v ∈ flagN ε (W A) := fun v => by rw [← SetLike.mem_coe, eN]
    have mM : ∀ v, v ∈ M ↔ v ∈ flagM ε (W A) := fun v => by rw [← SetLike.mem_coe, eM]
    have cN' : IsClosed (N : Set (Formalism.REAL.UJ ε)) := eN ▸ cN
    have cM' : IsClosed (M : Set (Formalism.REAL.UJ ε)) := eM ▸ cM
    have hN' : IsGaugeSub (N : Set (Formalism.REAL.UJ ε)) _ μN := eN ▸ hN
    have hM' : IsGaugeSub (M : Set (Formalism.REAL.UJ ε)) _ μM := eM ▸ hM
    obtain ⟨hN0, iN⟩ := GlobalTheory.IwasawaShape.gauge_ne_zero_finite N _ μN cN' hN'
    obtain ⟨hM0, iM⟩ := GlobalTheory.IwasawaShape.gauge_ne_zero_finite M _ μM cM' hM'
    haveI := iN
    haveI := iM
    let P : Subgroup (Formalism.REAL.UJ ε) := PSub ε A
    have hcl : IsClosed (P : Set (Formalism.REAL.UJ ε)) := GlobalTheory.CompanionTheory.ParabolicHaar.isClosed_pSub ε A
    have hPeq : ∀ g : Formalism.REAL.UJ ε, g ∈ P ↔ ∃ u ∈ flagN ε (W A), ∃ m ∈ flagM ε (W A), g = u * m :=
      GlobalTheory.CompanionTheory.PSubFlag.psubEq n ε A hA
    have hnorm1 : ∀ m ∈ M, ∀ v ∈ N, m * v * m⁻¹ ∈ N := fun m hm v hv =>
      (mN _).2 (hnorm m ((mM m).1 hm) v ((mN v).1 hv))
    have hnorm' : ∀ l ∈ M, ∀ v ∈ N, l⁻¹ * v * l ∈ N := fun l hl v hv => by
      simpa using hnorm1 l⁻¹ (M.inv_mem hl) v hv
    have hMN : ∀ l ∈ M, l ∈ N → l = 1 := fun l hl hlN =>
      huniq l ((mN l).1 hlN) l⁻¹ ((mM _).1 (M.inv_mem hl)) (by
        rw [mul_inv_cancel, ← GlobalTheory.IwasawaShape.coe_KG]; exact (Formalism.REAL.KG ε).one_mem)
    have hMP : ∀ l ∈ M, ∀ v ∈ N, l * v ∈ P := fun l hl v hv =>
      (hPeq _).2 ⟨l * v * l⁻¹, (mN _).1 (hnorm1 l hl v hv), l, (mM l).1 hl, by group⟩
    have hdec : ∀ p ∈ P, ∃ l ∈ M, ∃ v ∈ N, p = l * v := by
      intro p hp
      obtain ⟨u, hu, m, hm, rfl⟩ := (hPeq p).1 hp
      exact ⟨m, (mM m).2 hm, m⁻¹ * u * m, hnorm' m ((mM m).2 hm) u ((mN u).2 hu), by group⟩
    obtain ⟨hP0, sf, T, hTm, hT0, hT1⟩ := GlobalTheory.ParabModulus.prodMul_facts M N P cM' cN' hcl.measurableSet hMN hMP hdec
      μM μN hM0 hN0 hM'.1 hN'.1
    haveI := sf
    have lP : ∀ s ∈ P, (GlobalTheory.ParabModulus.prodMul μM μN).map (fun g => s * g) = GlobalTheory.ParabModulus.prodMul μM μN := by
      intro s hs
      obtain ⟨l, hl, v, hv, rfl⟩ := hdec s hs
      have : (fun g => l * v * g) = (fun g => l * g) ∘ (fun g => v * g) := by
        funext g; simp [mul_assoc]
      rw [this, ← Measure.map_map (measurable_const_mul l) (measurable_const_mul v),
        GlobalTheory.ParabModulus.prodMul_left_snd M N hnorm' μM μN hM'.1 hN'.2.1 v hv,
        GlobalTheory.ParabModulus.prodMul_left_fst M μM μN hM'.2.1 l hl]
    have key : ∀ ρ : Measure (Formalism.REAL.UJ ε), SigmaFinite ρ → ρ (P : Set (Formalism.REAL.UJ ε))ᶜ = 0 →
        (∀ s ∈ P, ρ.map (fun g => s * g) = ρ) → ρ ≠ 0 → ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧
          ∀ F : Formalism.REAL.UJ ε → ℝ≥0∞, Measurable F →
            ∫⁻ x, F x ∂ρ = c * ∫⁻ u, ∫⁻ m, modA A m * F (u * m) ∂μM ∂μN := by
      intro ρ sρ hρ0 hρi hρne
      haveI := sρ
      obtain ⟨c, hc⟩ := GlobalTheory.ParabModulus.eq_smul_of_left_inv P hcl.measurableSet (ρ)
        (GlobalTheory.ParabModulus.prodMul μM μN) hρ0 hP0 hρi lP T hTm hT0 hT1
      have c0 : c ≠ 0 := by
        rintro rfl
        exact hρne (by rw [hc, zero_smul])
      have c1 : c ≠ ⊤ := by
        rintro rfl
        have hS := iUnion_spanningSets (ρ)
        have hz : ∀ i, GlobalTheory.ParabModulus.prodMul μM μN (T ∩ spanningSets (ρ) i) = 0 := by
          intro i
          by_contra h
          have h1 : ρ (T ∩ spanningSets (ρ) i) = ⊤ := by
            generalize T ∩ spanningSets ρ i = X at h ⊢
            rw [hc, Measure.smul_apply, smul_eq_mul, ENNReal.top_mul h]
          have h2 : ρ (T ∩ spanningSets ρ i) < ⊤ := lt_of_le_of_lt (measure_mono Set.inter_subset_right)
            (measure_spanningSets_lt_top (ρ) i)
          rw [h1] at h2
          exact lt_irrefl _ h2
        refine hT0 (measure_mono_null (t := ⋃ i, T ∩ spanningSets (ρ) i) ?_ (measure_iUnion_null hz))
        rw [← Set.inter_iUnion, hS, Set.inter_univ]
      obtain ⟨i, hi⟩ : ∃ i, μN (compactCovering (Formalism.REAL.UJ ε) i) ≠ 0 := by
        by_contra h
        push Not at h
        exact hN0 (Measure.measure_univ_eq_zero.1 (by
          rw [← iUnion_compactCovering]; exact measure_iUnion_null h))
      have hC := isCompact_compactCovering (Formalism.REAL.UJ ε) i
      refine ⟨c, c0, c1, fun F hF => ?_⟩
      rw [hc, lintegral_smul_measure, smul_eq_mul,
        lintegral_prodMul_eq (flagM ε (W A)) μM μN hM.1 (modA A) hmod _ hC.measurableSet hi hC.measure_lt_top.ne F hF]
    obtain ⟨sρ, hρ0, hρi, hρne⟩ := muPar_facts (ε := ε) A ν
    exact key (muPar ε A ν) sρ hρ0 hρi hρne

end GlobalTheory.CompanionTheory.FubNM
