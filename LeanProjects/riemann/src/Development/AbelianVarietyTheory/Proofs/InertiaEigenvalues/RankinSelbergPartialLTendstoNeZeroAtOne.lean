import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsGoodEmptyIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalRankinSelbergLogarithmFormulaStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GenDirichletHasSumIteratedDeriv
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsOneLeNormPsumMultiset
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankinSelbergGLnGLmPartialLEqDivEntireStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankinSelbergSameDegreeMeromorphicContinuationStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormProdSatakeParametersUnitaryEqOneStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterNormSqLtAbsNormUnitaryCuspStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGoodRankinSelbergPlaceSetSupersetTotallyCoStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalRankinSelbergFactorConjTendstoOneNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DirichletSeriesExponentialSumConvergesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PartialRankinSelbergProductConjSwapRealStatement

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.JSW Filter Topology Formalism.UG GlobalTheory.RSNonvan

namespace GlobalTheory.RSNonvan

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

theorem analyticAt_dslope' {f : ℂ → ℂ} {ξ x : ℂ} (hx : AnalyticAt ℂ f x) : AnalyticAt ℂ (dslope f ξ) x := by
  by_cases h : x = ξ
  · subst h
    obtain ⟨p, hp⟩ := hx
    exact ⟨_, hp.has_fpower_series_dslope_fslope⟩
  · have h1 : AnalyticAt ℂ (fun t => (t - ξ)⁻¹ * (f t - f ξ)) x :=
      ((analyticAt_id.sub analyticAt_const).inv (sub_ne_zero.2 h)).mul (hx.sub analyticAt_const)
    refine h1.congr ?_
    filter_upwards [dslope_eventuallyEq_slope_of_ne f h] with t ht
    rw [ht, slope_def_module, smul_eq_mul]

theorem hasProd_of_subset {ι : Type} [DecidableEq ι] (f : ι → ℂ) {T T' : Finset ι} (h : T ⊆ T') {b : ℂ}
    (hb : HasProd (fun w : {w // w ∉ T'} => f w.1) b) :
    HasProd (fun w : {w // w ∉ T} => f w.1) ((∏ w ∈ T' \ T, f w) * b) := by
  classical
  let s : Set {w // w ∉ T} := {w | w.1 ∈ T'}
  let e1 : (↑(T' \ T) : Set ι) ≃ s :=
    { toFun := fun w => ⟨⟨w.1, (Finset.mem_sdiff.1 (Finset.mem_coe.1 w.2)).2⟩, (Finset.mem_sdiff.1 (Finset.mem_coe.1 w.2)).1⟩
      invFun := fun w => ⟨w.1.1, Finset.mem_coe.2 (Finset.mem_sdiff.2 ⟨w.2, w.1.2⟩)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let e2 : {w // w ∉ T'} ≃ (sᶜ : Set {w // w ∉ T}) :=
    { toFun := fun w => ⟨⟨w.1, fun hw => w.2 (h hw)⟩, w.2⟩
      invFun := fun w => ⟨w.1.1, w.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have h1 : HasProd ((fun w : {w // w ∉ T} => f w.1) ∘ ((↑) : s → {w // w ∉ T})) (∏ w ∈ T' \ T, f w) :=
    (e1.hasProd_iff).1 (Finset.hasProd (T' \ T) f)
  have h2 : HasProd ((fun w : {w // w ∉ T} => f w.1) ∘ ((↑) : (sᶜ : Set {w // w ∉ T}) → {w // w ∉ T})) b :=
    (e2.hasProd_iff).1 hb
  exact h1.mul_compl h2

theorem sat_spec {a : ℕ} {π : CG E a} {w : HeightOneSpectrum (𝓞 E)} (h : ∃ B, π.HasSat w B) :
    π.HasSat w (sat π w) := by
  unfold sat
  rw [dif_pos h]
  exact h.choose_spec

theorem prod_map_val (B : Multiset ℂˣ) : (B.map (fun α : ℂˣ => (α : ℂ))).prod = ((B.prod : ℂˣ) : ℂ) := by
  induction B using Multiset.induction_on with
  | empty => simp
  | cons b B ih => simp [ih]

theorem offDiag : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a b : ℕ) (σ : CG E a) (σ' : CG E b), 1 ≤ a → 1 ≤ b → σ.IsUnitary → σ'.IsUnitary → (⟨a, σ⟩ : Σ a, CG E a) ≠ ⟨b, σ'⟩ → ∀ T : Finset (HeightOneSpectrum (𝓞 E)), IsGood T → UnrOutside T σ → UnrOutside T σ' → ∃ G : ℂ → ℂ, (∀ x : ℝ, 0 < x → AnalyticAt ℂ G (x : ℂ)) ∧ ∀ x : ℝ, 1 < x → HasProd (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => lfac σ σ' (x : ℂ) w.1) (G x) := by
  intro E _ _ _ a b σ σ' ha hb hσ hσ' hne T hgood hU hU'
  rcases lt_trichotomy a b with hab | rfl | hab
  · obtain ⟨F, H, hF, hH, hHpos, hFH⟩ := GlobalTheory.T.rankinSelberg_GLn_GLm_partialL_eq_div_entire E b a σ' σ ha hab hσ' hσ T hgood.2 hU' hU
    refine ⟨fun z => starRingEnd ℂ (F (starRingEnd ℂ z) / H (starRingEnd ℂ z)), ?_, ?_⟩
    · intro x hx
      have hopen : IsOpen {z : ℂ | H (starRingEnd ℂ z) ≠ 0} :=
        isOpen_ne_fun (hH.continuous.comp Complex.continuous_conj) continuous_const
      have hxmem : (x : ℂ) ∈ {z : ℂ | H (starRingEnd ℂ z) ≠ 0} := by
        simp only [Set.mem_setOf_eq, Complex.conj_ofReal]
        intro h0
        have := (hHpos x).1
        rw [h0, Complex.zero_re] at this
        exact lt_irrefl 0 this
      refine DifferentiableOn.analyticAt (fun z hz => ?_) (hopen.mem_nhds hxmem)
      have hd : DifferentiableAt ℂ (fun u => F u / H u) (starRingEnd ℂ z) := (hF _).div (hH _) hz
      have := hd.conj_conj
      rw [Complex.conj_conj] at this
      exact this.differentiableWithinAt
    · intro x hx
      have hp := (GlobalTheory.T.localRankinSelberg_logarithm_formula.2 E a b σ σ' hσ hσ' T hU hU' x hx).2
      have e := GlobalTheory.T.partial_rankinSelberg_product_conj_swap_real E b a σ' σ hσ' hσ T hU' hU x hx
      have h2 : ∏' w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, lfac σ' σ (x : ℂ) w.1 = F x / H x := (hFH x hx).tprod_eq
      have h3 : ∏' w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, lfac σ σ' (x : ℂ) w.1 =
          starRingEnd ℂ (F (starRingEnd ℂ (x : ℂ)) / H (starRingEnd ℂ (x : ℂ))) := by
        rw [e, h2, Complex.conj_ofReal]
      beta_reduce
      rw [← h3]
      exact hp.multipliable.hasProd
  · have hne' : σ ≠ σ' := fun h => hne (by rw [h])
    obtain ⟨F, hFa, hF1, hF⟩ := GlobalTheory.T.rankinSelberg_sameDegree_meromorphic_continuation E a σ σ' ha hσ hσ' T hgood hU hU'
    refine ⟨dslope F 1, fun x hx => analyticAt_dslope' (hFa x hx), fun x hx => ?_⟩
    have hx1 : (x : ℂ) ≠ 1 := by exact_mod_cast hx.ne'
    have e : dslope F 1 (x : ℂ) = F x / ((x : ℂ) - 1) := by
      rw [dslope_of_ne _ hx1, slope_def_module, hF1 hne', sub_zero, smul_eq_mul, inv_mul_eq_div]
    rw [e]
    exact hF x hx
  · obtain ⟨F, H, hF, hH, hHpos, hFH⟩ := GlobalTheory.T.rankinSelberg_GLn_GLm_partialL_eq_div_entire E a b σ σ' hb hab hσ hσ' T hgood.2 hU hU'
    refine ⟨fun z => F z / H z, fun x hx => (hF.analyticAt _).div (hH.analyticAt _) ?_, fun x hx => hFH x hx⟩
    intro h0
    have := (hHpos x).1
    rw [h0, Complex.zero_re] at this
    exact lt_irrefl 0 this

theorem tendsto_of_analyticAt {G : ℂ → ℂ} (hG : AnalyticAt ℂ G 1) :
    Tendsto (fun x : ℝ => G x) (𝓝[>] 1) (𝓝 (G 1)) := by
  have h := hG.continuousAt.comp (x := (1 : ℝ)) (by simpa using Complex.continuous_ofReal.continuousAt)
  have h2 := h.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (1 : ℝ)))
  simp only [Function.comp_def, Complex.ofReal_one] at h2
  exact h2

theorem tendsto_partialL_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a b : ℕ) (σ : CG E a) (σ' : CG E b), 1 ≤ a → 1 ≤ b → σ.IsUnitary → σ'.IsUnitary → (⟨a, σ⟩ : Σ a, CG E a) ≠ ⟨b, σ'⟩ → ∀ T : Finset (HeightOneSpectrum (𝓞 E)), UnrOutside T σ → UnrOutside T σ' → ∃ z : ℂ, z ≠ 0 ∧ Tendsto (fun x : ℝ => ∏' w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, locL (Ideal.absNorm w.1.asIdeal) (sat σ w.1) ((sat σ' w.1).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ)) (𝓝[>] 1) (𝓝 z) := by
  intro E _ _ _ a b σ σ' ha hb hσ hσ' hne T hT hT'
  classical
  obtain ⟨T', hTT', hgood⟩ := GlobalTheory.T.exists_goodRankinSelbergPlaceSet_superset_totallyComplex E T
  have hU : UnrOutside T' σ := fun w hw => hT w fun h => hw (hTT' h)
  have hU' : UnrOutside T' σ' := fun w hw => hT' w fun h => hw (hTT' h)
  obtain ⟨G, hGa, hG⟩ := offDiag E a b σ σ' ha hb hσ hσ' hne T' hgood hU hU'
  obtain ⟨G', hG'a, hG'⟩ := offDiag E b a σ' σ hb ha hσ' hσ (Ne.symm hne) T' hgood hU' hU
  obtain ⟨D, hDa, -, hD⟩ := GlobalTheory.T.rankinSelberg_sameDegree_meromorphic_continuation E a σ σ ha hσ hσ T' hgood hU hU
  obtain ⟨D', hD'a, -, hD'⟩ := GlobalTheory.T.rankinSelberg_sameDegree_meromorphic_continuation E b σ' σ' hb hσ' hσ' T' hgood hU' hU'
  have hGa1 : AnalyticAt ℂ G 1 := by simpa using hGa 1 one_pos
  have hG'a1 : AnalyticAt ℂ G' 1 := by simpa using hG'a 1 one_pos
  have hlim : Tendsto (fun x : ℝ => ∏' w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T'}, lfac σ σ' (x : ℂ) w.1)
      (𝓝[>] 1) (𝓝 (G 1)) :=
    (tendsto_of_analyticAt hGa1).congr' (eventually_nhdsWithin_of_forall fun x hx => ((hG x hx).tprod_eq).symm)
  have hG1 : G 1 ≠ 0 := by
    intro h0
    have hG'1 : G' 1 = 0 := by
      have hlimc : Tendsto (fun x : ℝ => G' x) (𝓝[>] 1) (𝓝 (starRingEnd ℂ (G 1))) := by
        refine ((Complex.continuous_conj.tendsto _).comp (tendsto_of_analyticAt hGa1)).congr'
          (eventually_nhdsWithin_of_forall fun x hx => ?_)
        have e := GlobalTheory.T.partial_rankinSelberg_product_conj_swap_real E a b σ σ' hσ hσ' T' hU hU' x hx
        simp only [Function.comp]
        rw [← (hG x hx).tprod_eq, ← (hG' x hx).tprod_eq, e]
      rw [tendsto_nhds_unique (tendsto_of_analyticAt hG'a1) hlimc, h0, map_zero]
    let P : ℂ → ℂ := fun z => D z * D' z * dslope G 1 z * dslope G' 1 z
    have hPa : ∀ x : ℝ, 0 < x → AnalyticAt ℂ P (x : ℂ) := fun x hx =>
      (((hDa x hx).mul (hD'a x hx)).mul (analyticAt_dslope' (hGa x hx))).mul (analyticAt_dslope' (hG'a x hx))
    have hP : ∀ x : ℝ, 1 < x → ∃ g : ℂ, HasSum (fun p : {w : HeightOneSpectrum (𝓞 E) // w ∉ T'} × ℕ =>
        ((dcoef σ σ' p.1.1 p.2 : ℝ) : ℂ) * Complex.exp (-((dexp p.1.1 p.2 : ℝ) : ℂ) * (x : ℂ))) g ∧ P x = Complex.exp g := by
      intro x hx
      obtain ⟨g, hg, he⟩ := GlobalTheory.T.dirichlet_series_exponential_sum_converges E a b σ σ' hσ hσ' T' hU hU' x hx
      refine ⟨g, hg, ?_⟩
      rw [← he, (hD x hx).tprod_eq, (hD' x hx).tprod_eq, (hG x hx).tprod_eq, (hG' x hx).tprod_eq]
      have hx1 : (x : ℂ) ≠ 1 := by exact_mod_cast hx.ne'
      have hx1' : (x : ℂ) - 1 ≠ 0 := sub_ne_zero.2 hx1
      have e1 : dslope G 1 (x : ℂ) = G x / ((x : ℂ) - 1) := by
        rw [dslope_of_ne _ hx1, slope_def_module, h0, sub_zero, smul_eq_mul, inv_mul_eq_div]
      have e2 : dslope G' 1 (x : ℂ) = G' x / ((x : ℂ) - 1) := by
        rw [dslope_of_ne _ hx1, slope_def_module, hG'1, sub_zero, smul_eq_mul, inv_mul_eq_div]
      simp only [P, e1, e2]
      field_simp
    have hN : (0 : ℝ) < 1 / ((a + b : ℕ) : ℝ) := by
      have : (0 : ℝ) < ((a + b : ℕ) : ℝ) := by exact_mod_cast (show 0 < a + b by omega)
      positivity
    obtain ⟨g, hg, -⟩ := GlobalTheory.landau_exp_hasSum_of_analyticAt ({w : HeightOneSpectrum (𝓞 E) // w ∉ T'} × ℕ)
      (fun p => dcoef σ σ' p.1.1 p.2) (fun p => dexp p.1.1 p.2) 0 1 P (fun p => dcoef_nonneg _ _ _ _)
      (fun p => dexp_nonneg _ _) one_pos hPa hP _ hN
    set y : ℝ := 1 / ((a + b : ℕ) : ℝ) with hy
    have hs : Summable (fun p : {w : HeightOneSpectrum (𝓞 E) // w ∉ T'} × ℕ =>
        dcoef σ σ' p.1.1 p.2 * Real.exp (-(dexp p.1.1 p.2) * y)) := by
      rw [← Complex.summable_ofReal]
      refine hg.summable.congr fun p => ?_
      push_cast
      rfl
    refine GlobalTheory.PowerSumDiv.not_summable_psum_sq (a + b) (by omega) T'
      (fun w => (sat σ w).map (fun α : ℂˣ => (α : ℂ)) + (sat σ' w).map (fun α : ℂˣ => (α : ℂ))) ?_ ?_ (le_of_eq hy) ?_
    · intro w hw
      rw [Multiset.card_add, Multiset.card_map, Multiset.card_map, (sat_spec (hU w hw)).card, (sat_spec (hU' w hw)).card]
    · intro w hw
      rw [Multiset.prod_add, norm_mul, prod_map_val, prod_map_val, GlobalTheory.T.norm_prod_satakeParameters_unitary_eq_one E a σ w _ hσ (sat_spec (hU w hw)),
        GlobalTheory.T.norm_prod_satakeParameters_unitary_eq_one E b σ' w _ hσ' (sat_spec (hU' w hw)), one_mul]
    · refine hs.congr fun p => ?_
      have hq : (0 : ℝ) < (Ideal.absNorm p.1.1.asIdeal : ℝ) := by
        have := NumberField.HeightOneSpectrum.one_lt_absNorm p.1.1
        have : (0 : ℝ) < ((Ideal.absNorm p.1.1.asIdeal : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < Ideal.absNorm p.1.1.asIdeal)
        exact this
      simp only [dcoef, dexp]
      rw [Real.rpow_def_of_pos hq]
      have : -(((p.2 : ℝ) + 1) * Real.log (Ideal.absNorm p.1.1.asIdeal : ℝ)) * y =
          Real.log (Ideal.absNorm p.1.1.asIdeal : ℝ) * -(((p.2 : ℝ) + 1) * y) := by ring
      rw [this]
      ring
  have hfac : ∀ w ∈ T' \ T, Tendsto (fun x : ℝ => lfac σ σ' (x : ℂ) w) (𝓝[>] 1) (𝓝 (lfac σ σ' 1 w)) ∧
      lfac σ σ' 1 w ≠ 0 := by
    intro w hw
    have hw2 := (Finset.mem_sdiff.1 hw).2
    exact GlobalTheory.T.localRankinSelbergFactor_conj_tendsto_one_ne_zero (Ideal.absNorm w.asIdeal) (sat σ w) (sat σ' w) (NumberField.HeightOneSpectrum.one_lt_absNorm w)
      (GlobalTheory.T.satakeParameter_normSq_lt_absNorm_unitaryCusp E a σ ha hσ T hT w hw2) (GlobalTheory.T.satakeParameter_normSq_lt_absNorm_unitaryCusp E b σ' hb hσ' T hT' w hw2)
  refine ⟨(∏ w ∈ T' \ T, lfac σ σ' 1 w) * G 1,
    mul_ne_zero (Finset.prod_ne_zero_iff.2 fun w hw => (hfac w hw).2) hG1, ?_⟩
  have hprodlim : Tendsto (fun x : ℝ => ∏ w ∈ T' \ T, lfac σ σ' (x : ℂ) w) (𝓝[>] 1)
      (𝓝 (∏ w ∈ T' \ T, lfac σ σ' 1 w)) := tendsto_finset_prod _ fun w hw => (hfac w hw).1
  refine (hprodlim.mul hlim).congr' (eventually_nhdsWithin_of_forall fun x hx => ?_)
  have hp := (GlobalTheory.T.localRankinSelberg_logarithm_formula.2 E a b σ σ' hσ hσ' T' hU hU' x hx).2
  have h1 := hasProd_of_subset (fun w => lfac σ σ' (x : ℂ) w) hTT' hp.multipliable.hasProd
  exact h1.tprod_eq.symm

end GlobalTheory.RSNonvan
