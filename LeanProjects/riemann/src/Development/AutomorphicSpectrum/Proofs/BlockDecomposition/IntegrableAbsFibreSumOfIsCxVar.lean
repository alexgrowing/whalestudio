import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StPtsAbsIntegrable
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StDivisorGeneralPointBranches
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLelongLimitAtBranches
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsCurrent
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StRegMassNearSmall
import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.PoincareLelong
import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.SheetDensityEqSetSheetDensity
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedF
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGood
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSupp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSheet
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterFib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.CxPosDens
import Development.AutomorphicSpectrum.Proofs.MetricProofs.CxSimple
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SetFibreFiniteOfGoodProj
import Development.AutomorphicSpectrum.Proofs.MetricProofs.AemeasurableCxPosDensity
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsCxVarOfMemMinimalPrimesCxIdeal
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ConePtsSubsetMcPtsOfMinimal
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MemChartComponents
import Development.AutomorphicSpectrum.Proofs.MetricProofs.DomCellLogNormMeasurableInvariant
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LintegralFibreLogNormFiniteStatement
set_option maxSynthPendingDepth 1

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Pub.CxAbs

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt GlobalTheory.CompanionTheory.Ar.Pub.CxComp Filter Topology
open ReciprocityTheory.AnForm.R (conePts)
open GlobalTheory.CompanionTheory.Ar.Pub.CxChart (absLogNorm)

theorem absFibreSum_eq_sum_components_ae {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P : Ideal (MRing ι)} {e : ℕ}
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} {L : Fin e → HermLine ι} {A : HermLine ι}
    {s : MRing ι}
    (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ) (hL : ∀ j, IsSmoothHerm (L j)) (hA : IsSmoothHerm A)
    (hs : IsSectionOn P A s) :
    ∀ᵐ y, ∑ᶠ w ∈ fibre P Ψ y, |sheetDensity P Ψ (pot L) (logNorm A s) y w| =
      ∑ᶠ Q ∈ (cxIdeal P).minimalPrimes, ∑ᶠ w ∈ setFibre (conePts Q) Ψ y,
        |setSheetDensity (conePts Q) Ψ (pot L) (logNormC A (map (Int.castRingHom ℂ) s)) y w| := by
  classical
  have hfin : (cxIdeal P).minimalPrimes.Finite := Ideal.finite_minimalPrimes_of_isNoetherianRing _ _
  have hmeet := GroundTheory.Heights₂.Heights.HilbertSamuel.ComponentsMeetNull.proof
    GroundTheory.Heights₂.Heights.HilbertSamuel.ChartDimLt.proof
    GroundTheory.Heights₂.Heights.HilbertSamuel.ChartRatioImageNull.proof K ι P e Ψ hfin.toFinset hP hΨ
    (fun W hW => hfin.mem_toFinset.1 hW)
  filter_upwards [compl_mem_ae_iff.mpr hmeet, sheetIndep K ι P e Ψ L A s hP hΨ hL hA hs] with y hyN hind
  have hone : ∀ Q ∈ (cxIdeal P).minimalPrimes, ∀ Q' ∈ (cxIdeal P).minimalPrimes, ∀ z, z ∈ conePts Q →
      z ∈ conePts Q' → Ψ (segre z) = Fin.cons 1 y → Q' = Q := by
    intro Q hQ Q' hQ' z hz hz' hΨz
    by_contra hne
    refine hyN ⟨z, conePts_subset_mcPts_of_minimal hQ hz, hΨz, Q, hfin.mem_toFinset.2 hQ, Q',
      hfin.mem_toFinset.2 hQ', fun h => hne h.symm, ?_, ?_⟩
    · intro f hf
      simpa [MvPolynomial.coe_aeval_eq_eval] using hz.2 f hf
    · intro f hf
      simpa [MvPolynomial.coe_aeval_eq_eval] using hz'.2 f hf
  have hunion : fibre P Ψ y = ⋃ Q ∈ (cxIdeal P).minimalPrimes, setFibre (conePts Q) Ψ y := by
    ext w
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨z, hz, hzw, hΨw⟩
      obtain ⟨Q, hQ, hzQ⟩ := exists_minimal_of_mem_mcPts hz
      exact ⟨Q, hQ, z, hzQ, hzw, hΨw⟩
    · rintro ⟨Q, hQ, z, hz, hzw, hΨw⟩
      exact ⟨z, conePts_subset_mcPts_of_minimal hQ hz, hzw, hΨw⟩
  have hsub : ∀ Q ∈ (cxIdeal P).minimalPrimes, setFibre (conePts Q) Ψ y ⊆ fibre P Ψ y := by
    intro Q hQ w hw
    rw [hunion]
    exact Set.mem_biUnion hQ hw
  have hdisj : ((cxIdeal P).minimalPrimes).PairwiseDisjoint fun Q => setFibre (conePts Q) Ψ y := by
    intro Q hQ Q' hQ' hne
    refine Set.disjoint_left.2 ?_
    rintro w ⟨z, hz, hzw, hΨw⟩ ⟨z', hz', hzw', -⟩
    have hzQ' : z ∈ conePts Q' := mem_conePts_of_segre_eq hP hQ' hz' hz.1 (hzw'.trans hzw.symm)
    exact hne (hone Q hQ Q' hQ' z hz hzQ' (by rw [hzw]; exact hΨw)).symm
  rw [hunion, finsum_mem_biUnion hdisj hfin
    (fun Q hQ => (fibreFinite K ι P e Ψ hP hΨ y).subset (hsub Q hQ))]
  refine finsum_mem_congr rfl fun Q hQ => finsum_mem_congr rfl fun w hw => ?_
  refine congrArg abs ?_
  have hiff : (∃ γ, IsSheet P Ψ y w γ) ↔ ∃ γ, IsSetSheet (conePts Q) Ψ y w γ :=
    ⟨fun ⟨γ, h⟩ => ⟨γ, isSetSheet_of_isSheet hP hQ (hone Q hQ) hw h⟩,
      fun ⟨γ, h⟩ => ⟨γ, isSheet_of_isSetSheet hQ h⟩⟩
  rw [sheetDensity_eq_setSheetDensity]
  unfold setSheetDensity
  by_cases hex : ∃ γ, IsSheet P Ψ y w γ
  · have hexQ := hiff.1 hex
    have hexP : ∃ γ, IsSetSheet (mcPts P) Ψ y w γ := hex
    rw [dif_pos hexP, dif_pos hexQ]
    exact hind w _ _ hexP.choose_spec (isSheet_of_isSetSheet hQ hexQ.choose_spec)
  · have hexQ : ¬ ∃ γ, IsSetSheet (conePts Q) Ψ y w γ := fun h => hex (hiff.2 h)
    have hexP : ¬ ∃ γ, IsSetSheet (mcPts P) Ψ y w γ := hex
    rw [dif_neg hexP, dif_neg hexQ]

theorem abs_setSheetDensity_eq {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {e : ℕ}
    {S : Set ((Σ k, ι k) → ℂ)} (hS : ∀ z ∈ S, ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ)
    (A : HermLine ι) (s : MRingOver ℂ ι) (y : Fin e → ℂ) (w : ((k : K) → ι k) → ℂ) :
    |setSheetDensity S Ψ φ (logNormC A s) y w| =
      max (setSheetDensity S Ψ φ (absLogNorm A s) y w) 0 +
        max (setSheetDensity S Ψ φ (fun z => -absLogNorm A s z) y w) 0 := by
  unfold setSheetDensity
  split_ifs with hγ
  · have hz := hS _ hγ.choose_spec.2.self_of_nhds.2.1
    have ha : absLogNorm A s (hγ.choose y) = |logNormC A s (hγ.choose y)| := by
      simp only [absLogNorm, if_pos hz]
    beta_reduce
    rw [ha, abs_mul]
    generalize maDensity (fun j y' => φ j (hγ.choose y')) y = m
    generalize logNormC A s (hγ.choose y) = g
    have hg := abs_nonneg g
    rcases le_total 0 m with hm | hm
    · rw [abs_of_nonneg hm, max_eq_left (mul_nonneg hg hm),
        max_eq_right (by nlinarith : -|g| * m ≤ 0), add_zero]
    · rw [abs_of_nonpos hm, max_eq_right (by nlinarith : |g| * m ≤ 0),
        max_eq_left (by nlinarith : 0 ≤ -|g| * m), zero_add]
      ring
  · simp

theorem integrable_absFibreSum_of_isCxVar {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {Q : Ideal (MRingOver ℂ ι)} {e : ℕ} {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)}
    {L : Fin e → HermLine ι} {A : HermLine ι} {s : MRingOver ℂ ι} {a : K → ℕ}
    (hQ : IsCxVar Q e) (hΨ : IsSetGoodProj (conePts Q) Ψ) (hL : ∀ j, IsSmoothHerm (L j))
    (hA : IsSmoothHerm A) (hAa : ∀ k, A.a k = a k) (hs : IsMultiHomog s a) (hsQ : s ∉ Q) :
    Integrable (fun y => ∑ᶠ w ∈ setFibre (conePts Q) Ψ y,
      |setSheetDensity (conePts Q) Ψ (pot L) (logNormC A s) y w|) := by
  classical
  have hS : ∀ z ∈ conePts Q, ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0 := fun z hz => hz.1
  have hfin := GlobalTheory.CompanionTheory.Ar.Pub.CxFib.setFibre_finite K ι Q e Ψ hQ hΨ
  have hm := GlobalTheory.CompanionTheory.Ar.Pub.CxChart.measurable_absLogNorm A hA s
  have hdeg := fun (c : K → ℂ) (z : (Σ k, ι k) → ℂ) (hc : ∀ k, c k ≠ 0) =>
    GlobalTheory.CompanionTheory.Ar.Pub.CxChart.absLogNorm_blockScale A hAa hs hc z
  have h1 := GlobalTheory.CompanionTheory.Ar.Pub.CxPosMeas.cxPosDens_aemeasurable_of_finite hS hfin hL hm hdeg
  have h2 := GlobalTheory.CompanionTheory.Ar.Pub.CxPosMeas.cxPosDens_aemeasurable_of_finite hS hfin hL hm.neg
    (g := fun z => -absLogNorm A s z) (fun c z hc => by simp only [hdeg c z hc])
  have heq : (fun y => ∑ᶠ w ∈ setFibre (conePts Q) Ψ y,
      |setSheetDensity (conePts Q) Ψ (pot L) (logNormC A s) y w|) =
      fun y => cxPosDens (conePts Q) Ψ (pot L) (absLogNorm A s) y +
        cxPosDens (conePts Q) Ψ (pot L) (fun z => -absLogNorm A s z) y := by
    funext y
    unfold cxPosDens
    rw [finsum_mem_eq_finite_toFinset_sum _ (hfin y), finsum_mem_eq_finite_toFinset_sum _ (hfin y),
      finsum_mem_eq_finite_toFinset_sum _ (hfin y), ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun w _ => abs_setSheetDensity_eq hS Ψ (pot L) A s y w
  refine ⟨?_, (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun y =>
    finsum_nonneg fun w => finsum_nonneg fun _ => abs_nonneg _)).2
    (GlobalTheory.T.lintegral_fibre_logNorm_finite K ι Q e Ψ L A s a hQ hΨ hL hA hAa hs hsQ)⟩
  rw [heq]
  exact (h1.add h2).aestronglyMeasurable

theorem ptsAbsIntegrable : GroundTheory.Heights₂.Heights.Inter.PtsAbsIntegrable.Statement := by
  intro K _ ι _ P e Ψ L A s hP hΨ hL hA hs
  classical
  have hae := absFibreSum_eq_sum_components_ae hP hΨ hL hA hs
  obtain ⟨a, hAa, hsa, hsP⟩ := hs
  have hfin : (cxIdeal P).minimalPrimes.Finite := Ideal.finite_minimalPrimes_of_isNoetherianRing _ _
  have hsa' : IsMultiHomog (map (Int.castRingHom ℂ) s : MRingOver ℂ ι) a := fun m hm k =>
    hsa m (support_map_subset _ _ hm) k
  have hcomp : ∀ Q ∈ (cxIdeal P).minimalPrimes, Integrable (fun y => ∑ᶠ w ∈ setFibre (conePts Q) Ψ y,
      |setSheetDensity (conePts Q) Ψ (pot L) (logNormC A (map (Int.castRingHom ℂ) s)) y w|) := by
    intro Q hQ
    obtain ⟨hQv, hc⟩ := isCxVar_of_mem_minimalPrimes_cxIdeal K ι P e hP Q hQ
    refine integrable_absFibreSum_of_isCxVar hQv
      (fun z hz => hΨ z (conePts_subset_mcPts_of_minimal hQ hz)) hL hA hAa hsa' fun hmem => hsP ?_
    rw [← hc]
    exact hmem
  refine (integrable_finset_sum hfin.toFinset fun Q hQ => hcomp Q (hfin.mem_toFinset.1 hQ)).congr ?_
  filter_upwards [hae] with y hy
  rw [hy]
  exact (finsum_mem_eq_finite_toFinset_sum _ hfin).symm

end GlobalTheory.CompanionTheory.Ar.Pub.CxAbs
