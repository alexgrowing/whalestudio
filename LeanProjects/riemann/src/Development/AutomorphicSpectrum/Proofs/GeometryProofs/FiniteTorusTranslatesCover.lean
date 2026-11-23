import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsPeriodAtRestrict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FiniteMinimalPrimes
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SncResolutionRegularLocalRingStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SncResolutionCoverAndCone
import ReciprocityTheory.AnalyticForms.RegularLocalRings.AnChart
import ReciprocityTheory.AnalyticForms.RegularLocalRings.LocTransfer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterAlgRes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterMinor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open MvPolynomial

namespace GlobalTheory.CompanionTheory.Ar.ChartCover

private lemma eval_eq_zero_of_mem_mcPts' {K : Type} {J : K → Type}
    (P : Ideal (MRing J)) (z : (Σ k, J k) → ℂ) (hz : z ∈ mcPts P) :
    ∀ g ∈ pC P, MvPolynomial.eval z g = 0 := by
  intro g hg
  simp only [mcPts, Set.mem_ofPred_eq] at hz
  have hle : pC P ≤ RingHom.ker (MvPolynomial.eval z) := by
    unfold pC
    rw [Ideal.span_le]
    rintro _ ⟨f, hf, rfl⟩
    exact RingHom.mem_ker.mpr (hz.2 f hf)
  exact RingHom.mem_ker.mp (hle hg)

private lemma torusSmul_mem_mcPts' {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]
    (P : Ideal (MRing J)) (hP : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal (pC P))
    (c : K → ℂ) (hc : ∀ k, c k ≠ 0) (z : (Σ k, J k) → ℂ) (hz : z ∈ mcPts P) :
    torusSmul c z ∈ mcPts P := by
  have hv := eval_eq_zero_of_mem_mcPts' P z hz
  simp only [mcPts, Set.mem_ofPred_eq] at hz ⊢
  refine ⟨fun k => ?_, fun f hf => ?_⟩
  · obtain ⟨i, hi⟩ := hz.1 k
    exact ⟨i, mul_ne_zero (hc k) hi⟩
  · have hmem : MvPolynomial.map (Int.castRingHom ℂ) f ∈ pC P := by
      unfold pC
      exact Ideal.subset_span ⟨f, hf, rfl⟩
    exact ReciprocityTheory.AnForm.R.eval_eq_zero_of_smul hP c z hv _ hmem

theorem mcPts_finite_cover_up_to_torus :
    ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (P : Ideal (MRing J))
    (hP : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal (pC P)) (C : Type) (O : C → Set ((Σ k, J k) → ℂ)),
    (∀ i, IsOpen (O i)) → (∀ z ∈ mcPts P, ∃ i, z ∈ O i) →
    ∃ (m : ℕ) (e : Fin m → C), ∀ z ∈ mcPts P, ∃ (a : Fin m) (c : K → ℂ), (∀ k, c k ≠ 0) ∧
      torusSmul c z ∈ O (e a) ∧ torusSmul c z ∈ mcPts P := by
  intro K _ J _ P hP C O hO hcov
  classical
  set S : Set ((Σ k, J k) → ℂ) :=
    {w | (∀ k, ∑ i, ‖w ⟨k, i⟩‖ ^ 2 = 1) ∧
      ∀ f ∈ P, MvPolynomial.eval w (MvPolynomial.map (Int.castRingHom ℂ) f) = 0} with hS
  have hSsub : S ⊆ mcPts P := by
    intro w hw
    simp only [hS, Set.mem_ofPred_eq] at hw
    simp only [mcPts, Set.mem_ofPred_eq]
    refine ⟨fun k => ?_, hw.2⟩
    by_contra h
    push Not at h
    have h1 := hw.1 k
    simp [h] at h1
  have hScl : IsClosed S := by
    rw [hS]
    simp only [Set.ofPred_and, Set.ofPred_forall]
    refine IsClosed.inter (isClosed_iInter fun k => ?_)
      (isClosed_iInter fun f => isClosed_iInter fun _ => ?_)
    · exact isClosed_eq (continuous_finsetSum _ fun i _ =>
        (continuous_norm.comp (continuous_apply _)).pow 2) continuous_const
    · exact isClosed_eq (MvPolynomial.continuous_eval _) continuous_const
  have hSb : Bornology.IsBounded S := by
    refine (Metric.isBounded_closedBall (x := (0 : (Σ k, J k) → ℂ)) (r := 1)).subset ?_
    intro w hw
    simp only [hS, Set.mem_ofPred_eq] at hw
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
    rintro ⟨k, i⟩
    have h2 : ‖w ⟨k, i⟩‖ ^ 2 ≤ 1 := by
      rw [← hw.1 k]
      exact Finset.single_le_sum (f := fun j => ‖w ⟨k, j⟩‖ ^ 2) (fun j _ => sq_nonneg _)
        (Finset.mem_univ i)
    nlinarith [norm_nonneg (w ⟨k, i⟩)]
  have hScpt : IsCompact S := Metric.isCompact_of_isClosed_isBounded hScl hSb
  obtain ⟨t, ht⟩ := hScpt.elim_finite_subcover O hO
    (fun w hw => Set.mem_iUnion.2 (hcov w (hSsub hw)))
  refine ⟨t.card, fun a => (t.equivFin.symm a : C), ?_⟩
  intro z hz
  have hz0 := hz
  simp only [mcPts, Set.mem_ofPred_eq] at hz0
  have hpos : ∀ k, 0 < ∑ i, ‖z ⟨k, i⟩‖ ^ 2 := by
    intro k
    obtain ⟨i, hi⟩ := hz0.1 k
    exact lt_of_lt_of_le (pow_pos (norm_pos_iff.2 hi) 2)
      (Finset.single_le_sum (f := fun j => ‖z ⟨k, j⟩‖ ^ 2) (fun j _ => sq_nonneg _)
        (Finset.mem_univ i))
  set c : K → ℂ := fun k => (((Real.sqrt (∑ i, ‖z ⟨k, i⟩‖ ^ 2))⁻¹ : ℝ) : ℂ) with hcdef
  have hc : ∀ k, c k ≠ 0 := by
    intro k
    rw [hcdef]
    simp only [ne_eq, Complex.ofReal_eq_zero, inv_eq_zero]
    exact (Real.sqrt_pos.2 (hpos k)).ne'
  have hck : ∀ k, ‖c k‖ ^ 2 = (∑ i, ‖z ⟨k, i⟩‖ ^ 2)⁻¹ := by
    intro k
    rw [hcdef]
    simp only
    rw [Complex.norm_real, norm_inv, Real.norm_of_nonneg (Real.sqrt_nonneg _), inv_pow,
      Real.sq_sqrt (hpos k).le]
  have hmem := torusSmul_mem_mcPts' P hP c hc z hz
  have hw : torusSmul c z ∈ S := by
    have hm := hmem
    simp only [mcPts, Set.mem_ofPred_eq] at hm
    simp only [hS, Set.mem_ofPred_eq]
    refine ⟨fun k => ?_, hm.2⟩
    have e1 : ∀ i, ‖torusSmul c z ⟨k, i⟩‖ ^ 2 = ‖c k‖ ^ 2 * ‖z ⟨k, i⟩‖ ^ 2 := fun i => by
      show ‖c k * z ⟨k, i⟩‖ ^ 2 = _
      rw [norm_mul, mul_pow]
    rw [Finset.sum_congr rfl (fun i _ => e1 i), ← Finset.mul_sum, hck k,
      inv_mul_cancel₀ (hpos k).ne']
  have hcov' := ht hw
  simp only [Set.mem_iUnion] at hcov'
  obtain ⟨i, hi, hiO⟩ := hcov'
  refine ⟨t.equivFin ⟨i, hi⟩, c, hc, ?_, hmem⟩
  show torusSmul c z ∈ O ((t.equivFin.symm (t.equivFin ⟨i, hi⟩) : C))
  rw [Equiv.symm_apply_apply]
  exact hiO

end GlobalTheory.CompanionTheory.Ar.ChartCover
