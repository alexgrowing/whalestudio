import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSncModel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.ContinuousAtOfClosedRel
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNonvanishingDense
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRatPrimeDense
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PFiniteSeparatingModel
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRootsNear
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNoetherProjection
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRootsLiftToZeros
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRootsBounded
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPolyNonvanishDense

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

namespace PositivityTheory.UnitarySelfGeneration

private theorem rootsLiftToZeros_statement : GroundTheory.Heights₂.Heights.HilbertSamuel.RootsLiftToZeros.Statement := by
  intro σ P e ℓ u G hint hdiv y t hG
  classical
  let ψ : Polynomial (MvPolynomial (Fin e) ℚ) →+* MvPolynomial σ ℚ ⧸ P :=
    (Ideal.Quotient.mk P).comp (Polynomial.eval₂RingHom (aeval ℓ).toRingHom u)
  let φ : Polynomial (MvPolynomial (Fin e) ℚ) →+* ℂ := Polynomial.eval₂RingHom (aeval y).toRingHom t
  letI : Algebra (Polynomial (MvPolynomial (Fin e) ℚ)) (MvPolynomial σ ℚ ⧸ P) := ψ.toAlgebra
  have hψ : ∀ a, algebraMap (Polynomial (MvPolynomial (Fin e) ℚ)) (MvPolynomial σ ℚ ⧸ P) a =
      Ideal.Quotient.mk P (Polynomial.eval₂ (aeval ℓ).toRingHom u a) := fun a => rfl
  haveI : Algebra.IsIntegral (Polynomial (MvPolynomial (Fin e) ℚ)) (MvPolynomial σ ℚ ⧸ P) := by
    constructor
    intro s
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective s
    obtain ⟨p, hpm, hp⟩ := hint g
    refine ⟨p.map Polynomial.C, hpm.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have hc : (algebraMap (Polynomial (MvPolynomial (Fin e) ℚ)) (MvPolynomial σ ℚ ⧸ P)).comp Polynomial.C =
        (Ideal.Quotient.mk P).comp (aeval ℓ).toRingHom := by
      refine RingHom.ext fun a => ?_
      rw [RingHom.comp_apply, hψ, Polynomial.eval₂_C]
      rfl
    rw [hc, ← Polynomial.hom_eval₂]
    exact Ideal.Quotient.eq_zero_iff_mem.2 hp
  haveI : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  obtain ⟨Q, -, hQ, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (RingHom.ker φ) (⊥ : Ideal (MvPolynomial σ ℚ ⧸ P)) (by
    intro a ha
    rw [Ideal.mem_comap, Ideal.mem_bot, hψ] at ha
    obtain ⟨H, rfl⟩ := hdiv a (Ideal.Quotient.eq_zero_iff_mem.1 ha)
    simp only [RingHom.mem_ker, φ, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_mul, mul_eq_zero]
    left
    exact hG)
  letI : Algebra (Polynomial (MvPolynomial (Fin e) ℚ) ⧸
      Q.comap (algebraMap (Polynomial (MvPolynomial (Fin e) ℚ)) (MvPolynomial σ ℚ ⧸ P))) ℂ :=
    (Ideal.Quotient.lift _ φ (fun a ha => by rw [hQc] at ha; exact ha)).toAlgebra
  haveI : IsDomain ((MvPolynomial σ ℚ ⧸ P) ⧸ Q) := Ideal.Quotient.isDomain Q
  haveI : Module.IsTorsionFree (Polynomial (MvPolynomial (Fin e) ℚ) ⧸
      Q.comap (algebraMap (Polynomial (MvPolynomial (Fin e) ℚ)) (MvPolynomial σ ℚ ⧸ P))) ((MvPolynomial σ ℚ ⧸ P) ⧸ Q) :=
    Module.isTorsionFree_iff_algebraMap_injective.2 Ideal.algebraMap_quotient_injective
  haveI : Module.IsTorsionFree (Polynomial (MvPolynomial (Fin e) ℚ) ⧸
      Q.comap (algebraMap (Polynomial (MvPolynomial (Fin e) ℚ)) (MvPolynomial σ ℚ ⧸ P))) ℂ := by
    rw [Module.isTorsionFree_iff_algebraMap_injective, RingHom.injective_iff_ker_eq_bot, eq_bot_iff]
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [RingHom.mem_ker] at hx
    rw [Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem, hQc]
    exact hx
  haveI : Algebra.IsIntegral (Polynomial (MvPolynomial (Fin e) ℚ) ⧸
      Q.comap (algebraMap (Polynomial (MvPolynomial (Fin e) ℚ)) (MvPolynomial σ ℚ ⧸ P))) ((MvPolynomial σ ℚ ⧸ P) ⧸ Q) :=
    ⟨RingHom.IsIntegral.quotient _ Algebra.IsIntegral.isIntegral⟩
  haveI : Algebra.IsAlgebraic (Polynomial (MvPolynomial (Fin e) ℚ) ⧸
      Q.comap (algebraMap (Polynomial (MvPolynomial (Fin e) ℚ)) (MvPolynomial σ ℚ ⧸ P))) ((MvPolynomial σ ℚ ⧸ P) ⧸ Q) :=
    Algebra.IsIntegral.isAlgebraic
  let χ0 := IsAlgClosed.lift (M := ℂ) (R := Polynomial (MvPolynomial (Fin e) ℚ) ⧸
      Q.comap (algebraMap (Polynomial (MvPolynomial (Fin e) ℚ)) (MvPolynomial σ ℚ ⧸ P))) (S := (MvPolynomial σ ℚ ⧸ P) ⧸ Q)
  let χ : MvPolynomial σ ℚ →+* ℂ := (χ0 : (MvPolynomial σ ℚ ⧸ P) ⧸ Q →+* ℂ).comp
    ((Ideal.Quotient.mk Q).comp (Ideal.Quotient.mk P))
  have key : ∀ a, χ (Polynomial.eval₂ (aeval ℓ).toRingHom u a) = φ a := by
    intro a
    have h1 := χ0.commutes (Ideal.Quotient.mk _ a)
    exact h1
  have hχ : ∀ g, aeval (fun i => χ (X i)) g = χ g := by
    intro g
    have : (aeval (fun i => χ (X i))).toRingHom = χ :=
      MvPolynomial.ringHom_ext (fun r => RingHom.congr_fun
        (Subsingleton.elim ((aeval (fun i => χ (X i))).toRingHom.comp C) (χ.comp C)) r) (fun i => by simp)
    exact RingHom.congr_fun this g
  refine ⟨fun i => χ (X i), ?_, ?_, ?_⟩
  · intro g hg
    rw [hχ]
    show χ0 (Ideal.Quotient.mk Q (Ideal.Quotient.mk P g)) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.2 hg, map_zero, map_zero]
  · funext j
    rw [hχ]
    have := key (Polynomial.C (X j))
    simpa [φ] using this
  · rw [hχ]
    have := key Polynomial.X
    simpa [φ] using this

open GroundTheory.Heights₂.Heights.HilbertSamuel in
theorem nonvanishing_dense : NonvanishingDense.Statement := by
  have hR : RatPrimeDense.Statement := RatPrimeDense.proof (FiniteSeparatingModel.proof NoetherProjection.proof rootsLiftToZeros_statement) RootsNear.proof RootsBounded.proof PolyNonvanishDense.proof
  revert hR
  intro hR
  intro K _ ι _ P d f hP hfP
  classical
  have hprime : P.IsPrime := hP.2.1.1
  have hhor : IsHorizontal P := hP.2.2.1
  letI : Algebra (MvPolynomial (Σ k, ι k) ℤ) (MvPolynomial (Σ k, ι k) ℚ) :=
    MvPolynomial.algebraMvPolynomial
  have halg : algebraMap (MvPolynomial (Σ k, ι k) ℤ) (MvPolynomial (Σ k, ι k) ℚ) =
      MvPolynomial.map (Int.castRingHom ℚ) := by
    rw [MvPolynomial.algebraMap_def]
    congr 1
  have hdisj : Disjoint ((Submonoid.map (C (σ := Σ k, ι k)) (nonZeroDivisors ℤ) : Submonoid _) : Set (MvPolynomial (Σ k, ι k) ℤ)) (P : Set _) := by
    rw [Set.disjoint_left]
    rintro _ ⟨n, hn, rfl⟩ hnP
    have : n ∈ Ideal.comap (C : ℤ →+* MvPolynomial (Σ k, ι k) ℤ) P := hnP
    rw [hhor, Ideal.mem_bot] at this
    exact nonZeroDivisors.ne_zero hn this
  have hP'prime := IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.map (C (σ := Σ k, ι k)) (nonZeroDivisors ℤ)) (MvPolynomial (Σ k, ι k) ℚ) P hprime hdisj
  have hcomap := IsLocalization.comap_map_of_isPrime_disjoint (Submonoid.map (C (σ := Σ k, ι k)) (nonZeroDivisors ℤ)) (MvPolynomial (Σ k, ι k) ℚ) hprime hdisj
  rw [halg] at hP'prime hcomap
  set P' := Ideal.map (MvPolynomial.map (Int.castRingHom ℚ)) P with hP'
  have hf' : MvPolynomial.map (Int.castRingHom ℚ) f ∉ P' := by
    intro h
    apply hfP
    rw [← hcomap]
    exact h
  have hzero : ∀ z : (Σ k, ι k) → ℂ, (∀ g ∈ P', aeval z g = 0) ↔ (∀ g ∈ P, eval z (MvPolynomial.map (Int.castRingHom ℂ) g) = 0) := by
    intro z
    constructor
    · intro h g hg
      rw [← NonvanishingDense.aeval_map_rat]
      exact h _ (Ideal.mem_map_of_mem _ hg)
    · intro h g hg
      have hle : P' ≤ RingHom.ker (aeval z : MvPolynomial (Σ k, ι k) ℚ →ₐ[ℚ] ℂ).toRingHom := by
        rw [hP', Ideal.map_le_iff_le_comap]
        intro a ha
        rw [Ideal.mem_comap, RingHom.mem_ker]
        show aeval z (MvPolynomial.map (Int.castRingHom ℚ) a) = 0
        rw [NonvanishingDense.aeval_map_rat]
        exact h a ha
      exact hle hg
  have hO : IsOpen {w : (Σ k, ι k) → ℂ | ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0} := by
    simp only [Set.setOf_forall, Set.setOf_exists]
    exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
      isOpen_ne_fun (continuous_apply _) continuous_const
  intro z hz
  have hzP' : ∀ g ∈ P', aeval z g = 0 := (hzero z).2 hz.2
  have hcl := hR (Σ k, ι k) P' (MvPolynomial.map (Int.castRingHom ℚ) f) hP'prime hf' hzP'
  refine closure_mono ?_ (hO.inter_closure ⟨hz.1, hcl⟩)
  rintro w ⟨hw1, hw2, hw3⟩
  refine ⟨⟨hw1, (hzero w).1 hw2⟩, ?_⟩
  rw [← NonvanishingDense.aeval_map_rat]
  exact hw3

open HolomorphicMinorCharts in
theorem r_onto : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (e : ℕ) (R : AnLogRes P J e), IsArithVar P (e + 1) → ∀ z ∈ mcPts P, ∃ x, SameOrbit (R.lift x x) z := by
  intro K _ ι _ P J e R hP z hz
  obtain ⟨f, hfJ, hfP⟩ := Set.not_subset.mp R.nondeg
  have hcl := isClosed_minors (U := R.U) (lam := R.lift) (V := fun _ : (Σ k, ι k) → ℂ => Set.univ)
    (mu := fun _ w => w) (fun x => ⟨R.isOpen_U x, R.mem_U x⟩)
    (fun x p => holo_continuousAt (R.holo x p) (R.mem_U x)) R.compat (fun _ => ⟨isOpen_univ, trivial⟩)
    (fun y p => (continuous_apply p).continuousAt) (fun _ _ w _ => so_refl w)
  have hc := isClosedMap_snd_of_compactSpace _ hcl
  have h1 := nonvanishing_dense K ι P (e + 1) f hP hfP hz
  have h2 := closure_minimal (fun w hw => by
    obtain ⟨x, hx⟩ := R.surj w hw.1 fun hJ => hw.2 (hJ.2 f hfJ)
    exact ⟨(x, w), minors_of_so hx, rfl⟩) hc h1
  obtain ⟨⟨x, w⟩, hx, rfl⟩ := h2
  exact ⟨x, so_of_minors hx (R.mem x x (R.mem_U x)).1 hz.1⟩

end PositivityTheory.UnitarySelfGeneration
