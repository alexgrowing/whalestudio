import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsLatFlagPair
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MultihomogIdealEquivalenceStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RelevantPrimeOverMultihomogStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MultihomogComponentQuotientStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MultihomogNonvanishingRatioStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MultihomogRatioInductionStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MultihomogCoveringFormsStatement
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver)

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem twist_line : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MvPolynomial (Σ k, ι k) ℤ)) (D : ℕ), IsArithVar P (D + 1) → ∀ (S : Finset Nat.Primes) (T : LocPair ι ℤ Unit), T.IsVertOff P S → ∀ A : HermLine ι, A.a = T.x () → IsSmoothHerm A → IsConjInvariantH A → ∃ A' : HermLine ι, IsSmoothHerm A' ∧ IsConjInvariantH A' ∧ T.IsIsometric P (fun _ => A) (fun _ => A') := by
  intro K _ _ ι _ P D hP S T hT A hAx hAs hAc
  obtain ⟨_, ⟨hPp, hPh, _⟩, _, _⟩ := hP
  have hPh' := GlobalTheory.T.isMultiHomogIdeal_transfer K ι P hPh
  obtain ⟨⟨bf, bg, hf, hg, hdeg⟩, hfP, hgP, hW⟩ := hT ()
  generalize hfd : T.f () = f at *
  generalize hgd : T.g () = g at *
  let Q : (K → ℕ) → (K → ℕ) → MvPolynomial (Σ k, ι k) ℤ → MvPolynomial (Σ k, ι k) ℤ → Prop :=
    fun a b u v => GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog u a ∧
      GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog v b ∧ a + bf = b + bg ∧ u * f - v * g ∈ P
  have hQmul : ∀ (a b d : K → ℕ) (u v m : MvPolynomial (Σ k, ι k) ℤ), Q a b u v →
      GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog m d → Q (a + d) (b + d) (u * m) (v * m) := by
    rintro a b d u v m ⟨hu, hv, hab, hr⟩ hm
    refine ⟨hu.mul hm, hv.mul hm, ?_, ?_⟩
    · rw [add_right_comm, hab, add_right_comm]
    · have : u * m * f - v * m * g = m * (u * f - v * g) := by ring
      rw [this]
      exact P.mul_mem_left _ hr
  have hcompP : ∀ z ∈ mcPts P, ∀ (a : K → ℕ) (s : MvPolynomial (Σ k, ι k) ℤ),
      eval z (MvPolynomial.map (Int.castRingHom ℂ) s) ≠ 0 → s ∉ P := fun z hz _ s hs hm =>
    hs (hz.2 s hm)
  have hin : ∀ z ∈ mcPts P, (∃ (a b : K → ℕ) (u v : MvPolynomial (Σ k, ι k) ℤ), Q a b u v ∧
        eval z (MvPolynomial.map (Int.castRingHom ℂ) u) ≠ 0) ∧
      (∃ (a b : K → ℕ) (u v : MvPolynomial (Σ k, ι k) ℤ), Q a b u v ∧
        eval z (MvPolynomial.map (Int.castRingHom ℂ) v) ≠ 0) := by
    intro z hz
    obtain ⟨W, hWp, hPW, hWr, hWc, hWs⟩ := GlobalTheory.T.relevant_prime_over_multihomog K ι P z hPh' hz
    obtain ⟨u₀, v₀, hu₀, hv₀, hr⟩ := hW W hWp hPW hWr (fun p _ => hWc p)
    constructor
    · obtain ⟨a, ha⟩ := hWs u₀ hu₀
      obtain ⟨b, v, hv, hab, hr'⟩ := GlobalTheory.T.multihomog_component_quotient K ι P hPp hPh' f g u₀ v₀ bf bg a hf hg hfP hr
        (hcompP z hz a _ ha)
      exact ⟨a, b, _, v, ⟨weightedHomogeneousComponent_isWeightedHomogeneous a u₀, hv, hab, hr'⟩, ha⟩
    · obtain ⟨b, hb⟩ := hWs v₀ hv₀
      have hr₂ : v₀ * g - u₀ * f ∈ P := by
        have := P.neg_mem hr
        rwa [neg_sub] at this
      obtain ⟨a, u, hu, hab, hr'⟩ := GlobalTheory.T.multihomog_component_quotient K ι P hPp hPh' g f v₀ u₀ bg bf b hg hf hgP hr₂
        (hcompP z hz b _ hb)
      refine ⟨a, b, u, _, ⟨hu, weightedHomogeneousComponent_isWeightedHomogeneous b v₀, hab.symm, ?_⟩, hb⟩
      have := P.neg_mem hr'
      rwa [neg_sub] at this
  have hout : ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → z ∉ mcPts P →
      ∃ (a b : K → ℕ) (u v : MvPolynomial (Σ k, ι k) ℤ), Q a b u v ∧
        eval z (MvPolynomial.map (Int.castRingHom ℂ) u) ≠ 0 ∧
        eval z (MvPolynomial.map (Int.castRingHom ℂ) v) ≠ 0 := by
    intro z hc hz
    have : ∃ q ∈ P, eval z (MvPolynomial.map (Int.castRingHom ℂ) q) ≠ 0 := by
      by_contra hne
      push_neg at hne
      exact hz ⟨hc, hne⟩
    obtain ⟨q, hq, hqz⟩ := this
    obtain ⟨a, b, u, v, hu, hv, hab, huP, hvP, huz, hvz⟩ := GlobalTheory.T.multihomog_nonvanishing_ratio K ι P bf bg z q hPh' hc hq hqz
    refine ⟨a, b, u, v, ⟨hu, hv, hab, ?_⟩, huz, hvz⟩
    exact P.sub_mem (P.mul_mem_right _ huP) (P.mul_mem_right _ hvP)
  obtain ⟨Aₐ, B, n, u, v, hAB, hQ, hu, hv⟩ := GlobalTheory.T.multihomog_ratio_induction K ι Q bf bg hQmul (fun a b u v h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (fun z hc => by
      by_cases hz : z ∈ mcPts P
      · exact (hin z hz).1
      · obtain ⟨a, b, u, v, h, h1, _⟩ := hout z hc hz
        exact ⟨a, b, u, v, h, h1⟩)
    (fun z hc => by
      by_cases hz : z ∈ mcPts P
      · exact (hin z hz).2
      · obtain ⟨a, b, u, v, h, _, h1⟩ := hout z hc hz
        exact ⟨a, b, u, v, h, h1⟩)
  obtain ⟨A', ha', hs', hc', hh'⟩ := GlobalTheory.T.multihomog_covering_forms K ι A Aₐ B n u v (fun j => (hQ j).1) (fun j => (hQ j).2.1)
    hu hv hAs hAc
  refine ⟨A', hs', hc', fun _ => ⟨hAx, ?_, fun z hz => ?_⟩⟩
  · rw [ha', hAx]
    funext k
    have h1 := congrFun hdeg k
    have h2 : (Aₐ k : ℤ) + bf k = B k + bg k := by exact_mod_cast congrFun hAB k
    simp only [Pi.sub_apply] at h1
    linarith
  · show ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) (T.f ()))‖ * A'.h z =
      ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) (T.g ()))‖ * A.h z
    rw [hfd, hgd, hh']
    set fz := eval z (MvPolynomial.map (Int.castRingHom ℂ) f)
    set gz := eval z (MvPolynomial.map (Int.castRingHom ℂ) g)
    have hrel : ∀ j, ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) (u j))‖ ^ 2 * ‖fz‖ ^ 2 =
        ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) (v j))‖ ^ 2 * ‖gz‖ ^ 2 := by
      intro j
      have h0 := hz.2 _ (hQ j).2.2.2
      simp only [map_sub, map_mul] at h0
      have h1 := sub_eq_zero.mp h0
      have h2 := congrArg norm h1
      rw [norm_mul, norm_mul] at h2
      rw [← mul_pow, ← mul_pow, h2]
    have hD : 0 < ∑ j, ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) (v j))‖ ^ 2 := by
      obtain ⟨j, hj⟩ := hv z hz.1
      exact Finset.sum_pos' (fun _ _ => by positivity) ⟨j, Finset.mem_univ _, by positivity⟩
    have hsum : (∑ j, ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) (u j))‖ ^ 2) * ‖fz‖ ^ 2 =
        (∑ j, ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) (v j))‖ ^ 2) * ‖gz‖ ^ 2 := by
      rw [Finset.sum_mul, Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => hrel j
    have key : ‖fz‖ * Real.sqrt ((∑ j, ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) (u j))‖ ^ 2) /
        (∑ j, ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) (v j))‖ ^ 2)) = ‖gz‖ := by
      rw [← Real.sqrt_sq (norm_nonneg fz), ← Real.sqrt_mul (by positivity)]
      rw [show ‖fz‖ ^ 2 * ((∑ j, ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) (u j))‖ ^ 2) /
        (∑ j, ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) (v j))‖ ^ 2)) = ‖gz‖ ^ 2 by
        field_simp
        linarith]
      exact Real.sqrt_sq (norm_nonneg gz)
    calc ‖fz‖ * (A.h z * _) = (‖fz‖ * Real.sqrt _) * A.h z := by ring
      _ = ‖gz‖ * A.h z := by rw [key]

end GlobalTheory.CompanionTheory.Ar.Num
