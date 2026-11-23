import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.LocalPairPowerSumValueStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CycleNumberMulExpandStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.LocalPairValueLinearStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.VerticalPairPowerSumVanishStatement
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)

theorem GlobalTheory.CompanionTheory.Ar.Num.power_sum_term_dvr : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P d → ∀ (p : ℕ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (φ : Equiv.Perm (Ψ ⊕ Ψ)) (k : ℕ), 1 ≤ k → k ≤ d + 1 → ∀ (τ : Ψ) (Q : MvPolynomial (Ψ × Fin N) ℝ) (Hs : Ψ × Fin N → MvPolynomial ((Ψ × Fin N) ⊕ (Ψ × Fin N)) ℝ), Q.IsHomogeneous (d + 1 - k) → (∀ i, (Hs i).IsHomogeneous (d - k)) → (k = d + 1 → ∀ i, Hs i = 0) → ∀ T : LocPair ι O (Ψ × Fin N), T.IsVert P ϖ → FlagChernComparison P d p j φ T → PowerSumsVanish P d (fun i : Fin N => T.x' (τ, i)) → T.val P (fun i => (∑ a ∈ Finset.univ.filter (fun a : Fin N => (τ, a) = i), rename (Sum.map (fun a => (τ, a)) (fun a => (τ, a))) (MvPolynomial.map (Int.castRingHom ℝ) (psumExpansion N k a))) * rename Sum.inl Q + (∑ a : Fin N, X (Sum.inr (τ, a)) ^ k) * Hs i) = cycNum (divCycle P (C (p : O))) T.x (bracket j φ p k τ * Q) [] := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP p Ψ _ _ N j φ k hk1 hkd τ Q Hs hQ hHs hH0 T hT hM hPS
  obtain ⟨hadd, hsmul, -⟩ := GlobalTheory.T.local_pair_value_linear O K ι (Ψ × Fin N) T P
  have hB : T.val P (fun i => (∑ a : Fin N, X (Sum.inr (τ, a)) ^ k) * Hs i) = 0 := by
    rcases Nat.lt_or_ge k (d + 1) with hlt | hge
    · exact GlobalTheory.T.vertical_pair_power_sum_vanish O ϖ hϖ K ι P d hP (Ψ × Fin N) T hT N (fun a => (τ, a)) hPS k (d - k) hk1
        (by omega) Hs hHs
    · have hk : k = d + 1 := by omega
      have h0 := hsmul 0 (fun _ => 0)
      simp only [mul_zero, zero_mul] at h0
      have hfun : (fun i => (∑ a : Fin N, X (Sum.inr (τ, a)) ^ k) * Hs i) =
          (fun _ => (0 : MvPolynomial ((Ψ × Fin N) ⊕ (Ψ × Fin N)) ℝ)) := by
        funext i
        rw [hH0 hk i, mul_zero]
      rw [hfun]
      exact h0
  have hA : T.val P (fun i => (∑ a ∈ Finset.univ.filter (fun a : Fin N => (τ, a) = i),
        rename (Sum.map (fun a => (τ, a)) (fun a => (τ, a)))
          (MvPolynomial.map (Int.castRingHom ℝ) (psumExpansion N k a))) * rename Sum.inl Q) =
      cycNum (divCycle P (C (p : O))) T.x (bracket j φ p k τ * Q) [] := by
    rw [GlobalTheory.T.local_pair_power_sum_value O K ι (Ψ × Fin N) T P N k (fun a => (τ, a)) (rename Sum.inl Q),
      support_rename_of_injective Sum.inl_injective,
      Finset.sum_image (Finsupp.mapDomain_injective Sum.inl_injective).injOn,
      GlobalTheory.T.cycle_number_mul_expand O K ι (Ψ × Fin N) (divCycle P (C (p : O))) T.x (bracket j φ p k τ) Q []]
    refine Finset.sum_congr rfl fun μ hμ => ?_
    have hcl : classList (Sum.elim T.x T.x') (Finsupp.mapDomain Sum.inl μ) = classList T.x μ := by
      have hm : Finsupp.toMultiset (Finsupp.mapDomain (Sum.inl : Ψ × Fin N → (Ψ × Fin N) ⊕ (Ψ × Fin N)) μ) =
          (Finsupp.toMultiset μ).map Sum.inl := (Finsupp.toMultiset_map μ Sum.inl).symm
      unfold classList
      rw [hm, Multiset.map_map]
      rfl
    have hdeg : (classList T.x μ).length + k = d + 1 := by
      have h1 : (classList T.x μ).length = d + 1 - k := by
        have h2 := hQ (mem_support_iff.mp hμ)
        unfold classList
        rw [Multiset.length_toList, Multiset.card_map, Finsupp.card_toMultiset]
        rw [Finsupp.weight_apply] at h2
        exact (by simpa using h2 : (μ.sum fun _ c => c) = d + 1 - k)
      omega
    rw [coeff_rename_mapDomain _ Sum.inl_injective, hcl, List.append_nil, hM τ k hk1 _ hdeg]
  exact (hadd _ _).trans (by rw [hA, hB, add_zero])
