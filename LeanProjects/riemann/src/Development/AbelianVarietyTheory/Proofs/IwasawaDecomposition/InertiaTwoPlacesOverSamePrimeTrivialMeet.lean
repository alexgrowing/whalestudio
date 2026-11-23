import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeIdempotentCoeffAcrossLayers
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IwasawaDecompositionFactStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntegerDeepAtOnePlaceUnitAtOtherStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInertiaFixedIntegralOfSeparatingElementStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInertiaFixedRootsPerturbedPolynomialStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.InertiaTwoPlaces

open Polynomial

theorem fix_of_fix_integral {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (σ : G E Ω) (h : ∀ b : Ω, IsIntegral ℤ b → σ b = b) : σ = 1 := by
  ext x
  obtain ⟨s, t, hs, ht, hs1, e⟩ := ReciprocityTheory.Gal.exists_den E (⊤ : ValuationSubring Ω) (x := x)
    ((ValuationSubring.valuation_le_one_iff _ _).mpr trivial)
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs1
  have h2 : σ s * σ x = σ t := by rw [← map_mul, e]
  rw [h s hs, h t ht, ← e] at h2
  exact mul_left_cancel₀ hs0 h2

theorem eq_of_mem_Ine_of_mem_Ine : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (A A' : ValuationSubring Ω) (P : HeightOneSpectrum (𝓞 E)),
    IsPlaceOver (F := E) A P → IsPlaceOver (F := E) A' P → ∀ σ ∈ Ine (F := E) A,
    σ ∈ Ine (F := E) A' → σ ≠ 1 → A' = A := by
  intro E Ω _ _ _ _ _ A A' P hA hA' σ hσ hσ' hne
  by_contra hAA
  apply hne
  apply fix_of_fix_integral
  intro b hb
  by_contra hD
  have hD0 : σ b - b ≠ 0 := sub_ne_zero.mpr hD
  set f0 := minpoly ℤ b with hf0
  have hf0m : f0.Monic := minpoly.monic hb
  have hf0b : Polynomial.aeval b f0 = 0 := minpoly.aeval ℤ b
  set d := f0.natDegree with hd
  have hnat : ∀ n : ℕ, A'.valuation (n : Ω) ≤ 1 := fun n => ReciprocityTheory.Gal.valuation_natCast_le_one A' n
  obtain ⟨m, hdm, hmu⟩ : ∃ m : ℕ, d ≤ m ∧ A'.valuation (m : Ω) = 1 := by
    by_cases h1 : A'.valuation (d : Ω) = 1
    · exact ⟨d, le_rfl, h1⟩
    refine ⟨d + 1, Nat.le_succ d, ?_⟩
    by_contra h2
    have l1 : A'.valuation (d : Ω) < 1 := lt_of_le_of_ne (hnat d) h1
    have l2 : A'.valuation ((d + 1 : ℕ) : Ω) < 1 := lt_of_le_of_ne (hnat _) h2
    have : A'.valuation (((d + 1 : ℕ) : Ω) - (d : Ω)) < 1 := by
      rw [sub_eq_add_neg]
      exact Valuation.map_add_lt _ l2 (by rw [Valuation.map_neg]; exact l1)
    push_cast at this
    simp at this
  set f1 : Polynomial ℤ := Polynomial.X ^ (m - d) * f0 with hf1
  have hf1m : f1.Monic := (Polynomial.monic_X_pow _).mul hf0m
  have hf1d : f1.natDegree = m := by
    rw [hf1, (Polynomial.monic_X_pow _).natDegree_mul hf0m, Polynomial.natDegree_X_pow, ← hd]
    omega
  have hf1b : Polynomial.aeval b f1 = 0 := by simp [hf1, hf0b]
  have hσA : σ ∈ Dec (F := E) A := Ine_le_Dec A hσ
  have hbD : IsIntegral ℤ (σ b - b) :=
    (hb.map ((σ : Ω ≃ₐ[E] Ω).toAlgHom.restrictScalars ℤ)).sub hb
  have hc : IsIntegral ℤ ((σ b - b) ^ m) := hbD.pow m
  have hc0 : (σ b - b) ^ m ≠ 0 := pow_ne_zero _ hD0
  obtain ⟨e0, he0i, he0A, he0A'⟩ := GlobalTheory.T.exists_integer_deep_at_one_place_unit_at_other E Ω A A' P hA hA' (Ne.symm hAA) _ hc hc0
  obtain ⟨e, hei, hef, heA, heA'⟩ := GlobalTheory.T.exists_inertiaFixed_integral_of_separating_element E Ω A A' σ hσ' e0 _ he0i he0A he0A'
  obtain ⟨ys, hcard, hys, hprod⟩ := GlobalTheory.T.exists_inertia_fixed_roots_perturbed_polynomial E Ω A' σ hσ' b e m f1 hei hef heA' hmu hf1m hf1d hf1b
  have hbm : A.valuation (b ^ m - 1) ≤ 1 :=
    (A.valuation_le_one_iff _).mpr (ReciprocityTheory.Gal.mem_of_isIntegral_int A ((hb.pow m).sub isIntegral_one))
  have h1 : A.valuation (e * (b ^ m - 1)) < A.valuation (σ b - b) ^ m := by
    rw [Valuation.map_mul, ← Valuation.map_pow]
    calc A.valuation e * A.valuation (b ^ m - 1) ≤ A.valuation e * 1 := mul_le_mul_of_nonneg_left hbm zero_le'
      _ = A.valuation e := mul_one _
      _ < _ := heA
  have h2 : A.valuation (σ b - b) ^ m ≤ A.valuation ((ys.map (fun y => b - y)).prod) := by
    rw [map_multiset_prod, Multiset.map_map, ← hcard]
    rw [← Multiset.card_map (fun y => A.valuation (b - y)) ys]
    apply Multiset.pow_card_le_prod
    intro z hz
    rw [Multiset.mem_map] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    have hyf := (hys y hy).2
    have e1 : σ b - b = σ (b - y) - (b - y) := by rw [map_sub, hyf]; ring
    rw [e1, sub_eq_add_neg]
    refine (Valuation.map_add _ _ _).trans ?_
    rw [Valuation.map_neg, GlobalTheory.T.iwasawaDecomposition_fact E Ω A σ hσA, max_self]
  rw [← hprod] at h2
  exact absurd h2 (not_le.mpr h1)

end GlobalTheory.InertiaTwoPlaces
