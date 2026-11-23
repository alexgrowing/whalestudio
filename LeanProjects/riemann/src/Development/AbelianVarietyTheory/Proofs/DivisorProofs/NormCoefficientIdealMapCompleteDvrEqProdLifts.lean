import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationTransferModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanCoeffProdLinearStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAlgebraSplittingNormFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftToCompleteDvrOfFiniteStatement
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LocM

open MvPolynomial in

theorem GlobalTheory.NormSheaf.normIdeal_map_eq_prod_lifts : ∀ (A B K L : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CommRing B] [IsDomain B]
    [Field K] [Field L] [CharZero K] [Algebra A K] [Algebra B L] [Algebra K L] [FiniteDimensional K L]
    [IsFractionRing A K] [IsFractionRing B L] (φ : A →+* B), φ.Finite →
    (algebraMap K L).comp (algebraMap A K) = (algebraMap B L).comp φ → ∀ (J : Ideal B)
    (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V],
    IsAdicComplete (maximalIdeal V) V → ∀ h : A →+* V,
    ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V') (_ : CharZero V')
      (f : V →+* V') (ψ : Fin (Module.finrank K L) → (B →+* V')), IsAdicComplete (maximalIdeal V') V' ∧
      Function.Injective f ∧ IsLocalHom f ∧ (∀ j, (ψ j).comp φ = f.comp h) ∧
      (GlobalTheory.NormSheaf.normIdeal A K L B J).map (f.comp h) = ∏ j, J.map (ψ j) := by
  intro A B K L _ _ _ _ _ _ _ _ _ _ _ _ _ _ φ hφ hcomp J V _ _ _ _ hV h
  obtain ⟨R, _, _, hinj, hfin, σ, hσ, hP⟩ := GlobalTheory.T.exists_finite_algebra_splitting_normForm A B K L φ hφ hcomp
  obtain ⟨V', _, _, _, _, f, ρ, hV', hf, hloc, hρ⟩ := GlobalTheory.T.exists_lift_to_complete_dvr_of_finite' A R hinj hfin V hV h
  let ψ : Fin (Module.finrank K L) → (B →+* V') := fun j => ρ.comp (σ j)
  refine ⟨V', inferInstance, inferInstance, inferInstance, inferInstance, f, ψ, hV', hf, hloc, ?_, ?_⟩
  · intro j
    show (ρ.comp (σ j)).comp φ = f.comp h
    rw [RingHom.comp_assoc, hσ j, hρ]
  have key : ∀ (m : ℕ) (g : Fin m → B) (P : MvPolynomial (Fin m) A),
      P.map (algebraMap A R) = ∏ j, ∑ i, C (σ j (g i)) * X i →
      Ideal.span (Set.range fun s => (f.comp h) (P.coeff s)) =
        ∏ j, Ideal.span (Set.range fun i => ψ j (g i)) := by
    intro m g P hPR
    rw [← GlobalTheory.T.span_coeff_prod_linear_eq_prod_span V' _ m (fun j i => ψ j (g i))]
    have hE : (∏ j, ∑ i, C (ψ j (g i)) * X i : MvPolynomial (Fin m) V') = (P.map (algebraMap A R)).map ρ := by
      rw [hPR]; simp [map_prod, map_sum, ψ]
    have hfun : (fun s => (f.comp h) (P.coeff s)) =
        fun s => (∏ j, ∑ i, C (ψ j (g i)) * X i : MvPolynomial (Fin m) V').coeff s := by
      funext s
      rw [hE, MvPolynomial.map_map, MvPolynomial.coeff_map, hρ]
    rw [hfun]
  unfold GlobalTheory.NormSheaf.normIdeal
  rw [Ideal.map_span]
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ ⟨a, ⟨m, g, hgJ, s, hs⟩, rfl⟩
    obtain ⟨P, hPK, hPR⟩ := hP m g
    have ha : a = P.coeff s := IsFractionRing.injective A K (by rw [hs, ← hPK, MvPolynomial.coeff_map])
    have hmem : (f.comp h) a ∈ Ideal.span (Set.range fun s => (f.comp h) (P.coeff s)) :=
      Ideal.subset_span ⟨s, by rw [ha]⟩
    rw [key m g P hPR] at hmem
    have hle : ∏ j, Ideal.span (Set.range fun i => ψ j (g i)) ≤ ∏ j, J.map (ψ j) :=
      Finset.prod_le_prod' (fun j _ => Ideal.span_le.2 (by
        rintro _ ⟨i, rfl⟩; exact Ideal.mem_map_of_mem _ (hgJ i)))
    exact hle hmem
  · have hfg : ∀ j, ∃ t : Finset V', (↑t : Set V') ⊆ ψ j '' (J : Set B) ∧ J.map (ψ j) = Ideal.span (↑t : Set V') := by
      intro j
      have h1 : (J.map (ψ j)).FG := IsNoetherian.noetherian _
      rw [Ideal.map] at h1 ⊢
      exact (Submodule.fg_span_iff_fg_span_finset_subset _).1 h1
    choose t ht hspan using hfg
    have hpre : ∀ (x : Σ j, (t j : Set V')), ∃ b ∈ J, ψ x.1 b = x.2 := by
      rintro ⟨j, x, hx⟩
      obtain ⟨b, hb, e⟩ := ht j hx
      exact ⟨b, hb, e⟩
    choose pre hpreJ hpreψ using hpre
    let e := Fintype.equivFin (Σ j, (t j : Set V'))
    let g : Fin (Fintype.card (Σ j, (t j : Set V'))) → B := fun i => pre (e.symm i)
    have hgJ : ∀ i, g i ∈ J := fun i => hpreJ _
    obtain ⟨P, hPK, hPR⟩ := hP _ g
    have hj : ∀ j, Ideal.span (Set.range fun i => ψ j (g i)) = J.map (ψ j) := by
      intro j
      apply le_antisymm
      · rw [Ideal.span_le]; rintro _ ⟨i, rfl⟩; exact Ideal.mem_map_of_mem _ (hgJ i)
      · rw [hspan j, Ideal.span_le]
        intro x hx
        apply Ideal.subset_span
        refine ⟨e ⟨j, x, hx⟩, ?_⟩
        simp only [g, Equiv.symm_apply_apply]
        exact hpreψ ⟨j, x, hx⟩
    calc ∏ j, J.map (ψ j) = ∏ j, Ideal.span (Set.range fun i => ψ j (g i)) := by simp_rw [hj]
      _ = Ideal.span (Set.range fun s => (f.comp h) (P.coeff s)) := (key _ g P hPR).symm
      _ ≤ _ := by
        rw [Ideal.span_le]
        rintro _ ⟨s, rfl⟩
        apply Ideal.subset_span
        exact ⟨P.coeff s, ⟨_, g, hgJ, s, by rw [← hPK, MvPolynomial.coeff_map]⟩, rfl⟩
