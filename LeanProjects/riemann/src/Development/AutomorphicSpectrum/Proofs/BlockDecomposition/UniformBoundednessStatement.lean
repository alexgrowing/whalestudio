import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JpUnif

noncomputable section

open Matrix MeasureTheory

namespace GlobalTheory.CompanionTheory.Jp.Unif

theorem integral_coset {X G : Type*} [Group X] [MeasurableSpace X] [MeasurableMul X] (ν : Measure X)
    [IsProbabilityMeasure ν] [ν.IsMulLeftInvariant] [Group G] (N : Subgroup G) [Finite (G ⧸ N)] (ρ : X →* G)
    (hρ : Function.Surjective ρ) (hN : MeasurableSet (ρ ⁻¹' (N : Set G))) (c : G ⧸ N → ℂ) :
    ∫ x, c (QuotientGroup.mk (ρ x)) ∂ν = (ν.real (ρ ⁻¹' (N : Set G)) : ℂ) * ∑ᶠ u, c u := by
  classical
  letI := Fintype.ofFinite (G ⧸ N)
  have hS : ∀ u : G ⧸ N, ∃ y : X, {x | (QuotientGroup.mk (ρ x) : G ⧸ N) = u} =
      (fun x => y * x) ⁻¹' (ρ ⁻¹' (N : Set G)) := by
    intro u
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective u
    obtain ⟨y, hy⟩ := hρ g⁻¹
    refine ⟨y, ?_⟩
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe, map_mul, hy]
    rw [eq_comm, QuotientGroup.eq]
  choose y hy using hS
  have hmeas : ∀ u : G ⧸ N, MeasurableSet {x | (QuotientGroup.mk (ρ x) : G ⧸ N) = u} := by
    intro u
    rw [hy u]
    exact hN.preimage (measurable_const_mul (y u))
  have hmeasure : ∀ u : G ⧸ N,
      ν.real {x | (QuotientGroup.mk (ρ x) : G ⧸ N) = u} = ν.real (ρ ⁻¹' (N : Set G)) := by
    intro u
    rw [hy u]
    show (ν _).toReal = (ν _).toReal
    rw [measure_preimage_mul]
  have hdecomp : (fun x => c (QuotientGroup.mk (ρ x))) = fun x =>
      ∑ u, Set.indicator {x | (QuotientGroup.mk (ρ x) : G ⧸ N) = u} (fun _ => c u) x := by
    funext x
    rw [Finset.sum_eq_single (QuotientGroup.mk (ρ x) : G ⧸ N)]
    · exact (Set.indicator_of_mem (show x ∈ {x' : X | (QuotientGroup.mk (ρ x') : G ⧸ N) =
        QuotientGroup.mk (ρ x)} from rfl) (fun _ => c (QuotientGroup.mk (ρ x)))).symm
    · intro u _ hu
      exact Set.indicator_of_notMem (by intro h; exact hu (Eq.symm h)) _
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [finsum_eq_sum_of_fintype, hdecomp, integral_finset_sum]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    rw [integral_indicator_const _ (hmeas u), hmeasure u, Complex.real_smul]
  · intro u _
    exact (integrable_const (c u)).indicator (hmeas u)

theorem integral_level {X G : Type*} [Group X] [MeasurableSpace X] [MeasurableMul X] (ν : Measure X)
    [IsProbabilityMeasure ν] [ν.IsMulLeftInvariant] [Group G] (N : Subgroup G) [Finite (G ⧸ N)] (ρ : X →* G)
    (hρ : Function.Surjective ρ) (hN : MeasurableSet (ρ ⁻¹' (N : Set G))) (φ : G → ℂ)
    (hφ : ∀ κ, ∀ γ ∈ N, φ (κ * γ) = φ κ) :
    ∫ x, φ (ρ x) ∂ν = (Nat.card (G ⧸ N) : ℂ)⁻¹ * ∑ᶠ u : G ⧸ N, φ (Quotient.out u) := by
  classical
  letI := Fintype.ofFinite (G ⧸ N)
  have hone : ∫ _x, (1 : ℂ) ∂ν = 1 := by simp
  have hsum : ∑ᶠ _u : G ⧸ N, (1 : ℂ) = (Nat.card (G ⧸ N) : ℂ) := by
    rw [finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card,
      nsmul_eq_mul, mul_one]
  have h1 : ∫ _x, (1 : ℂ) ∂ν = (ν.real (ρ ⁻¹' (N : Set G)) : ℂ) * ∑ᶠ _u : G ⧸ N, (1 : ℂ) :=
    GlobalTheory.CompanionTheory.Jp.Unif.integral_coset ν N ρ hρ hN (fun _ => 1)
  rw [hone, hsum] at h1
  have hA : (ν.real (ρ ⁻¹' (N : Set G)) : ℂ) = (Nat.card (G ⧸ N) : ℂ)⁻¹ :=
    eq_inv_of_mul_eq_one_left h1.symm
  calc ∫ x, φ (ρ x) ∂ν = ∫ x, φ (Quotient.out (QuotientGroup.mk (ρ x) : G ⧸ N)) ∂ν := by
        congr 1
        funext x
        obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul N (ρ x)
        rw [hh, hφ _ _ h.2]
    _ = (ν.real (ρ ⁻¹' (N : Set G)) : ℂ) * ∑ᶠ u : G ⧸ N, φ (Quotient.out u) :=
        GlobalTheory.CompanionTheory.Jp.Unif.integral_coset ν N ρ hρ hN (fun u => φ (Quotient.out u))
    _ = (Nat.card (G ⧸ N) : ℂ)⁻¹ * ∑ᶠ u : G ⧸ N, φ (Quotient.out u) := by rw [hA]

theorem finite_quot_sq {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Fintype (IsLocalRing.ResidueField O)] {ϖ : O} (hϖ : Irreducible ϖ) : Finite (O ⧸ Ideal.span {ϖ ^ 2}) := by
  have hm : IsLocalRing.maximalIdeal O = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  have : Finite (O ⧸ IsLocalRing.maximalIdeal O) := Finite.of_fintype (IsLocalRing.ResidueField O)
  rw [← Ideal.span_singleton_pow, ← hm]
  exact Ideal.finite_quotient_pow (IsNoetherian.noetherian _) 2

theorem finite_quotient_level_square_congruence {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Fintype (IsLocalRing.ResidueField O)] (n : ℕ) {ϖ : O} (hϖ : Irreducible ϖ) :
    Finite (GL (Ix n) O ⧸ Gam2 (n := n) ϖ) := by
  haveI := GlobalTheory.CompanionTheory.Jp.Unif.finite_quot_sq hϖ
  haveI : Finite (Matrix (GlobalTheory.CompanionTheory.Jp.Ix n) (GlobalTheory.CompanionTheory.Jp.Ix n) (O ⧸ Ideal.span {ϖ ^ 2})) :=
    inferInstanceAs (Finite (GlobalTheory.CompanionTheory.Jp.Ix n → GlobalTheory.CompanionTheory.Jp.Ix n → O ⧸ Ideal.span {ϖ ^ 2}))
  haveI : Finite (GL (GlobalTheory.CompanionTheory.Jp.Ix n) (O ⧸ Ideal.span {ϖ ^ 2})) :=
    Finite.of_injective (fun g : GL (GlobalTheory.CompanionTheory.Jp.Ix n) (O ⧸ Ideal.span {ϖ ^ 2}) =>
      (g : Matrix (GlobalTheory.CompanionTheory.Jp.Ix n) (GlobalTheory.CompanionTheory.Jp.Ix n) (O ⧸ Ideal.span {ϖ ^ 2})))
      (fun _ _ h => Units.ext h)
  exact Finite.of_injective _ (QuotientGroup.kerLift_injective
    (Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk (Ideal.span {ϖ ^ 2})) :
      GL (GlobalTheory.CompanionTheory.Jp.Ix n) O →* GL (GlobalTheory.CompanionTheory.Jp.Ix n) (O ⧸ Ideal.span {ϖ ^ 2})))

theorem jpUnif : JpUnif := by
  intro O _ _ _ _ n ϖ hϖ X _ _ _ ν _ _ ρ hρ hN φ hφ
  haveI := finite_quotient_level_square_congruence n hϖ
  exact integral_level ν (Gam2 (n := n) ϖ) ρ hρ hN φ hφ

end GlobalTheory.CompanionTheory.Jp.Unif

end
