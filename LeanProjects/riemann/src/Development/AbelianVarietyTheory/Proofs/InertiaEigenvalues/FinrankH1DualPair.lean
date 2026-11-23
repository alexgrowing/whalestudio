import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMutuallyDualStableLatticesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H1LatticeIndexGrowthStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GrowthGaloisInvariantsModPrimePowerLatticeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H1ReductionIndexBoundDualStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H1LatticeRankGrowthStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteH1PeriodDatumStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoefficientRingIntegersCompactAdicPropertiesStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.EulerCharH1

theorem le_of_pow_le {q a b C : ℕ} (hq : 2 ≤ q) (h : ∀ r : ℕ, q ^ (r * a) ≤ C * q ^ (r * b)) :
    a ≤ b := by
  by_contra hab
  push_neg at hab
  have key : ∀ r : ℕ, q ^ r ≤ C := by
    intro r
    have h1 := h r
    have hpos : 0 < q ^ (r * b) := pow_pos (by omega) _
    have : q ^ (r * a) ≥ q ^ (r * b) * q ^ r := by
      rw [← pow_add]
      apply Nat.pow_le_pow_right (by omega)
      nlinarith
    have : q ^ (r * b) * q ^ r ≤ C * q ^ (r * b) := le_trans this h1
    rw [mul_comm (q ^ (r * b))] at this
    exact Nat.le_of_mul_le_mul_right this hpos
  have h2 := key C
  have h3 : C < 2 ^ C := Nat.lt_two_pow_self
  have h4 : 2 ^ C ≤ q ^ C := Nat.pow_le_pow_left hq C
  omega

theorem stableSub_span_smul {G LL O V : Type} [Group G] [Field LL] [CommRing O] [Algebra O LL]
    [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
    {ρ : Representation LL G V} (L : Lattice (O := O) ρ) (c : O) :
    StableSub L (Ideal.span {c} • ⊤ : Submodule O ↥L.T) := by
  intro g x hx
  rw [Submodule.ideal_span_singleton_smul] at hx ⊢
  obtain ⟨y, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hx
  exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr ⟨actT L g y, Submodule.mem_top, (map_smul _ _ _).symm⟩

end GlobalTheory.EulerCharH1

namespace GlobalTheory.EulerCharH1

theorem natCast_not_isUnit (l : ℕ) [Fact l.Prime] (LL : Type) [Field LL] [Algebra ℚ_[l] LL]
    (O : Type) [CommRing O] [Algebra O LL]
    (hint : ∀ x : LL, x ∈ Set.range (algebraMap O LL) ↔
      RingHom.IsIntegralElem ((algebraMap ℚ_[l] LL).comp (algebraMap ℤ_[l] ℚ_[l])) x) :
    ¬ IsUnit ((l : ℕ) : O) := by
  rintro ⟨u, hu⟩
  have hl0 : ((l : ℕ) : ℚ_[l]) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hy : algebraMap O LL ((u⁻¹ : Oˣ) : O) = algebraMap ℚ_[l] LL (((l : ℕ) : ℚ_[l])⁻¹) := by
    rw [map_inv₀, map_natCast]
    have h1 : algebraMap O LL ((u⁻¹ : Oˣ) : O) * algebraMap O LL (u : O) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    rw [hu, map_natCast] at h1
    exact eq_inv_of_mul_eq_one_left h1
  obtain ⟨p, hpm, hp⟩ := (hint _).mp ⟨_, hy⟩
  rw [← Polynomial.hom_eval₂] at hp
  have hp' : p.eval₂ (algebraMap ℤ_[l] ℚ_[l]) (((l : ℕ) : ℚ_[l])⁻¹) = 0 :=
    (algebraMap ℚ_[l] LL).injective (by rw [hp, map_zero])
  have hI : IsIntegral ℤ_[l] (((l : ℕ) : ℚ_[l])⁻¹) := ⟨p, hpm, hp'⟩
  obtain ⟨w, hw⟩ := IsIntegrallyClosed.isIntegral_iff.mp hI
  have hlw : ((l : ℕ) : ℤ_[l]) * w = 1 := by
    apply IsFractionRing.injective ℤ_[l] ℚ_[l]
    rw [map_mul, hw, map_natCast, map_one, mul_inv_cancel₀ hl0]
  exact PadicInt.p_nonunit (IsUnit.of_mul_eq_one _ hlw)

end GlobalTheory.EulerCharH1

namespace GlobalTheory.EulerCharH1

theorem two_le_card (l : ℕ) [Fact l.Prime] (LL : Type) [Field LL] [Algebra ℚ_[l] LL]
    [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL]
    (hO : GoodO (Qp := ℚ_[l]) LL O) : 2 ≤ Nat.card (O ⧸ Ideal.span {((l : ℕ) : O)}) := by
  obtain ⟨hint, -, hfin, -⟩ := GlobalTheory.T.coefficient_ring_integers_compact_adic_properties l LL O hO
  have hf : Finite (O ⧸ Ideal.span {((l : ℕ) : O)}) := by
    simpa using hfin 1
  have : Nontrivial (O ⧸ Ideal.span {((l : ℕ) : O)}) :=
    Ideal.Quotient.nontrivial_iff.mpr (by
      rw [Ne, Ideal.span_singleton_eq_top]; exact natCast_not_isUnit l LL O hint)
  exact Finite.one_lt_card

theorem eq_of_bounds {q a h0 h0' d C1 C2 C3 C4 : ℕ} (X Y H H' : ℕ → ℕ) (hq : 2 ≤ q)
    (hX : ∀ r, q ^ (r * a) ≤ X r ∧ X r ≤ C1 * q ^ (r * a))
    (hY : ∀ r, X r ≤ Y r ∧ Y r ≤ C2 * X r)
    (hE : ∀ r, Y r = H r * H' r * q ^ (r * d))
    (hH : ∀ r, q ^ (r * h0) ≤ H r ∧ H r ≤ C3 * q ^ (r * h0))
    (hH' : ∀ r, q ^ (r * h0') ≤ H' r ∧ H' r ≤ C4 * q ^ (r * h0')) :
    a = h0 + h0' + d := by
  have key : ∀ r : ℕ, q ^ (r * a) ≤ C3 * C4 * q ^ (r * (h0 + h0' + d)) ∧
      q ^ (r * (h0 + h0' + d)) ≤ C2 * C1 * q ^ (r * a) := by
    intro r
    obtain ⟨hX1, hX2⟩ := hX r
    obtain ⟨hY1, hY2⟩ := hY r
    obtain ⟨hH1, hH2⟩ := hH r
    obtain ⟨hH1', hH2'⟩ := hH' r
    have hpow : q ^ (r * (h0 + h0' + d)) = q ^ (r * h0) * q ^ (r * h0') * q ^ (r * d) := by
      rw [← pow_add, ← pow_add]; ring_nf
    constructor
    · calc q ^ (r * a) ≤ X r := hX1
        _ ≤ Y r := hY1
        _ = H r * H' r * q ^ (r * d) := hE r
        _ ≤ (C3 * q ^ (r * h0)) * (C4 * q ^ (r * h0')) * q ^ (r * d) := by
          gcongr
        _ = C3 * C4 * q ^ (r * (h0 + h0' + d)) := by rw [hpow]; ring
    · calc q ^ (r * (h0 + h0' + d)) = q ^ (r * h0) * q ^ (r * h0') * q ^ (r * d) := hpow
        _ ≤ H r * H' r * q ^ (r * d) := by gcongr
        _ = Y r := (hE r).symm
        _ ≤ C2 * X r := hY2
        _ ≤ C2 * (C1 * q ^ (r * a)) := by gcongr
        _ = C2 * C1 * q ^ (r * a) := by ring
  have h1 := le_of_pow_le hq (fun r => (key r).1)
  have h2 := le_of_pow_le hq (fun r => (key r).2)
  omega

theorem finite_and_finrank_H1V : Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK →
    ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l), ∀ (K : FinExt l) (LL : Type) [Field LL]
    [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL],
    GoodO (Qp := ℚ_[l]) LL O → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O)
    (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDual1 (P.PD K) A.ρ A'.ρ m →
    Module.Finite LL (H1V A.ρ) ∧ finrank LL (H1V A.ρ) = finrank LL ↥(H0V A.ρ) +
      finrank LL ↥(H0V A'.ρ) + finrank ℚ_[l] ↥K.1 * finrank LL A.V := by
  intro hTD hEC l _ P K LL _ _ _ O _ _ hO A A' m hm
  obtain ⟨LA, LA', hLL, -⟩ := GlobalTheory.T.exists_mutuallyDual_stable_lattices l P K LL O hO A A' m hm
  have hfinT : Module.Finite O (LatticeCohomology LA) := GlobalTheory.T.finite_H1_period_datum hTD l P K LL O hO A LA
  obtain ⟨hfinV, C1, -, hX⟩ := GlobalTheory.T.H1_lattice_rank_growth_of_goodO l K LL O hO A LA hfinT
  obtain ⟨C2, -, hY⟩ := GlobalTheory.T.H1_reduction_index_bound_of_tateDuality hTD l P K LL O hO A A' LA LA' m hLL
  obtain ⟨C3, -, hH⟩ := GlobalTheory.T.growth_galois_invariants_mod_prime_power_lattice l K LL O hO A LA
  obtain ⟨C4, -, hH'⟩ := GlobalTheory.T.growth_galois_invariants_mod_prime_power_lattice l K LL O hO A' LA'
  exact ⟨hfinV, eq_of_bounds _ _ _ _ (two_le_card l LL O hO) hX
    (fun r => hY r (stableSub_span_smul LA _))
    (fun r => GlobalTheory.T.H1_lattice_index_growth_of_tateDuality_eulerChar hTD hEC l P K LL O hO A A' LA LA' m hLL r
      (stableSub_span_smul LA _) (stableSub_span_smul LA' _))
    (fun r => hH r (stableSub_span_smul LA _)) (fun r => hH' r (stableSub_span_smul LA' _))⟩

end GlobalTheory.EulerCharH1
