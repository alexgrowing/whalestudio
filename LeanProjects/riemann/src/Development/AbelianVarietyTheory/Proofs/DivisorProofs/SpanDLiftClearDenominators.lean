import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentialsSpanOfUniformizerBasis
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.span_D_lift_clear_denominators : ∀ (k K L : Type) [Field k] [CharZero k] [Field K] [Field L] [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L] (B : Subalgebra k K) [Algebra.FiniteType k B] (Q : Ideal B), Q.IsPrime → ∀ s : B, s ∈ Q → s ≠ 0 → (∀ y ∈ Q, ∃ c r : B, r ∉ Q ∧ r * y = c * s) → ∀ (m : ℕ) (y : Fin m → B), IsTranscendenceBasis k (fun j => Ideal.Quotient.mk Q (y j)) → ∀ v : B, ∃ r : B, r ∉ Q ∧ ∃ c : Fin (m + 1) → B, algebraMap K L (r : K) • D k L (algebraMap K L (v : K)) = ∑ l, algebraMap K L (c l : K) • (Fin.cons (D k L (algebraMap K L (s : K))) (fun j => D k L (algebraMap K L (y j : K))) : Fin (m + 1) → Ω[L⁄k]) l := by
  intro k K L _ _ _ _ _ _ _ _ B _ Q hQ s hsQ hs0 hgen m y hy v
  classical
  let R := Localization.AtPrime Q
  haveI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing k B
  haveI : IsNoetherianRing R := IsLocalization.isNoetherianRing Q.primeCompl R inferInstance
  have hinj : Function.Injective (algebraMap B R) :=
    IsLocalization.injective R Q.primeCompl_le_nonZeroDivisors
  have hmax : IsLocalRing.maximalIdeal R = Ideal.span {algebraMap B R s} := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      intro z hz
      obtain ⟨c, r, hr, hrc⟩ := hgen z hz
      rw [Ideal.mem_comap, Ideal.mem_span_singleton']
      refine ⟨IsLocalization.mk' R c (⟨r, hr⟩ : Q.primeCompl), ?_⟩
      have hu := IsLocalization.map_units R (⟨r, hr⟩ : Q.primeCompl)
      apply hu.mul_left_cancel
      rw [← mul_assoc, IsLocalization.mk'_spec', ← map_mul, ← map_mul]
      exact congrArg _ hrc.symm
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      exact Ideal.mem_map_of_mem _ hsQ
  have hs0' : algebraMap B R s ≠ 0 := fun h => hs0 (hinj (by rw [h, map_zero]))
  have hnf : ¬ IsField R := by
    intro hf
    have h1 := IsLocalRing.isField_iff_maximalIdeal_eq.1 hf
    rw [hmax, Ideal.span_singleton_eq_bot] at h1
    exact hs0' h1
  have hprin : Submodule.IsPrincipal (IsLocalRing.maximalIdeal R) := ⟨⟨_, hmax⟩⟩
  haveI : IsDiscreteValuationRing R := ((IsDiscreteValuationRing.TFAE R hnf).out 0 4).2 hprin
  have hirr : Irreducible (algebraMap B R s) :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).2 hmax
  haveI : IsDomain (B ⧸ Q) := Ideal.Quotient.isDomain Q
  haveI : Nontrivial (B ⧸ Q) := IsDomain.toNontrivial
  haveI : Algebra.IsAlgebraic (B ⧸ Q) Q.ResidueField :=
    IsLocalization.isAlgebraic (R := B ⧸ Q) (S := Q.ResidueField) (M := nonZeroDivisors (B ⧸ Q))
  haveI : FaithfulSMul (B ⧸ Q) Q.ResidueField :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (IsFractionRing.injective _ _)
  have htb : IsTranscendenceBasis k (fun j => IsLocalRing.residue R (algebraMap B R (y j))) := by
    have h2 := hy.algebraMap_comp (A := Q.ResidueField)
    convert h2 using 1
    funext j
    simp only [Function.comp_apply, Ideal.algebraMap_quotient_residueField_mk]
    rfl
  have hspan := GlobalTheory.span_D_uniformizer_transcendenceBasis k R (algebraMap B R s) hirr m
    (fun j => algebraMap B R (y j)) htb
  have hunit : ∀ z : Q.primeCompl, IsUnit (algebraMap B K z) := fun z => by
    refine isUnit_iff_ne_zero.2 fun h => z.2 ?_
    have hz : (z : B) = 0 := Subtype.ext h
    rw [hz]; exact Q.zero_mem
  let ψ : R →+* K := IsLocalization.lift hunit
  letI : Algebra R L := ((algebraMap K L).comp ψ).toAlgebra
  have hRL : ∀ x : B, algebraMap R L (algebraMap B R x) = algebraMap K L (x : K) := fun x => by
    rw [RingHom.algebraMap_toAlgebra, RingHom.comp_apply, IsLocalization.lift_eq]
    rfl
  haveI : IsScalarTower k R L := IsScalarTower.of_algebraMap_eq fun a => by
    rw [IsScalarTower.algebraMap_apply k B R, hRL, IsScalarTower.algebraMap_apply k K L]
    rfl
  haveI : SMulCommClass k R L := inferInstance
  let Φ := KaehlerDifferential.map k k R L
  let g : Fin (m + 1) → Ω[R⁄k] := Fin.cons (D k R (algebraMap B R s)) (fun j => D k R (algebraMap B R (y j)))
  have hDv : D k R (algebraMap B R v) ∈ Submodule.span R (Set.range g) := by
    rw [Fin.range_cons, hspan]; exact Submodule.mem_top
  obtain ⟨c', hc'⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 hDv
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples Q.primeCompl (Finset.univ : Finset (Fin (m + 1))) c'
  have hb' : ∀ l, ∃ x : B, algebraMap B R x = algebraMap B R (b : B) * c' l := fun l => by
    obtain ⟨x, hx⟩ := hb l (Finset.mem_univ l)
    exact ⟨x, by rw [hx, Algebra.smul_def]⟩
  choose c hc using hb'
  have hΦD : ∀ x : B, Φ (D k R (algebraMap B R x)) = D k L (algebraMap K L (x : K)) := fun x => by
    rw [KaehlerDifferential.map_D, hRL]
  have hΦg : ∀ l, Φ (g l) = (Fin.cons (D k L (algebraMap K L (s : K))) (fun j => D k L (algebraMap K L (y j : K))) : Fin (m + 1) → Ω[L⁄k]) l := by
    intro l
    refine Fin.cases ?_ (fun j => ?_) l
    · simp only [g, Fin.cons_zero]; exact hΦD s
    · simp only [g, Fin.cons_succ]; exact hΦD (y j)
  refine ⟨b, b.2, c, ?_⟩
  rw [← hRL, ← hΦD, algebraMap_smul, ← map_smul, ← hc', Finset.smul_sum, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← hRL, ← hΦg, algebraMap_smul L (algebraMap B R (c l)) (Φ (g l)), ← map_smul Φ]
  congr 1
  rw [hc, mul_smul]
