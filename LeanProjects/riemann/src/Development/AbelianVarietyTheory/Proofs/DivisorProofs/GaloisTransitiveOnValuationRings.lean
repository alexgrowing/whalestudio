import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemValuationSubringOfIsIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsExtraBis
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

open scoped nonZeroDivisors

namespace GlobalTheory.ProlongConj

section general

variable {Ω : Type} [Field Ω]

theorem mem_of_isIntegral {R : Type} [CommRing R] [Algebra R Ω] (A : ValuationSubring Ω)
    (hR : ∀ r : R, algebraMap R Ω r ∈ A) {b : Ω} (hb : IsIntegral R b) : b ∈ A := by
  first
  | (rename_i h_1 h_3 h_4; revert Ω h_1 R h_3 h_4 A hR b hb; exact @_root_.GlobalTheory.IntegralInValuationSubring.mem_valuationSubring_of_isIntegral)
  | exact @_root_.GlobalTheory.IntegralInValuationSubring.mem_valuationSubring_of_isIntegral
  | exact _root_.GlobalTheory.IntegralInValuationSubring.mem_valuationSubring_of_isIntegral
  | (apply _root_.GlobalTheory.IntegralInValuationSubring.mem_valuationSubring_of_isIntegral <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegralInValuationSubring.mem_valuationSubring_of_isIntegral <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegralInValuationSubring.mem_valuationSubring_of_isIntegral <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegralInValuationSubring.mem_valuationSubring_of_isIntegral ..)

variable (S : Type) [CommRing S] [IsDomain S] [IsDedekindDomain S] [Algebra S Ω] [IsFractionRing S Ω]

theorem exists_den (A : ValuationSubring Ω) (hS : ∀ s : S, algebraMap S Ω s ∈ A) {x : Ω} (hx : x ∈ A) :
    ∃ s t : S, A.valuation (algebraMap S Ω s) = 1 ∧ algebraMap S Ω s * x = algebraMap S Ω t := by
  first
  | (rename_i h_1 h_3 h_4 h_5 h_6 h_7; revert Ω h_1 S h_3 h_4 h_5 h_6 h_7 A hS x hx; exact @_root_.GlobalTheory.ClosingLemma.main)
  | exact @_root_.GlobalTheory.ClosingLemma.main
  | exact _root_.GlobalTheory.ClosingLemma.main
  | (apply _root_.GlobalTheory.ClosingLemma.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.ClosingLemma.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ClosingLemma.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ClosingLemma.main ..)

theorem le_of_valuation_lt_one_iff {A A' : ValuationSubring Ω} (hS : ∀ s : S, algebraMap S Ω s ∈ A)
    (hS' : ∀ s : S, algebraMap S Ω s ∈ A')
    (h : ∀ s : S, A.valuation (algebraMap S Ω s) < 1 ↔ A'.valuation (algebraMap S Ω s) < 1) :
    A ≤ A' := by
  intro x hx
  obtain ⟨s, t, hs1, e⟩ := exists_den S A hS hx
  have hs0 : algebraMap S Ω s ≠ 0 := by
    intro h0
    rw [h0, Valuation.map_zero] at hs1
    exact zero_ne_one hs1
  have hs1' : A'.valuation (algebraMap S Ω s) = 1 := by
    refine le_antisymm ((A'.valuation_le_one_iff _).mpr (hS' s)) ?_
    rw [← not_lt, ← h s, hs1]
    exact lt_irrefl 1
  have hxt : x = algebraMap S Ω t * (algebraMap S Ω s)⁻¹ := by rw [← e]; field_simp
  rw [← A'.valuation_le_one_iff, hxt, Valuation.map_mul, map_inv₀, hs1', inv_one, _root_.mul_one,
    A'.valuation_le_one_iff]
  exact hS' t

def primeBelow (A : ValuationSubring Ω) (hS : ∀ s : S, algebraMap S Ω s ∈ A) : Ideal S :=
  (IsLocalRing.maximalIdeal A).comap ((algebraMap S Ω).codRestrict A hS)

theorem mem_primeBelow {A : ValuationSubring Ω} (hS : ∀ s : S, algebraMap S Ω s ∈ A) (s : S) :
    s ∈ primeBelow S A hS ↔ A.valuation (algebraMap S Ω s) < 1 :=
  A.valuation_lt_one_iff _

instance isPrime_primeBelow (A : ValuationSubring Ω) (hS : ∀ s : S, algebraMap S Ω s ∈ A) :
    (primeBelow S A hS).IsPrime := by
  unfold primeBelow
  infer_instance

end general

section galois

theorem smul_valuation_lt_one_iff {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] (g : Ω ≃ₐ[K] Ω)
    (A : ValuationSubring Ω) (y : Ω) :
    (g • A).valuation y < 1 ↔ A.valuation ((g⁻¹ : Ω ≃ₐ[K] Ω) y) < 1 := by
  rw [← ValuationSubring.mem_nonunits_iff, ← ValuationSubring.mem_nonunits_iff,
    ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, map_inv₀,
    map_eq_zero_iff _ (g⁻¹ : Ω ≃ₐ[K] Ω).injective]

theorem exists_smul_eq_of_isAbove : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K] (Ω : Type) [Field Ω] [Algebra K Ω] [IsGalois K Ω]
    [FiniteDimensional K Ω] (V V' : ValuationSubring Ω), IsAbove R K V.toSubring →
    IsAbove R K V'.toSubring → ∃ g : Ω ≃ₐ[K] Ω, g • V = V' := by
  intro R K _ _ _ _ _ _ Ω _ _ _ _ V V' hV hV'
  letI : Algebra R Ω := ((algebraMap K Ω).comp (algebraMap R K)).toAlgebra
  haveI : IsScalarTower R K Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI hc : SMulCommClass (Ω ≃ₐ[K] Ω) R Ω := ⟨fun g r x => by
    rw [← IsScalarTower.algebraMap_smul K r x, ← IsScalarTower.algebraMap_smul K r (g • x)]
    exact map_smul g _ _⟩
  haveI : IsDedekindDomain (integralClosure R Ω) := integralClosure.isDedekindDomain R K Ω
  haveI : IsFractionRing (integralClosure R Ω) Ω :=
    integralClosure.isFractionRing_of_finite_extension K Ω
  haveI : Algebra.IsInvariant R (integralClosure R Ω) (Ω ≃ₐ[K] Ω) := by
    constructor
    intro b hb
    obtain ⟨k, hk⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := K) (b : Ω)).2
      fun g => congrArg Subtype.val (hb g)
    have hint : IsIntegral R k := by
      have h2 : IsIntegral R (algebraMap K Ω k) := hk ▸ b.2
      exact (isIntegral_algebraMap_iff (algebraMap K Ω).injective).1 h2
    obtain ⟨v, hv⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
    refine ⟨v, Subtype.ext ?_⟩
    rw [← hk, ← hv, ← IsScalarTower.algebraMap_apply]
    rfl
  have key : ∀ W : ValuationSubring Ω, IsAbove R K W.toSubring → ∀ k : K,
      (W.valuation (algebraMap K Ω k) < 1 ↔ k⁻¹ ∉ (algebraMap R K).range ∨ k = 0) := by
    intro W hW k
    rw [← ValuationSubring.mem_nonunits_iff, ValuationSubring.mem_nonunits_iff_or, ← map_inv₀,
      map_eq_zero_iff _ (algebraMap K Ω).injective, ← hW]
    exact or_comm
  have hR : ∀ W : ValuationSubring Ω, IsAbove R K W.toSubring → ∀ r : R, algebraMap R Ω r ∈ W := by
    intro W hW r
    have : algebraMap R K r ∈ W.toSubring.comap (algebraMap K Ω) := by rw [hW]; exact ⟨r, rfl⟩
    exact this
  have hS : ∀ W : ValuationSubring Ω, IsAbove R K W.toSubring →
      ∀ s : integralClosure R Ω, algebraMap (integralClosure R Ω) Ω s ∈ W :=
    fun W hW s => mem_of_isIntegral W (hR W hW) s.2
  have hunder : (primeBelow (integralClosure R Ω) V (hS V hV)).under R =
      (primeBelow (integralClosure R Ω) V' (hS V' hV')).under R := by
    ext r
    rw [Ideal.under_def, Ideal.mem_comap, Ideal.mem_comap, mem_primeBelow, mem_primeBelow]
    exact (key V hV (algebraMap R K r)).trans (key V' hV' (algebraMap R K r)).symm
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq (A := R) (B := integralClosure R Ω)
    (G := Ω ≃ₐ[K] Ω) _ _ hunder
  have hgS : ∀ s : integralClosure R Ω, algebraMap (integralClosure R Ω) Ω s ∈ g • V := by
    intro s
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    exact hS V hV (g⁻¹ • s)
  have hmem : ∀ s : integralClosure R Ω, (g • V).valuation (algebraMap (integralClosure R Ω) Ω s) < 1 ↔
      V'.valuation (algebraMap (integralClosure R Ω) Ω s) < 1 := by
    intro s
    rw [smul_valuation_lt_one_iff, ← mem_primeBelow (integralClosure R Ω) (hS V' hV'), hg,
      Ideal.mem_pointwise_smul_iff_inv_smul_mem, mem_primeBelow]
    rfl
  exact ⟨g, le_antisymm (le_of_valuation_lt_one_iff (integralClosure R Ω) hgS (hS V' hV') hmem)
    (le_of_valuation_lt_one_iff (integralClosure R Ω) (hS V' hV') hgS fun s => (hmem s).symm)⟩

end galois

end GlobalTheory.ProlongConj
