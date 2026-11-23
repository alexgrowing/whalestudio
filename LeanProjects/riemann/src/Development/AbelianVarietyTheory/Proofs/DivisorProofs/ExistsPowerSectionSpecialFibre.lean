import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SpecialFibreUnits
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BijectiveAlgebraMapIntegralClosureOfBirational

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits GlobalTheory.Cartier

namespace GlobalTheory.ExpChoice

variable {X : Scheme.{0}} [IsIntegral X]

theorem unitAt_zpow {z : X} {u : X.functionField} (h : UnitAt z u) (n : ℤ) : UnitAt z (u ^ n) := by
  have hp : ∀ k : ℕ, UnitAt z (u ^ k) := fun k => by
    induction k with
    | zero => simpa using unitAt_one z
    | succ k ih => rw [pow_succ]; exact ih.mul h
  rcases n with k | k
  · simpa using hp k
  · rw [zpow_negSucc]; exact (hp (k+1)).inv

section DVR

variable {z : X} [IsDiscreteValuationRing (X.presheaf.stalk z)]

theorem exists_unit_mul_zpow {ϖ : X.presheaf.stalk z} (hϖ : Irreducible ϖ) {f : X.functionField}
    (hf : f ≠ 0) : ∃ (k : ℤ) (u : X.functionField), UnitAt z u ∧
      f = u * algebraMap _ X.functionField ϖ ^ k := by
  have hinj := IsFractionRing.injective (X.presheaf.stalk z) X.functionField
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := X.presheaf.stalk z) f
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha0 : a ≠ 0 := by rintro rfl; simp at hf
  obtain ⟨na, ua, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hϖ
  obtain ⟨nb, ub, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖ
  have hp : algebraMap _ X.functionField ϖ ≠ 0 := (map_ne_zero_iff _ hinj).2 hϖ.ne_zero
  have hub : algebraMap _ X.functionField (ub : X.presheaf.stalk z) ≠ 0 :=
    (map_ne_zero_iff _ hinj).2 ub.ne_zero
  refine ⟨(na : ℤ) - nb, algebraMap _ X.functionField (ua : X.presheaf.stalk z) /
    algebraMap _ X.functionField (ub : X.presheaf.stalk z), ?_, ?_⟩
  · rw [div_eq_mul_inv]
    exact UnitAt.mul ⟨_, ua.isUnit, rfl⟩ (UnitAt.inv ⟨_, ub.isUnit, rfl⟩)
  · rw [zpow_sub₀ hp, zpow_natCast, zpow_natCast, map_mul, map_mul, map_pow, map_pow]
    field_simp

theorem regAt_unit_mul_zpow_iff {ϖ : X.presheaf.stalk z} (hϖ : Irreducible ϖ) {u : X.functionField}
    (hu : UnitAt z u) (k : ℤ) :
    RegAt z (u * algebraMap _ X.functionField ϖ ^ k) ↔ 0 ≤ k := by
  have hinj := IsFractionRing.injective (X.presheaf.stalk z) X.functionField
  have hp : algebraMap _ X.functionField ϖ ≠ 0 := (map_ne_zero_iff _ hinj).2 hϖ.ne_zero
  constructor
  · rintro ⟨a, ha⟩
    by_contra hk
    push_neg at hk
    obtain ⟨b, -, hbu⟩ := hu.inv
    obtain ⟨j, hj⟩ : ∃ j : ℕ, (j : ℤ) = -k - 1 := ⟨(-k - 1).toNat, Int.toNat_of_nonneg (by omega)⟩
    have e : algebraMap _ X.functionField (ϖ * (b * a * ϖ ^ j)) = 1 := by
      rw [map_mul, map_mul, map_mul, map_pow, hbu, ha, ← zpow_natCast, hj]
      have hu0 := hu.ne_zero
      calc algebraMap _ X.functionField ϖ * (u⁻¹ * (u * algebraMap _ X.functionField ϖ ^ k) *
            algebraMap _ X.functionField ϖ ^ (-k - 1))
          = algebraMap _ X.functionField ϖ ^ (1 + k + (-k - 1)) := by
            rw [zpow_add₀ hp, zpow_add₀ hp, zpow_one]
            field_simp
        _ = 1 := by rw [show 1 + k + (-k - 1) = 0 by ring, zpow_zero]
    rw [← map_one (algebraMap (X.presheaf.stalk z) X.functionField)] at e
    exact hϖ.not_isUnit (IsUnit.of_mul_eq_one _ (hinj e))
  · intro hk
    refine hu.regAt.mul ⟨ϖ ^ k.toNat, ?_⟩
    rw [map_pow, ← zpow_natCast, Int.toNat_of_nonneg hk]

end DVR

theorem finite_dvr_notMem [IsLocallyNoetherian X] [CompactSpace X] (π : Γ(X, ⊤))
    (hπ : genericPoint X ∈ X.basicOpen π) :
    {z : X | z ∉ X.basicOpen π ∧ IsDiscreteValuationRing (X.presheaf.stalk z)}.Finite := by
  have hπ0 : fnOf ⊤ trivial π ≠ 0 :=
    ((unitAt_fnOf_iff (show genericPoint X ∈ (⊤ : X.Opens) from trivial) trivial π).2 hπ).ne_zero
  have hcov : (Set.univ : Set X) ⊆ ⋃ U : X.affineOpens, ((U : X.Opens) : Set X) := fun x _ => by
    obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
    exact Set.mem_iUnion.2 ⟨⟨U, hU⟩, hx⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun U : X.affineOpens => ((U : X.Opens) : Set X)) (fun U => (U : X.Opens).isOpen) hcov
  have fin : ∀ U : X.affineOpens,
      ({z : X | z ∉ X.basicOpen π ∧ IsDiscreteValuationRing (X.presheaf.stalk z)} ∩
        ((U : X.Opens) : Set X)).Finite := by
    rintro ⟨U, hU⟩
    by_cases hne : Nonempty U
    swap
    · refine Set.finite_empty.subset fun z hz => hne ⟨⟨z, hz.2⟩⟩
    have hg : genericPoint X ∈ U := by
      obtain ⟨⟨x, hx⟩⟩ := hne
      exact gen_mem hx
    haveI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    let a : Γ(X, U) := ReciprocityTheory.ChartRestriction.G.Geo.Tor.resG X (le_top : U ≤ ⊤) π
    have ha : a ≠ 0 := by
      intro h0
      apply hπ0
      rw [← fnOf_resG (le_top : U ≤ ⊤) hg π]
      exact (congrArg (fnOf U hg) h0).trans (map_zero _)
    have hba : X.basicOpen a = U ⊓ X.basicOpen π := X.basicOpen_res π (homOfLE (le_top : U ≤ ⊤)).op
    refine ((GlobalTheory.finite_height_eq_one_mem ha).image hU.fromSpec).subset ?_
    rintro z ⟨⟨hzπ, hdvr⟩, hzU⟩
    refine ⟨hU.primeIdealOf ⟨z, hzU⟩, ⟨?_, ?_⟩, hU.fromSpec_primeIdealOf ⟨z, hzU⟩⟩
    · let y : U := ⟨z, hzU⟩
      haveI : IsDiscreteValuationRing (X.presheaf.stalk (y : X)) := hdvr
      letI : Algebra Γ(X, U) (X.presheaf.stalk (y : X)) := X.presheaf.algebra_section_stalk y
      haveI := hU.isLocalization_stalk y
      have e := IsLocalization.AtPrime.ringKrullDim_eq_height (hU.primeIdealOf y).asIdeal
        (X.presheaf.stalk (y : X))
      rw [IsDiscreteValuationRing.ringKrullDim_eq_one] at e
      exact_mod_cast e.symm
    · have hz' : hU.fromSpec (hU.primeIdealOf ⟨z, hzU⟩) ∉ X.basicOpen a := by
        rw [hU.fromSpec_primeIdealOf ⟨z, hzU⟩, hba]
        exact fun h => hzπ h.2
      have := mt (fun h => (hU.fromSpec_preimage_basicOpen a).ge h) hz'
      by_contra h
      exact this ((PrimeSpectrum.mem_basicOpen _ _).2 h)
  refine (t.finite_toSet.biUnion fun U _ => fin U).subset fun z hz => ?_
  obtain ⟨U, hU, hzU⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ z))
  exact Set.mem_biUnion hU ⟨hz, hzU⟩

theorem exists_dvr_notMem [IsLocallyNoetherian X]
    (hN : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) (π : Γ(X, ⊤))
    (hπ : genericPoint X ∈ X.basicOpen π) {z₀ : X} (hz₀ : z₀ ∉ X.basicOpen π) :
    ∃ z : X, z ∉ X.basicOpen π ∧ IsDiscreteValuationRing (X.presheaf.stalk z) := by
  have hπ0 : fnOf ⊤ trivial π ≠ 0 :=
    ((unitAt_fnOf_iff (show genericPoint X ∈ (⊤ : X.Opens) from trivial) trivial π).2 hπ).ne_zero
  obtain ⟨U, hU, hz₀U, -⟩ := exists_isAffineOpen_mem_and_subset (x := z₀) (U := ⊤) trivial
  haveI : Nonempty U := ⟨⟨z₀, hz₀U⟩⟩
  have hg : genericPoint X ∈ U := gen_mem hz₀U
  haveI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  haveI : IsIntegrallyClosed Γ(X, U) := GlobalTheory.isIntegrallyClosed_sections_of_stalks hN hU
  let a : Γ(X, U) := ReciprocityTheory.ChartRestriction.G.Geo.Tor.resG X (le_top : U ≤ ⊤) π
  have ha : a ≠ 0 := by
    intro h0
    apply hπ0
    rw [← fnOf_resG (le_top : U ≤ ⊤) hg π]
    exact (congrArg (fnOf U hg) h0).trans (map_zero _)
  have hba : X.basicOpen a = U ⊓ X.basicOpen π := X.basicOpen_res π (homOfLE (le_top : U ≤ ⊤)).op
  have haq : a ∈ (hU.primeIdealOf ⟨z₀, hz₀U⟩).asIdeal := by
    have hz' : hU.fromSpec (hU.primeIdealOf ⟨z₀, hz₀U⟩) ∉ X.basicOpen a := by
      rw [hU.fromSpec_primeIdealOf ⟨z₀, hz₀U⟩, hba]
      exact fun h => hz₀ h.2
    have := mt (fun h => (hU.fromSpec_preimage_basicOpen a).ge h) hz'
    by_contra h
    exact this ((PrimeSpectrum.mem_basicOpen _ _).2 h)
  obtain ⟨p, hp, -⟩ := Ideal.exists_minimalPrimes_le ((Ideal.span_singleton_le_iff_mem _).2 haq)
  haveI : p.IsPrime := hp.1.1
  have hap : a ∈ p := (Ideal.span_singleton_le_iff_mem _).1 hp.1.2
  have h1 : p.height = 1 := by
    refine le_antisymm (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ p hp) ?_
    rw [ENat.one_le_iff_ne_zero, Ne, Ideal.height_eq_zero_iff_eq_bot]
    rintro rfl
    exact ha hap
  let P : PrimeSpectrum Γ(X, U) := ⟨p, inferInstance⟩
  have hz : hU.fromSpec P ∈ U := hU.range_fromSpec.le ⟨P, rfl⟩
  letI : Algebra Γ(X, U) (X.presheaf.stalk (hU.fromSpec P)) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨_, hz⟩
  haveI : IsLocalization.AtPrime (X.presheaf.stalk (hU.fromSpec P)) p := hU.isLocalization_stalk' P hz
  refine ⟨hU.fromSpec P, fun h => ?_, GlobalTheory.isDiscreteValuationRing_of_height_eq_one p h1 _⟩
  have h2 : hU.fromSpec P ∈ X.basicOpen a := by rw [hba]; exact ⟨hz, h⟩
  have h3 := (hU.fromSpec_preimage_basicOpen a).le h2
  exact (PrimeSpectrum.mem_basicOpen _ _).1 h3 hap

theorem zpow_exponent_identity {K : Type} [Field K] {p : K} (hp : p ≠ 0) (u v : K) (m t n : ℤ) (M : ℕ) :
    (u * p ^ m) ^ n * ((v * p ^ t) ^ M)⁻¹ = (u ^ n * (v ^ (M : ℤ))⁻¹) * p ^ (m * n - t * M) := by
  rw [← zpow_natCast (v * p ^ t), zpow_sub₀ hp, mul_zpow, mul_zpow, ← zpow_mul, ← zpow_mul,
    mul_inv, mul_comm t]
  ring

open ReciprocityTheory.ChartRestriction.G.Geo.Tor in

theorem point_data {z : X} [IsDiscreteValuationRing (X.presheaf.stalk z)] (π : Γ(X, ⊤))
    (hπ0 : fnOf ⊤ trivial π ≠ 0) (hz : z ∉ X.basicOpen π) (L : LB X) (τ : L.ι → X.functionFieldˣ) (hL : L.IsLB)
    (hr : IsRatSec L τ) :
    ∃ (p : X.functionField) (m t : ℤ), p ≠ 0 ∧ 1 ≤ m ∧
      (∀ u, UnitAt z u → ∀ k : ℤ, RegAt z (u * p ^ k) ↔ 0 ≤ k) ∧
      (∃ u, UnitAt z u ∧ fnOf ⊤ trivial π = u * p ^ m) ∧
      ∀ i, z ∈ L.U i → ∃ v, UnitAt z v ∧ (τ i : X.functionField) = v * p ^ t := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (X.presheaf.stalk z)
  have hp : algebraMap _ X.functionField ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (X.presheaf.stalk z) X.functionField)).2 hϖ.ne_zero
  have hzt : z ∈ (⊤ : X.Opens) := trivial
  obtain ⟨m, u, hu, hm⟩ := exists_unit_mul_zpow hϖ hπ0
  obtain ⟨j, hj⟩ := exists_chart hL z
  obtain ⟨t, w, hw, ht⟩ := exists_unit_mul_zpow hϖ (τ j).ne_zero
  refine ⟨_, m, t, hp, ?_, fun u hu k => regAt_unit_mul_zpow_iff hϖ hu k, ⟨u, hu, hm⟩, ?_⟩
  · have h0 : 0 ≤ m := (regAt_unit_mul_zpow_iff hϖ hu m).1 (hm ▸ regAt_fnOf hzt trivial π)
    have h1 : m ≠ 0 := by
      rintro rfl
      rw [zpow_zero, mul_one] at hm
      exact hz ((unitAt_fnOf_iff hzt trivial π).1 (hm ▸ hu))
    omega
  · intro i hi
    have hij : z ∈ L.U i ⊓ L.U j := ⟨hi, hj⟩
    refine ⟨fnOf _ (gen_mem hij) (L.g i j : Γ(X, L.U i ⊓ L.U j)) * w,
      (unitAt_fnOf hij _ _).mul hw, ?_⟩
    rw [hr i j (gen_mem hij), ht, mul_assoc]

end GlobalTheory.ExpChoice

open GlobalTheory.ExpChoice in

theorem GlobalTheory.ExpChoice.exists_exponents : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X],
  (∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) →
  ∀ (π : Γ(X, ⊤)), genericPoint X ∈ X.basicOpen π → (∃ z : X, z ∉ X.basicOpen π) →
  ∀ (L : LB X) (τ : L.ι → X.functionFieldˣ), L.IsLB → IsRatSec L τ →
    (∀ (i : L.ι) (z : X), z ∈ L.U i → z ∈ X.basicOpen π → UnitAt z (τ i : X.functionField)) →
    ∃ (M : ℕ) (n : ℤ) (x₀ : X), 1 ≤ M ∧ x₀ ∉ X.basicOpen π ∧
      (∀ (i : L.ι) (z : X), z ∈ L.U i → IsDiscreteValuationRing (X.presheaf.stalk z) →
        RegAt z (fnOf ⊤ trivial π ^ n * ((τ i : X.functionField) ^ M)⁻¹)) ∧
      (∀ i : L.ι, x₀ ∈ L.U i → UnitAt x₀ (fnOf ⊤ trivial π ^ n * ((τ i : X.functionField) ^ M)⁻¹)) := by
  intro X _ _ _ hN π hπ ⟨z₀, hz₀⟩ L τ hL hr hτ
  have hπ0 : fnOf ⊤ trivial π ≠ 0 :=
    ((unitAt_fnOf_iff (show genericPoint X ∈ (⊤ : X.Opens) from trivial) trivial π).2 hπ).ne_zero
  set S : Set X := {z | z ∉ X.basicOpen π ∧ IsDiscreteValuationRing (X.presheaf.stalk z)} with hSdef
  have hS : S.Finite := finite_dvr_notMem π hπ
  have hne : S.Nonempty := exists_dvr_notMem hN π hπ hz₀
  have data : ∀ z ∈ S, ∃ (p : X.functionField) (m t : ℤ), p ≠ 0 ∧ 1 ≤ m ∧
      (∀ u, UnitAt z u → ∀ k : ℤ, RegAt z (u * p ^ k) ↔ 0 ≤ k) ∧
      (∃ u, UnitAt z u ∧ fnOf ⊤ trivial π = u * p ^ m) ∧
      ∀ i, z ∈ L.U i → ∃ v, UnitAt z v ∧ (τ i : X.functionField) = v * p ^ t := fun z hz => by
    haveI := hz.2
    exact point_data π hπ0 hz.1 L τ hL hr
  choose! p m t hp hm hreg hπrep hτrep using data
  obtain ⟨x₀, hx₀, hmax⟩ := Set.exists_max_image S (fun z => (t z : ℚ) / (m z)) hS hne
  have hM : (((m x₀).toNat : ℕ) : ℤ) = m x₀ := Int.toNat_of_nonneg (by linarith [hm x₀ hx₀])
  have key : ∀ z ∈ S, ∀ i, z ∈ L.U i → ∃ u, UnitAt z u ∧
      fnOf ⊤ trivial π ^ t x₀ * ((τ i : X.functionField) ^ (m x₀).toNat)⁻¹ =
        u * p z ^ (m z * t x₀ - t z * m x₀) := by
    intro z hz i hi
    obtain ⟨u, hu, e1⟩ := hπrep z hz
    obtain ⟨v, hv, e2⟩ := hτrep z hz i hi
    refine ⟨u ^ t x₀ * (v ^ ((m x₀).toNat : ℤ))⁻¹,
      (unitAt_zpow hu _).mul (unitAt_zpow hv _).inv, ?_⟩
    rw [e1, e2, zpow_exponent_identity (hp z hz), hM]
  refine ⟨(m x₀).toNat, t x₀, x₀, by have := hm x₀ hx₀; omega, hx₀.1, ?_, ?_⟩
  · intro i z hi hdvr
    by_cases hzb : z ∈ X.basicOpen π
    · have h1 := (unitAt_fnOf_iff (show z ∈ (⊤ : X.Opens) from trivial) trivial π).2 hzb
      have h2 := unitAt_zpow (hτ i z hi hzb) ((m x₀).toNat : ℤ)
      rw [zpow_natCast] at h2
      exact ((unitAt_zpow h1 _).mul h2.inv).regAt
    · have hz : z ∈ S := ⟨hzb, hdvr⟩
      obtain ⟨u, hu, e⟩ := key z hz i hi
      rw [e, hreg z hz u hu]
      have h := hmax z hz
      have hmz : (0 : ℚ) < m z := by exact_mod_cast (hm z hz)
      have hm0 : (0 : ℚ) < m x₀ := by exact_mod_cast (hm x₀ hx₀)
      rw [div_le_div_iff₀ hmz hm0] at h
      have h' : t z * m x₀ ≤ t x₀ * m z := by exact_mod_cast h
      linarith
  · intro i hi
    obtain ⟨u, hu, e⟩ := key x₀ hx₀ i hi
    rw [e, mul_comm (m x₀) (t x₀), sub_self, zpow_zero, mul_one]
    exact hu
