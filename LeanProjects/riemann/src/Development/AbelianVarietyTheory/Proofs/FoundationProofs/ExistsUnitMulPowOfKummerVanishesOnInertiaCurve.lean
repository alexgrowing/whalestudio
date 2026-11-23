import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFirstChernClassOfLineBundle
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InertFixesRootOfUnitRatio
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCongOfCongOnFixed
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GaloisOfPrimePowerDegree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInertiaElementRestrictingToFiniteGalois
open GlobalTheory.NeedB Polynomial

namespace GlobalTheory.KumVal

theorem val_term_le_one {F : Type} [Field F] {O : ValuationSubring F} {β : Type} (s : Finset β) (f : β → F)
    (hf : ∀ i ∈ s, ∀ j ∈ s, f i ≠ 0 → O.valuation (f i) = O.valuation (f j) → i = j)
    (hs : O.valuation (∑ i ∈ s, f i) ≤ 1) : ∀ i ∈ s, O.valuation (f i) ≤ 1 := by
  classical
  intro i hi
  obtain ⟨j, hj, hmax⟩ := s.exists_max_image (fun i => O.valuation (f i)) ⟨i, hi⟩
  by_cases h0 : f j = 0
  · refine (hmax i hi).trans ?_
    simp [h0]
  refine (hmax i hi).trans ?_
  rw [← Finset.add_sum_erase s f hj] at hs
  rwa [Valuation.map_add_eq_of_lt_left] at hs
  refine Valuation.map_sum_lt _ (by simpa using h0) fun k hk => ?_
  rw [Finset.mem_erase] at hk
  exact lt_of_le_of_ne (hmax k hk.2) fun he => hk.1 (hf j hj k hk.2 h0 he.symm).symm

theorem cong_on_adjoin : ∀ (W K : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field K] [Algebra W K]
    [IsFractionRing W K] (F : Type) [Field F]
    [Algebra K F] [Algebra W F] [IsScalarTower W K F]
    (O : ValuationSubring F),
    (∀ w : W, algebraMap W F w ∈ O) → (∀ w ∈ IsLocalRing.maximalIdeal W, algebraMap W F w ∈ O.nonunits) →
    ∀ (ϖ : W), Irreducible ϖ → ∀ (l : ℕ), l ≠ 0 → ∀ (x : F), x ^ l = algebraMap W F ϖ →
    ∀ (g : F ≃ₐ[K] F) (b : F), b ∈ IntermediateField.adjoin K {x} →
    O.valuation b ≤ 1 → O.valuation (g b - b) < 1 := by
  intro W K _ _ _ _ _ _ F _ _ _ _ O hO hm ϖ hϖ l hl0 x hx g b hb hb1
  have hϖ0 : ϖ ≠ 0 := hϖ.ne_zero
  set ϖK : K := algebraMap W K ϖ with hϖK
  have hx' : x ^ l = algebraMap K F ϖK := by
    rw [hx, hϖK, ← IsScalarTower.algebraMap_apply]
  have hunit : ∀ u : Wˣ, O.valuation (algebraMap W F (u : W)) = 1 := by
    intro u
    have a1 := (O.valuation_le_one_iff _).2 (hO u)
    have a2 := (O.valuation_le_one_iff _).2 (hO ((u⁻¹ : Wˣ) : W))
    have e : O.valuation (algebraMap W F (u : W)) * O.valuation (algebraMap W F ((u⁻¹ : Wˣ) : W)) = 1 := by
      rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
    refine le_antisymm a1 ?_
    by_contra hc
    push_neg at hc
    have := mul_lt_one_of_lt_of_le hc a2
    rw [e] at this
    exact lt_irrefl _ this
  have hϖlt : O.valuation (algebraMap W F ϖ) < 1 := by
    have := hm ϖ ((IsLocalRing.mem_maximalIdeal _).2 hϖ.not_isUnit)
    exact this
  have hWv : ∀ w : W, w ≠ 0 → ∃ n : ℕ,
      O.valuation (algebraMap W F w) = O.valuation (algebraMap W F ϖ) ^ n := by
    intro w hw
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hw hϖ
    exact ⟨n, by rw [map_mul, map_mul, hunit, _root_.one_mul, map_pow, map_pow]⟩

  have hvpos : ∀ w : W, w ≠ 0 → O.valuation (algebraMap W F w) ≠ 0 := by
    intro w hw
    rw [Valuation.ne_zero_iff]
    intro h0
    apply hw
    have : algebraMap W K w = 0 := by
      rw [IsScalarTower.algebraMap_apply W K F] at h0
      exact (map_eq_zero _).mp h0
    exact (IsFractionRing.injective W K) (by rw [this, map_zero])
  have hK : ∀ a : K, a ≠ 0 → ∃ m : ℤ,
      O.valuation (algebraMap K F a) = O.valuation (algebraMap K F ϖK) ^ m := by
    intro a ha
    obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := W) a
    have hq0 : q ≠ 0 := nonZeroDivisors.ne_zero hq
    have hp0 : p ≠ 0 := by rintro rfl; simp at ha
    obtain ⟨n, hn⟩ := hWv p hp0
    obtain ⟨k, hk⟩ := hWv q hq0
    refine ⟨(n : ℤ) - k, ?_⟩
    rw [map_div₀, map_div₀, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, hϖK,
      ← IsScalarTower.algebraMap_apply, hn, hk, zpow_sub₀ (hvpos ϖ hϖ0), zpow_natCast, zpow_natCast]
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [zero_pow hl0, eq_comm] at hx
    exact hvpos ϖ hϖ0 (by rw [hx, map_zero])
  set t := O.valuation x with ht
  have htl : O.valuation (algebraMap K F ϖK) = t ^ l := by rw [← hx', map_pow]
  have ht0 : 0 < t := zero_lt_iff.mpr (by simpa [ht] using hx0)
  have ht1 : t < 1 := by
    have := hϖlt
    rw [IsScalarTower.algebraMap_apply W K F, ← hϖK, htl] at this
    exact (pow_lt_one_iff hl0).mp this
  have hinj : Function.Injective fun n : ℤ => t ^ n := zpow_right_injective₀ ht0 ht1.ne
  have hval : ∀ (a : K) (i : ℕ), algebraMap K F a * x ^ i ≠ 0 →
      ∃ m : ℤ, O.valuation (algebraMap K F a * x ^ i) = t ^ ((i : ℤ) + l * m) := by
    intro a i ha
    have ha0 : a ≠ 0 := by rintro rfl; simp at ha
    obtain ⟨m, hm⟩ := hK a ha0
    refine ⟨m, ?_⟩
    rw [map_mul, hm, htl, map_pow, zpow_add₀ ht0.ne', zpow_mul, zpow_natCast, zpow_natCast, mul_comm]
  have hmod : ∀ (i j : ℕ) (m n : ℤ), i < l → j < l → t ^ ((i : ℤ) + l * m) = t ^ ((j : ℤ) + l * n) →
      i = j := by
    intro i j m n hi hj he
    have := congrArg (· % (l : ℤ)) (hinj he)
    simp only [Int.add_mul_emod_self_left] at this
    rw [Int.emod_eq_of_lt (by omega) (by omega), Int.emod_eq_of_lt (by omega) (by omega)] at this
    omega
  have hq : (X ^ l - C ϖK).Monic := monic_X_pow_sub_C _ hl0
  have hint : IsIntegral K x := ⟨X ^ l - C ϖK, hq, by simp [hx']⟩
  have hb' : b ∈ Algebra.adjoin K {x} := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic]; exact hb
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hb'
  obtain ⟨p₀, rfl⟩ := hb'
  set p := p₀ %ₘ (X ^ l - C ϖK)
  have hp : aeval x p = aeval x p₀ := aeval_modByMonic_eq_self_of_root (by simp [hx'])
  have hdeg : p.natDegree < l := by
    have := natDegree_modByMonic_lt p₀ hq (by
      intro h1
      have := congrArg natDegree h1
      rw [natDegree_X_pow_sub_C, natDegree_one] at this
      exact hl0 this)
    rwa [natDegree_X_pow_sub_C] at this
  change O.valuation (aeval x p₀) ≤ 1 at hb1
  change O.valuation (g (aeval x p₀) - aeval x p₀) < 1
  rw [← hp, aeval_eq_sum_range' hdeg] at hb1 ⊢
  simp only [Algebra.smul_def] at hb1 ⊢
  have hle := val_term_le_one _ _ (fun i hi j hj h0 he => by
    obtain ⟨m, hm⟩ := hval _ i h0
    obtain ⟨n, hn⟩ := hval (p.coeff j) j (by
      intro h00
      rw [h00, map_zero] at he
      exact h0 (by simpa using he))
    exact hmod i j m n (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) (by rw [← hm, ← hn, he])) hb1
  have hgx : O.valuation (g x) = t := by
    refine pow_left_injective hl0 ?_
    show _ ^ l = t ^ l
    rw [← map_pow, ← map_pow, hx', g.commutes, htl]
  rw [map_sum, ← Finset.sum_sub_distrib]
  refine Valuation.map_sum_lt _ one_ne_zero fun i hi => ?_
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · simp
  have hlt : O.valuation (algebraMap K F (p.coeff i) * x ^ i) < 1 := by
    refine lt_of_le_of_ne (hle i hi) fun he => ?_
    obtain ⟨m, hm⟩ := hval (p.coeff i) i (by intro h0; simp [h0] at he)
    have := hmod i 0 m 0 (Finset.mem_range.mp hi) (by omega) (by rw [← hm, he]; simp)
    omega
  refine Valuation.map_sub_lt _ ?_ hlt
  rw [map_mul g, g.commutes, map_pow g, map_mul, map_pow, hgx]
  rwa [map_mul, map_pow] at hlt

theorem exists_inert_moves_root (W K F : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field K] [CharZero K]
    [Algebra W K] [IsFractionRing W K] [Field F] [Algebra K F] [IsAlgClosure K F] [Algebra W F] [IsScalarTower W K F]
    (O : ValuationSubring F) (h1 : ∀ w : W, algebraMap W F w ∈ O)
    (h2 : ∀ w ∈ IsLocalRing.maximalIdeal W, algebraMap W F w ∈ O.nonunits) (ϖ : W) (hϖ : Irreducible ϖ) (l : ℕ)
    (hl : l ≠ 0) (ζ π : F) (hζ : IsPrimitiveRoot ζ l) (hπ : π ^ l = algebraMap W F ϖ) :
    ∃ (σ : F ≃ₐ[K] F) (ξ : F), Inert O σ ∧ IsPrimitiveRoot ξ l ∧ σ π = ξ * π := by
  have hπ' : π ^ l = algebraMap K F (algebraMap W K ϖ) := by rw [hπ, ← IsScalarTower.algebraMap_apply]
  have hmin := GlobalTheory.TameKummer.minpoly_eq K hϖ hl (ρ := π) hπ'
  have hmin' := GlobalTheory.TameKummer.minpoly_eq K hϖ hl (ρ := ζ * π)
    (by rw [mul_pow, hζ.pow_eq_one, _root_.one_mul]; exact hπ')
  haveI : IsGalois K F := {}
  obtain ⟨g, hg⟩ := (Normal.minpoly_eq_iff_mem_orbit (F := K) F (x := ζ * π) (y := π)).1
    (hmin'.trans hmin.symm)
  change g π = ζ * π at hg
  let S := integralClosure W F
  have hc : SMulCommClass (F ≃ₐ[K] F) W F := ⟨fun g v x => by
    rw [← IsScalarTower.algebraMap_smul K v x, ← IsScalarTower.algebraMap_smul K v (g • x)]
    simp only [AlgEquiv.smul_def, Algebra.smul_def, _root_.map_mul, AlgEquiv.commutes]⟩
  letI : TopologicalSpace S := ⊥
  haveI : DiscreteTopology S := ⟨rfl⟩
  haveI : ContinuousSMul (F ≃ₐ[K] F) S := by
    rw [continuousSMul_iff_stabilizer_isOpen]
    intro x
    have := stabilizer_isOpen_of_isIntegral (K := K) (x : F)
    convert this using 1
    ext g
    simp only [SetLike.mem_coe, MulAction.mem_stabilizer_iff]
    exact Subtype.ext_iff
  let H := MulAction.stabilizer (F ≃ₐ[K] F) π
  have hH : IsClosed (H : Set (F ≃ₐ[K] F)) :=
    H.isClosed_of_isOpen (stabilizer_isOpen_of_isIntegral (K := K) π)
  haveI : CompactSpace H := isCompact_iff_compactSpace.mp hH.isCompact
  have hSO : ∀ b : F, IsIntegral W b → b ∈ O := fun b hb => GlobalTheory.ProlongConj.mem_of_isIntegral O h1 hb
  let incl : S →+* O := (S.val.toRingHom).codRestrict O (fun b => hSO b b.2)
  let Q : Ideal S := (IsLocalRing.maximalIdeal O).comap incl
  have hQ : ∀ b : S, b ∈ Q ↔ O.valuation (b : F) < 1 := fun b =>
    ValuationSubring.valuation_lt_one_iff O (incl b)
  obtain ⟨a₁, ha₁, a₂, ha₂, hcong⟩ := GlobalTheory.InertiaMovesRoot.exists_cong_of_cong_on_fixed (R := W) H Q g
    (fun b hb => by
      rw [hQ]
      refine cong_on_adjoin W K F O h1 h2 ϖ hϖ l hl π hπ g b ?_ ((O.valuation_le_one_iff _).mpr (hSO b b.2))
      rw [← InfiniteGalois.fixedField_fixingSubgroup (IntermediateField.adjoin K {π}),
        IntermediateField.mem_fixedField_iff]
      intro e he
      exact congrArg Subtype.val (hb e (he ⟨π, IntermediateField.mem_adjoin_simple_self K π⟩)))
  let σ := a₂ * g * a₁
  have hσπ : σ π = a₂ ζ * π := by
    have e1 : a₁ π = π := ha₁
    have e2 : a₂ π = π := ha₂
    simp only [σ, AlgEquiv.mul_apply, e1, hg, map_mul, e2]
  have hσS : ∀ b : F, IsIntegral W b → O.valuation (σ b - b) < 1 := fun b hb =>
    (hQ (σ • ⟨b, hb⟩ - ⟨b, hb⟩)).1 (hcong ⟨b, hb⟩)
  have hin := GlobalTheory.InertiaRestrict.mem_inertia_of_sub_lt_one W K F O h1 σ hσS
  rw [GlobalTheory.Published.AbVarRed.mem_inertia_iff] at hin
  exact ⟨σ, a₂ ζ, fun x hx => hin.2 x ((O.valuation_le_one_iff x).1 hx), hζ.map_of_injective a₂.injective, hσπ⟩

theorem exists_unit_of_inert_fixes (W K Ω : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field K]
    [CharZero K] [Algebra W K] [IsFractionRing W K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (B : ValuationSubring Ω) (h1 : ∀ x : W, algebraMap K Ω (algebraMap W K x) ∈ B)
    (h2 : ∀ x ∈ IsLocalRing.maximalIdeal W, algebraMap K Ω (algebraMap W K x) ∈ B.nonunits)
    (N : ℕ) (hN : 0 < N) (hvN : B.valuation (N : Ω) = 1) (ζ : Ω) (hζ : IsPrimitiveRoot ζ N)
    (w : K) (θ : Ω) (hw : w ≠ 0) (hθ : θ ^ N = algebraMap K Ω w)
    (hfix : ∀ g : Ω ≃ₐ[K] Ω, Inert B g → g θ = θ) :
    ∃ c : K, c ≠ 0 ∧ B.valuation (algebraMap K Ω (w / c ^ N)) = 1 := by
  letI : Algebra W Ω := ((algebraMap K Ω).comp (algebraMap W K)).toAlgebra
  haveI : IsScalarTower W K Ω := .of_algebraMap_eq fun _ => rfl
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible W
  obtain ⟨π, hπ⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap W Ω ϖ) hN
  obtain ⟨σ, ξ, hσ, hξ, hσπ⟩ := exists_inert_moves_root W K Ω B h1 h2 ϖ hϖ N hN.ne' ζ π hζ hπ
  obtain ⟨m, u, hwu⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible (K := K) hϖ hw
  have hϖK : algebraMap W K ϖ ≠ 0 := by
    rw [map_ne_zero_iff _ (IsFractionRing.injective W K)]; exact hϖ.ne_zero
  have hπ' : π ^ N = algebraMap K Ω (algebraMap W K ϖ) := hπ
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [zero_pow hN.ne', eq_comm] at hπ'
    exact hϖK ((_root_.map_eq_zero _).1 hπ')
  have hu1 : B.valuation (algebraMap K Ω (algebraMap W K (u : W))) = 1 :=
    ValuationSubring.valuation_unit B (Units.map (((algebraMap W Ω).codRestrict B h1).toMonoidHom) u)
  rw [Units.smul_def, Algebra.smul_def] at hwu
  have hpow : (θ / π ^ m) ^ N = algebraMap K Ω (algebraMap W K (u : W)) := by
    rw [div_pow, hθ, hwu, map_mul, map_zpow₀, ← hπ', ← zpow_natCast (π ^ m), ← zpow_natCast π, ← zpow_mul,
      ← zpow_mul, mul_comm m, mul_div_cancel_right₀ _ (zpow_ne_zero _ hπ0)]
  have hq : σ (θ / π ^ m) = θ / π ^ m := by
    refine GlobalTheory.inert_fixes_root_of_unit_ratio K Ω B σ N 1 _ hN hvN hσ (map_one σ) one_ne_zero ?_ ?_
    · rw [hpow]; exact σ.commutes _
    · rw [one_pow, div_one, hpow, hu1]
  have hθ0 : θ ≠ 0 := by
    rintro rfl
    rw [zero_pow hN.ne', eq_comm] at hθ
    exact hw ((_root_.map_eq_zero _).1 hθ)
  have hξm : ξ ^ m = 1 := by
    rw [map_div₀, hfix σ hσ, map_zpow₀, hσπ, mul_zpow, div_eq_mul_inv, div_eq_mul_inv, mul_right_inj' hθ0, inv_inj] at hq
    exact (mul_eq_right₀ (zpow_ne_zero _ hπ0)).1 hq
  obtain ⟨q, hq⟩ := (hξ.zpow_eq_one_iff_dvd m).1 hξm
  refine ⟨algebraMap W K ϖ ^ q, zpow_ne_zero _ hϖK, ?_⟩
  rw [hwu, hq, ← zpow_natCast (algebraMap W K ϖ ^ q), ← zpow_mul, mul_comm q,
    mul_div_cancel_right₀ _ (zpow_ne_zero _ hϖK), hu1]

theorem exists_unit_of_inert_fixes_dedekind (A K Ω : Type) [CommRing A] [IsDedekindDomain A] [Field K]
    [CharZero K] [Algebra A K] [IsFractionRing A K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (B : ValuationSubring Ω) (hB : ∀ x : A, algebraMap K Ω (algebraMap A K x) ∈ B)
    (N : ℕ) (hN : 0 < N) (hvN : B.valuation (N : Ω) = 1) (ζ : Ω) (hζ : IsPrimitiveRoot ζ N)
    (w : K) (θ : Ω) (hw : w ≠ 0) (hθ : θ ^ N = algebraMap K Ω w)
    (hfix : ∀ g : Ω ≃ₐ[K] Ω, Inert B g → g θ = θ) :
    ∃ c : K, c ≠ 0 ∧ B.valuation (algebraMap K Ω (w / c ^ N)) = 1 := by
  let f : A →+* B := ((algebraMap K Ω).comp (algebraMap A K)).codRestrict B hB
  let P : Ideal A := (IsLocalRing.maximalIdeal B).comap f
  have hP : ∀ a : A, a ∈ P ↔ B.valuation (algebraMap K Ω (algebraMap A K a)) < 1 := fun a =>
    B.valuation_lt_one_iff (f a)
  haveI : P.IsPrime := Ideal.comap_isPrime _ _
  have hone : ∀ a : A, a ∉ P → B.valuation (algebraMap K Ω (algebraMap A K a)) = 1 := fun a ha =>
    le_antisymm ((B.valuation_le_one_iff _).2 (hB a)) (not_lt.1 fun h => ha ((hP a).2 h))
  by_cases hP0 : P = ⊥
  · refine ⟨1, one_ne_zero, ?_⟩
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := A) w
    have ha0 : a ≠ 0 := by rintro rfl; simp at hw
    rw [one_pow, div_one, map_div₀, map_div₀, hone a (by rw [hP0]; simpa using ha0),
      hone b (by rw [hP0]; simpa using nonZeroDivisors.ne_zero hb), div_one]
  let v : IsDedekindDomain.HeightOneSpectrum A := ⟨P, inferInstance, hP0⟩
  let W := v.valuationSubringAtPrime K
  haveI : IsLocalization P.primeCompl W :=
    Localization.subalgebra.isLocalization_ofField K P.primeCompl P.primeCompl_le_nonZeroDivisors
  haveI : IsDiscreteValuationRing W :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain A hP0 W
  have key : ∀ (a : A) (s : P.primeCompl), B.valuation (algebraMap K Ω (algebraMap W K (IsLocalization.mk' W a s))) =
      B.valuation (algebraMap K Ω (algebraMap A K a)) := fun a s => by
    have e := congrArg (fun y => B.valuation (algebraMap K Ω (algebraMap W K y))) (IsLocalization.mk'_spec W a s)
    simp only [map_mul, ← IsScalarTower.algebraMap_apply A W K] at e
    rwa [hone s s.2, _root_.mul_one] at e
  refine exists_unit_of_inert_fixes W K Ω B (fun x => ?_) (fun x hx => ?_) N hN hvN ζ hζ w θ hw hθ hfix
  · obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl x
    rw [← B.valuation_le_one_iff, key, B.valuation_le_one_iff]
    exact hB a
  · obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl x
    rw [ValuationSubring.mem_nonunits_iff, key, ← hP]
    exact (IsLocalization.AtPrime.mk'_mem_maximal_iff W P a s).1 hx

theorem exists_unit_of_kum_eq_zero : ∀ (k K Ω : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k[X] K] [Algebra (RatFunc k) K]
    [IsScalarTower k[X] (RatFunc k) K] [FiniteDimensional (RatFunc k) K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (N : ℕ) (ζ : Ω), 0 < N → IsPrimitiveRoot ζ N →
    ∀ (w : K) (θ : Ω), w ≠ 0 → θ ^ N = algebraMap K Ω w →
    ∀ B : ValuationSubring Ω, GlobalTheory.NeedB.Over (FunctionField.ringOfIntegers k K).toSubring B →
      (∀ g : Ω ≃ₐ[K] Ω, Inert B g → kum (N := N) ζ θ g = 0) →
      ∃ c : K, c ≠ 0 ∧ B.valuation (algebraMap K Ω (w / c ^ N)) = 1 := by
  intro k K Ω _ _ _ _ _ _ _ _ _ _ _ N ζ hN hζ w θ hw hθ B hB hk
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI : CharZero K := (((algebraMap k[X] K).comp Polynomial.C).charZero_iff (RingHom.injective _)).1 inferInstance
  haveI : CharZero (RatFunc k) := charZero_of_injective_algebraMap (algebraMap k (RatFunc k)).injective
  have hNK0 : (N : K) ≠ 0 := by exact_mod_cast hN.ne'
  have hNinv : (N : K)⁻¹ ∈ FunctionField.ringOfIntegers k K := by
    have : ((algebraMap k[X] K).comp Polynomial.C) ((N : k)⁻¹) = (N : K)⁻¹ := by
      rw [map_inv₀, map_natCast]
    rw [← this]
    exact Subalgebra.algebraMap_mem _ _
  have hvN : B.valuation (N : Ω) = 1 := by
    have h1 : B.valuation (N : Ω) ≤ 1 := (B.valuation_le_one_iff _).2 (natCast_mem B N)
    have h2 := (B.valuation_le_one_iff _).2 (hB _ hNinv)
    have h0 : (N : Ω) ≠ 0 := by
      rw [← map_natCast (algebraMap K Ω)]; exact (_root_.map_ne_zero _).2 hNK0
    rw [map_inv₀, map_natCast, map_inv₀, inv_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 h0))] at h2
    exact le_antisymm h1 h2
  have hθ0 : θ ≠ 0 := by
    rintro rfl
    rw [zero_pow hN.ne', eq_comm] at hθ
    exact hw ((_root_.map_eq_zero _).1 hθ)
  refine exists_unit_of_inert_fixes_dedekind (FunctionField.ringOfIntegers k K) K Ω B (fun x => hB _ x.2) N hN hvN ζ hζ
    w θ hw hθ fun g hg => ?_
  have hξ : (g θ / θ) ^ N = 1 := by
    rw [div_pow, ← map_pow, hθ, g.commutes, div_self ((_root_.map_ne_zero _).2 hw)]
  obtain ⟨i, hiN, hi⟩ := hζ.eq_pow_of_pow_eq_one hξ
  have h1 : g θ = ζ ^ ((i : ZMod N)).val * θ := by
    rw [ZMod.val_cast_of_lt hiN, hi]; field_simp
  have h2 := kum_choose_spec (N := N) ⟨_, h1⟩
  rwa [hk g hg, ZMod.val_zero, pow_zero, _root_.one_mul] at h2

end GlobalTheory.KumVal
