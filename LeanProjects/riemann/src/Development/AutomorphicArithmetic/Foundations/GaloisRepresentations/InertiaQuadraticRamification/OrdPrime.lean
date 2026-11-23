import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.UnrCharAtOf
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChebotarevDegreeOneIffCheb
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChebotarevDegreeOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOpenNormalFiniteIndexLeAbsGaloisGroup
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOpenNormalFiniteIndexLeAbsGaloisGroupStatement
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsCoprimePowOfMemIneKer
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AbsNormPrimeIffInertiaDegEqOneAndFiniteRamified

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published
open UpperTheory.Gal.UnramifiedFromSplittingCriterion
open scoped Pointwise

private theorem op_isPlaceOver {Ω : Type} [Field Ω] [Algebra ℚ Ω] (A : ValuationSubring Ω)
    (v : HeightOneSpectrum (𝓞 ℚ)) (p : ℕ) (hp : p.Prime) (hv : ((p : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
    (hA : A.valuation (p : Ω) < 1) : IsPlaceOver A v := by
  intro x
  obtain ⟨n, rfl⟩ : ∃ n : ℤ, x = (n : 𝓞 ℚ) :=
    ⟨Rat.ringOfIntegersEquiv x, Rat.ringOfIntegersEquiv.injective (by rw [map_intCast]; simp)⟩
  have hint : ∀ m : ℤ, A.valuation (m : Ω) ≤ 1 := fun m =>
    (A.valuation_le_one_iff _).mpr (intCast_mem A m)
  have hcast : algebraMap ℚ Ω (((n : 𝓞 ℚ)) : ℚ) = (n : Ω) := by simp
  rw [hcast]
  by_cases hd : (p : ℤ) ∣ n
  · obtain ⟨m, rfl⟩ := hd
    constructor
    · intro _
      have : (((p : ℤ) * m : ℤ) : 𝓞 ℚ) = (p : 𝓞 ℚ) * (m : 𝓞 ℚ) := by push_cast; rfl
      rw [this]
      exact v.asIdeal.mul_mem_right _ hv
    · intro _
      have : ((((p : ℤ) * m : ℤ)) : Ω) = (p : Ω) * (m : Ω) := by push_cast; rfl
      rw [this, Valuation.map_mul]
      exact mul_lt_one_of_lt_of_le hA (hint m)
  · obtain ⟨a, b, hab⟩ := (Nat.prime_iff_prime_int.1 hp).coprime_iff_not_dvd.2 hd
    constructor
    · intro h
      exfalso
      have e : (1 : Ω) = (a : Ω) * (p : Ω) + (b : Ω) * (n : Ω) := by
        have := congrArg (fun t : ℤ => (t : Ω)) hab
        push_cast at this
        exact this.symm
      have h1 : A.valuation (1 : Ω) < 1 := by
        rw [e]
        refine Valuation.map_add_lt _ ?_ ?_
        · rw [Valuation.map_mul, mul_comm]; exact mul_lt_one_of_lt_of_le hA (hint a)
        · rw [Valuation.map_mul, mul_comm]; exact mul_lt_one_of_lt_of_le h (hint b)
      simp at h1
    · intro h
      exfalso
      have e : (1 : 𝓞 ℚ) = (a : 𝓞 ℚ) * (p : 𝓞 ℚ) + (b : 𝓞 ℚ) * (n : 𝓞 ℚ) := by
        have := congrArg (fun t : ℤ => (t : 𝓞 ℚ)) hab
        push_cast at this
        exact this.symm
      have h1 : (1 : 𝓞 ℚ) ∈ v.asIdeal := by
        rw [e]
        exact v.asIdeal.add_mem (v.asIdeal.mul_mem_left _ hv) (v.asIdeal.mul_mem_left _ h)
      exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)

private theorem op_normV (v : HeightOneSpectrum (𝓞 ℚ)) : normV v = Ideal.absNorm v.asIdeal := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rfl

private theorem op_ringHom_eq {Y Ω : Type} [Field Y] [NumberField Y] [Field Ω] [CharZero Ω] (j₁ j₂ : Y →+* Ω)
    (h : ∀ i, j₁ (Module.finBasis ℚ Y i) = j₂ (Module.finBasis ℚ Y i)) (y : Y) : j₁ y = j₂ y := by
  have := (Module.finBasis ℚ Y).ext (f₁ := (RingHom.toRatAlgHom j₁).toLinearMap)
    (f₂ := (RingHom.toRatAlgHom j₂).toLinearMap) h
  exact DFunLike.congr_fun this y

private theorem op_dec_le {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    {N : Subgroup (G F Ω)} (hNo : IsOpen (N : Set (G F Ω))) {B : ValuationSubring Ω}
    {u : HeightOneSpectrum (𝓞 F)} (hB : IsPlaceOver B u) (hI : Ine (F := F) B ≤ N) {σ : G F Ω}
    (hσ : IsFrob B (normV u) σ) (hσN : σ ∈ N) : Dec (F := F) B ≤ N := by
  intro d hd
  have h := GlobalTheory.TameQuot.closure_frob_sup_Ine F Ω B u hB ⟨σ, hσ.1⟩ hσ
  have hc : IsClosed ((N.subgroupOf (Dec (F := F) B) : Subgroup (Dec (F := F) B)) : Set (Dec (F := F) B)) :=
    (N.isClosed_of_isOpen hNo).preimage continuous_subtype_val
  have h2 := Subgroup.topologicalClosure_minimal
    (Subgroup.zpowers (⟨σ, hσ.1⟩ : Dec (F := F) B) ⊔ (Ine (F := F) B).subgroupOf (Dec (F := F) B))
    (sup_le (Subgroup.zpowers_le.2 (Subgroup.mem_subgroupOf.2 hσN))
      (fun x hx => Subgroup.mem_subgroupOf.2 (hI (Subgroup.mem_subgroupOf.1 hx)))) hc
  rw [h] at h2
  exact Subgroup.mem_subgroupOf.1 (h2 (Subgroup.mem_top (⟨d, hd⟩ : Dec (F := F) B)))

private theorem op_arith {ℓ m j k t : ℕ} (hℓ : ℓ.Prime) (hm : m ∣ ℓ ^ j * t) (hm0 : m ≠ 0) (hk : ℓ ^ k ∣ t)
    (hn : ¬ ℓ ^ k ∣ m) : m ∣ t := by
  obtain ⟨a, m', hm', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm0 ℓ hℓ.ne_one
  have hak : a < k := by
    by_contra h
    exact hn (Dvd.dvd.mul_right (pow_dvd_pow ℓ (not_lt.1 h)) _)
  have hco : Nat.Coprime ℓ m' := (Nat.Prime.coprime_iff_not_dvd hℓ).2 hm'
  have h1 : m' ∣ t := (hco.symm.pow_right j).dvd_of_dvd_mul_left ((Dvd.intro_left _ rfl).trans hm)
  have h2 : ℓ ^ a ∣ t := (pow_dvd_pow ℓ hak.le).trans hk
  exact (hco.pow_left a).mul_dvd_of_dvd_of_dvd h2 h1

private theorem op_val_root {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {q n : ℕ} {y : Ω} (hn0 : n ≠ 0)
    (hq : ¬ A.valuation (q : Ω) < 1) (hy : y ^ n = (q : Ω)) : A.valuation y = 1 := by
  have h1 : A.valuation (q : Ω) = 1 := le_antisymm (valuation_natCast_le_one A q) (not_lt.1 hq)
  rw [← hy, map_pow] at h1
  exact (pow_eq_one_iff.1 h1).resolve_right hn0

private theorem op_val {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {p q n t : ℕ} {y w : Ω}
    (hp : A.valuation (p : Ω) < 1) (hn : ¬ A.valuation (n : Ω) < 1) (hn0 : n ≠ 0)
    (hq : ¬ A.valuation (q : Ω) < 1) (hy : y ^ n = (q : Ω)) (hw : w ^ n = (q : Ω))
    (hfrob : A.valuation (w - y ^ (n * t + 1)) < 1) (hqt : (p : ℤ) ∣ (q : ℤ) ^ t - 1) : w = y := by
  have hvy := op_val_root A hn0 hq hy
  have hy0 : y ≠ 0 := by
    rintro rfl
    simp at hvy
  have hq0 : (q : Ω) ≠ 0 := by
    rw [← hy]
    exact pow_ne_zero _ hy0
  obtain ⟨ξ, rfl⟩ : ∃ ξ, w = ξ * y := ⟨w / y, (div_mul_cancel₀ _ hy0).symm⟩
  have hξn : ξ ^ n = 1 := by
    rw [mul_pow, hy] at hw
    exact mul_right_cancel₀ hq0 (hw.trans (one_mul _).symm)
  have e1 : ξ * y - y ^ (n * t + 1) = y * (ξ - (q : Ω) ^ t) := by
    rw [pow_succ, pow_mul, hy]
    ring
  rw [e1, map_mul, hvy, one_mul] at hfrob
  obtain ⟨c, hc⟩ := hqt
  have e2 : (q : Ω) ^ t - 1 = (p : Ω) * (c : Ω) := by
    have := congrArg (fun z : ℤ => (z : Ω)) hc
    push_cast at this
    exact this
  have h2 : A.valuation ((q : Ω) ^ t - 1) < 1 := by
    rw [e2, map_mul]
    exact mul_lt_one_of_lt_of_le hp ((A.valuation_le_one_iff _).mpr (intCast_mem A c))
  have h3 : A.valuation (ξ - 1) < 1 := by
    have e3 : ξ - 1 = (ξ - (q : Ω) ^ t) + ((q : Ω) ^ t - 1) := by ring
    rw [e3]
    exact Valuation.map_add_lt _ hfrob h2
  rw [eq_of_pow_eq_one A hn hξn (one_pow n) h3, one_mul]

theorem UpperTheory.Gal.UnramifiedFromSplittingCriterion.ordPrime :
    KumMove → OrdPrime := by
  classical
  intro hKum E Ω _ _ _ _ _ ℓ k q B hℓ hq
  have hc0 : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  have hcl : IsAlgClosure ℚ Ω := ⟨IsAlgClosure.isAlgClosed E, Algebra.IsAlgebraic.trans ℚ E Ω⟩
  have hac : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E

  let X : Set Ω := Set.range fun i => algebraMap E Ω (Module.finBasis ℚ E i)
  have hXfin : X.Finite := Set.finite_range _
  let L := IntermediateField.adjoin ℚ X
  have hLfin : FiniteDimensional ℚ L := by
    have : Finite X := hXfin
    exact IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  obtain ⟨U0, hU0n, hU0o, -, hU0U⟩ := GlobalTheory.OpenNormal.exists_open_normal_le Ω ℚ L.fixingSubgroup
    (IntermediateField.fixingSubgroup_isOpen L)

  obtain ⟨j, hj⟩ := hKum Ω U0 hU0o ℓ q hℓ hq
  have hℓ0 : ∀ n, 0 < ℓ ^ n := fun n => pow_pos hℓ.pos n
  obtain ⟨ζ, hζ⟩ : ∃ ζ : Ω, IsPrimitiveRoot ζ (ℓ ^ (j + k)) := by
    haveI : NeZero ((ℓ ^ (j + k) : ℕ) : Ω) := ⟨by exact_mod_cast (hℓ0 (j + k)).ne'⟩
    exact HasEnoughRootsOfUnity.exists_primitiveRoot Ω (ℓ ^ (j + k))
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (q : Ω) (hℓ0 j)
  obtain ⟨σ, hσU, hσζ, hσy⟩ := hj (j + k) (by omega) ζ y hζ hy
  let X2 : Set Ω := {ζ, y}
  have hX2fin : X2.Finite := by simp [X2]
  let L2 := IntermediateField.adjoin ℚ X2
  have hL2fin : FiniteDimensional ℚ L2 := by
    have : Finite X2 := hX2fin
    exact IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  obtain ⟨N, hNn, hNo, -, hNU⟩ := GlobalTheory.OpenNormal.exists_open_normal_le Ω ℚ (L2.fixingSubgroup ⊓ U0)
    ((IntermediateField.fixingSubgroup_isOpen L2).inter hU0o)
  have hfix : ∀ n ∈ N, ∀ x ∈ X2, n x = x := fun n hn x hx =>
    (IntermediateField.mem_fixingSubgroup_iff L2 n).1 (hNU hn).1 x (IntermediateField.subset_adjoin ℚ X2 hx)

  set K := max B (max q (ℓ ^ (j + k))) with hK
  have hKne : ((K.factorial : ℕ) : 𝓞 ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero K)
  have hspan : Ideal.span {((K.factorial : ℕ) : 𝓞 ℚ)} ≠ 0 := by
    simpa using hKne
  obtain ⟨v, hvS, hd, -, B0, hB0, hIne, φ, hφ, hφg⟩ := GlobalTheory.Published.chebotarevDegreeOne_iff_cheb.1
    GlobalTheory.Published.chebotarevDegreeOne' ℚ Ω N hNo hNn σ (Ideal.finite_factors hspan).toFinset
  have hKv : ((K.factorial : ℕ) : 𝓞 ℚ) ∉ v.asIdeal := by
    intro h
    apply hvS
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
    exact h
  have hφN : σ⁻¹ * φ ∈ N := by
    have := hNn.conj_mem _ hφg σ⁻¹
    simpa [mul_assoc] using this
  have hφX : ∀ x ∈ X2, φ x = σ x := by
    intro x hx
    have h2 := hfix _ hφN x hx
    have h3 := congrArg σ h2
    rw [AlgEquiv.mul_apply] at h3
    have h4 : σ ((σ⁻¹ : G ℚ Ω) (φ x)) = φ x := mul_inv_apply _
    rw [h4] at h3
    exact h3
  have hφU : φ ∈ U0 := by
    have := U0.mul_mem hσU (hNU hφN).2
    simpa using this
  have hDec : Dec (F := ℚ) B0 ≤ U0 := op_dec_le hU0o hB0 (hIne.trans fun n hn => (hNU hn).2) hφ hφU
  have hpr : (normV v).Prime := by
    rw [op_normV]
    exact ((GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified ℚ).1 v).2 hd
  have hpv : ((normV v : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := by
    rw [op_normV]
    exact Ideal.absNorm_mem _
  have hdvd : ∀ m : ℕ, 0 < m → m ≤ K → ((m : ℕ) : 𝓞 ℚ) ∉ v.asIdeal := by
    intro m hm hmK h
    apply hKv
    obtain ⟨c, hc⟩ := Nat.dvd_factorial hm hmK
    rw [hc, Nat.cast_mul]
    exact v.asIdeal.mul_mem_right _ h
  have hBp : B < normV v := by
    by_contra hle
    exact hdvd _ hpr.pos ((not_lt.1 hle).trans (le_max_left _ _)) hpv
  have hnv : ∀ m : ℕ, 0 < m → m ≤ K → ¬ B0.valuation (m : Ω) < 1 := fun m hm hmK h =>
    hdvd m hm hmK ((hB0 (m : 𝓞 ℚ)).1 (by simpa using h))
  have hpval : B0.valuation ((normV v : ℕ) : Ω) < 1 := by
    simpa using (hB0 ((normV v : ℕ) : 𝓞 ℚ)).2 hpv
  have hqK : q ≤ K := (le_max_left _ _).trans (le_max_right _ _)
  have hMK : ℓ ^ (j + k) ≤ K := (le_max_right _ _).trans (le_max_right _ _)
  have hjK : ℓ ^ j ≤ K := (Nat.pow_le_pow_right hℓ.pos (by omega)).trans hMK
  have hqv := hnv q (by omega) hqK
  refine ⟨normV v, hpr, hBp, ?_, ?_⟩
  · haveI : Fact (normV v).Prime := ⟨hpr⟩

    have hζ0 : ζ ≠ 0 := hζ.ne_zero (hℓ0 _).ne'
    have h1 : φ ζ = ζ ^ normV v := by
      refine eq_of_pow_eq_one B0 (hnv _ (hℓ0 _) hMK) ?_ ?_
        (hφ.2 ζ (valuation_eq_one_of_pow_eq_one B0 (hℓ0 _).ne' hζ.pow_eq_one).le)
      · rw [← map_pow, hζ.pow_eq_one, map_one]
      · rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
    have hφζ : φ ζ = ζ := by
      rw [hφX ζ (Set.mem_insert _ _), hσζ]
    have hpow : ζ ^ (normV v - 1) = 1 := by
      have : ζ ^ (normV v - 1) * ζ = 1 * ζ := by
        rw [← pow_succ, Nat.sub_add_cancel hpr.one_le, one_mul, ← h1, hφζ]
      exact mul_right_cancel₀ hζ0 this
    obtain ⟨c, hc⟩ := hζ.dvd_of_pow_eq_one _ hpow
    have hpt : normV v - 1 = ℓ ^ j * (ℓ ^ k * c) := by
      rw [hc, pow_add, mul_assoc]
    have hpt' : normV v = ℓ ^ j * (ℓ ^ k * c) + 1 := by
      have := hpr.one_le
      omega
    by_contra hn
    have hpq : ¬ normV v ∣ q := by
      rintro ⟨c', hc'⟩
      apply hdvd q (by omega) hqK
      rw [hc', Nat.cast_mul]
      exact v.asIdeal.mul_mem_right _ hpv
    have hq0 : (q : ZMod (normV v)) ≠ 0 := fun h => hpq ((ZMod.natCast_eq_zero_iff _ _).1 h)
    have hm := ZMod.orderOf_dvd_card_sub_one hq0
    have hm0 : orderOf (q : ZMod (normV v)) ≠ 0 :=
      (Nat.pos_of_dvd_of_pos hm (by have := hpr.two_le; omega)).ne'
    have hmt := op_arith hℓ (hpt ▸ hm) hm0 (Dvd.intro _ rfl) hn
    have hqt : (q : ZMod (normV v)) ^ (ℓ ^ k * c) = 1 := orderOf_dvd_iff_pow_eq_one.1 hmt
    have hqt' : ((normV v : ℕ) : ℤ) ∣ (q : ℤ) ^ (ℓ ^ k * c) - 1 := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [hqt, sub_self]
    have hvy := op_val_root B0 (hℓ0 j).ne' hqv hy
    have hfrob : B0.valuation (σ y - y ^ (ℓ ^ j * (ℓ ^ k * c) + 1)) < 1 := by
      have := hφ.2 y hvy.le
      rw [hφX y (Set.mem_insert_of_mem _ rfl)] at this
      rwa [← hpt']
    exact hσy (op_val B0 hpval (by exact hnv _ (hℓ0 j) hjK) (hℓ0 j).ne' hqv hy
      (by rw [← map_pow, hy, map_natCast]) hfrob hqt')
  · intro A hA h hhA z
    have hAv : IsPlaceOver A v := op_isPlaceOver A v _ hpr hpv hA
    obtain ⟨s, hs⟩ := exists_smul_eq_of_isPlaceOver hB0 hAv
    let h' : G ℚ Ω := AlgEquiv.ofRingEquiv (f := h) (fun r => by simp)
    have hDecA : h' ∈ Dec (F := ℚ) A := by
      rw [mem_Dec]
      ext w
      rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, ← hhA]
      show h' ((h'⁻¹ : G ℚ Ω) w) ∈ A ↔ w ∈ A
      rw [mul_inv_apply]
    have hk : s⁻¹ * h' * s ∈ Dec (F := ℚ) B0 := by
      rw [mem_Dec]
      show (s⁻¹ * h' * s) • B0 = B0
      rw [mul_smul, hs, mul_smul, (mem_Dec.1 hDecA), ← hs, inv_smul_smul]
    have h1 := hU0n.conj_mem _ (hDec hk) s
    have h2 : s * (s⁻¹ * h' * s) * s⁻¹ = h' := by group
    rw [h2] at h1
    have hfixb : ∀ i, h (algebraMap E Ω (Module.finBasis ℚ E i)) = algebraMap E Ω (Module.finBasis ℚ E i) :=
      fun i => (IntermediateField.mem_fixingSubgroup_iff L h').1 (hU0U h1) _
        (IntermediateField.subset_adjoin ℚ X ⟨i, rfl⟩)
    exact op_ringHom_eq ((h : Ω →+* Ω).comp (algebraMap E Ω)) (algebraMap E Ω) hfixb z
