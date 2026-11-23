import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsGoodPoly
set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.CompanionTheory.TraceJac

section dvr
variable {R F L : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field F] [Field L]
  [Algebra R F] [IsFractionRing R F] [Algebra F L] [Algebra R L] [IsScalarTower R F L]
  [FiniteDimensional F L] [Algebra.IsSeparable F L]

include F in
theorem faithful_integralClosure : FaithfulSMul R (integralClosure R L) := by
  rw [faithfulSMul_iff_algebraMap_injective]
  have h1 : Function.Injective (algebraMap R L) := by
    rw [IsScalarTower.algebraMap_eq R F L]
    exact (algebraMap F L).injective.comp (IsFractionRing.injective R F)
  intro a b hab
  apply h1
  have h2 := congrArg (fun x : integralClosure R L => (x : L)) hab
  simpa using h2

include F in
theorem trace_radical (π : R) (hπ : Irreducible π) (y z : integralClosure R L) (n : ℕ)
    (h : y ^ n = algebraMap R _ π * z) :
    ∃ r : R, algebraMap R F (π * r) = Algebra.trace F L (y : L) := by
  classical
  have h1 : Function.Injective (algebraMap R L) := by
    rw [IsScalarTower.algebraMap_eq R F L]
    exact (algebraMap F L).injective.comp (IsFractionRing.injective R F)
  haveI : FaithfulSMul R L := by
    rw [faithfulSMul_iff_algebraMap_injective]
    exact h1
  haveI : Module.Finite R (integralClosure R L) := IsIntegralClosure.finite R F L (integralClosure R L)
  haveI : Module.Free R (integralClosure R L) := IsIntegralClosure.module_free R F L (integralClosure R L)
  haveI : IsLocalization (Algebra.algebraMapSubmonoid (integralClosure R L) (nonZeroDivisors R)) L :=
    IsIntegralClosure.isLocalization R F L (integralClosure R L)
  have htr : Algebra.trace F L (y : L) = algebraMap R F (Algebra.trace R (integralClosure R L) y) :=
    Algebra.trace_localization (Rₘ := F) (Sₘ := L) R (nonZeroDivisors R) y
  have hM : Algebra.leftMulMatrix (Module.Free.chooseBasis R (integralClosure R L)) y ^ n =
      π • Algebra.leftMulMatrix (Module.Free.chooseBasis R (integralClosure R L)) z := by
    rw [← map_pow, h, map_mul, AlgHom.commutes, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
  have hπm : IsLocalRing.residue R π = 0 :=
    (IsLocalRing.residue_eq_zero_iff π).mpr (mem_nonunits_iff.mpr hπ.not_isUnit)
  have hnil : IsNilpotent ((Algebra.leftMulMatrix (Module.Free.chooseBasis R (integralClosure R L)) y).map
      (IsLocalRing.residue R)) := by
    refine ⟨n, ?_⟩
    have h2 := map_pow (IsLocalRing.residue R).mapMatrix
      (Algebra.leftMulMatrix (Module.Free.chooseBasis R (integralClosure R L)) y) n
    simp only [RingHom.mapMatrix_apply] at h2
    rw [← h2, hM]
    ext i j
    simp [hπm]
  have htrace0 : IsLocalRing.residue R
      (Matrix.trace (Algebra.leftMulMatrix (Module.Free.chooseBasis R (integralClosure R L)) y)) = 0 := by
    have h2 := Matrix.isNilpotent_trace_of_isNilpotent hnil
    have h3 : Matrix.trace ((Algebra.leftMulMatrix (Module.Free.chooseBasis R (integralClosure R L)) y).map
        (IsLocalRing.residue R)) = IsLocalRing.residue R
          (Matrix.trace (Algebra.leftMulMatrix (Module.Free.chooseBasis R (integralClosure R L)) y)) := by
      simp [Matrix.trace, map_sum]
    rw [← h3]
    exact h2.eq_zero
  have hmem := (IsLocalRing.residue_eq_zero_iff _).mp htrace0
  rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at hmem
  obtain ⟨r, hr⟩ := hmem
  refine ⟨r, ?_⟩
  rw [htr, Algebra.trace_eq_matrix_trace (Module.Free.chooseBasis R (integralClosure R L)), ← hr]

theorem mem_prime (π : R) (hπ : Irreducible π) (P : Ideal (integralClosure R L)) [P.IsPrime] (hP : P ≠ ⊥) :
    algebraMap R _ π ∈ P := by
  have hne : P.comap (algebraMap R (integralClosure R L)) ≠ ⊥ := by
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP
    exact Ideal.comap_ne_bot_of_integral_mem hx0 hx (Algebra.IsIntegral.isIntegral x)
  have hmax : (P.comap (algebraMap R (integralClosure R L))).IsMaximal :=
    Ideal.IsPrime.isMaximal inferInstance hne
  have heq := IsLocalRing.eq_maximalIdeal hmax
  have hπm : π ∈ IsLocalRing.maximalIdeal R :=
    (IsLocalRing.mem_maximalIdeal π).mpr (mem_nonunits_iff.mpr hπ.not_isUnit)
  rw [← heq] at hπm
  exact hπm

include F in
theorem isPID_integralClosure : IsPrincipalIdealRing (integralClosure R L) := by
  classical
  haveI : IsDedekindDomain (integralClosure R L) :=
    IsIntegralClosure.isDedekindDomain R F L (integralClosure R L)
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  haveI := faithful_integralClosure (R := R) (F := F) (L := L)
  have hπ0 : algebraMap R (integralClosure R L) π ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective R (integralClosure R L))).mpr hπ.ne_zero
  apply IsPrincipalIdealRing.of_finite_primes
  have hfin := Ideal.finite_factors (R := integralClosure R L)
    (I := Ideal.span {algebraMap R (integralClosure R L) π}) (Ideal.span_singleton_eq_bot.not.mpr hπ0)
  refine ((hfin.image (fun v => v.asIdeal)).insert ⊥).subset ?_
  intro P hP
  by_cases hb : P = ⊥
  · exact Set.mem_insert_iff.mpr (Or.inl hb)
  · refine Set.mem_insert_iff.mpr (Or.inr ?_)
    haveI : P.IsPrime := hP
    refine ⟨⟨P, hP, hb⟩, ?_, rfl⟩
    show P ∣ Ideal.span {algebraMap R (integralClosure R L) π}
    rw [Ideal.dvd_span_singleton]
    exact mem_prime π hπ P hb

end dvr
end GlobalTheory.CompanionTheory.TraceJac

namespace GlobalTheory.CompanionTheory.TraceJac

theorem exists_den {R S L : Type*} [CommRing R] [CommRing S] [IsDomain S] [Field L] [Algebra R S]
    [Algebra S L] [IsFractionRing S L] [Algebra R L] [IsScalarTower R S L] [Module.Finite R S]
    (E : Derivation ℤ L L) (hE : ∀ r : R, ∃ r' : R, E (algebraMap R L r) = algebraMap R L r') :
    ∃ δ : S, δ ≠ 0 ∧ ∀ x : S, ∃ y : S,
      algebraMap S L δ * E (algebraMap S L x) = algebraMap S L y := by
  classical
  obtain ⟨m, s, hs⟩ := Module.Finite.exists_fin (R := R) (M := S)
  have hfrac : ∀ i, ∃ a d : S, d ≠ 0 ∧ E (algebraMap S L (s i)) = algebraMap S L a / algebraMap S L d := by
    intro i
    obtain ⟨a, d, hd, h⟩ := IsFractionRing.div_surjective (A := S) (E (algebraMap S L (s i)))
    exact ⟨a, d, nonZeroDivisors.ne_zero hd, h.symm⟩
  choose a d hd0 hd using hfrac
  refine ⟨∏ i, d i, Finset.prod_ne_zero_iff.mpr (fun i _ => hd0 i), fun x => ?_⟩
  have hx : x ∈ Submodule.span R (Set.range s) := hs ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    refine ⟨(∏ j ∈ Finset.univ.erase i, d j) * a i, ?_⟩
    have hdi : algebraMap S L (d i) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective S L)).mpr (hd0 i)
    rw [hd i, ← Finset.mul_prod_erase Finset.univ d (Finset.mem_univ i), map_mul, map_mul]
    field_simp
  | zero => exact ⟨0, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨y', hy'⟩ := hy
    obtain ⟨z', hz'⟩ := hz
    exact ⟨y' + z', by rw [map_add, map_add, mul_add, hy', hz', map_add]⟩
  | smul r y _ hy =>
    obtain ⟨y', hy'⟩ := hy
    obtain ⟨r', hr'⟩ := hE r
    refine ⟨algebraMap R S r * y' + y * (∏ i, d i) * algebraMap R S r', ?_⟩
    have e1 : algebraMap S L (r • y) = algebraMap R L r * algebraMap S L y := by
      rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply]
    rw [e1, Derivation.leibniz, hr', smul_eq_mul, smul_eq_mul]
    simp only [map_add, map_mul, ← IsScalarTower.algebraMap_apply, ← hy']
    ring

section dvr2
variable {R F L : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field F] [Field L]
  [Algebra R F] [IsFractionRing R F] [Algebra F L] [Algebra R L] [IsScalarTower R F L]
  [FiniteDimensional F L] [Algebra.IsSeparable F L]

open IsDedekindDomain in
include F in
theorem valuation_bounds (hnat : ∀ n : ℕ, n ≠ 0 → IsUnit (n : R)) (π : R) (hπ : Irreducible π)
    [IsDedekindDomain (integralClosure R L)] [IsFractionRing (integralClosure R L) L]
    [IsPrincipalIdealRing (integralClosure R L)]
    (P : HeightOneSpectrum (integralClosure R L)) (E' : Derivation ℤ L L)
    (I : Ideal (integralClosure R L))
    (hI : ∀ r : R, ∃ s ∈ I, E' (algebraMap R L r) = algebraMap (integralClosure R L) L s)
    (hR' : ∀ r : R, ∃ r' : R, E' (algebraMap R L r) = algebraMap R L r')
    (hπ' : ∃ s : integralClosure R L, E' (algebraMap R L π) =
      algebraMap (integralClosure R L) L (algebraMap R _ π * s)) :
    (∀ x : integralClosure R L, P.valuation L (E' (algebraMap _ L x)) ≤ 1) ∧
    (I ≤ P.asIdeal → ∀ x : integralClosure R L, P.valuation L (E' (algebraMap _ L x)) < 1) := by
  haveI := faithful_integralClosure (R := R) (F := F) (L := L)
  haveI : Module.Finite R (integralClosure R L) := IsIntegralClosure.finite R F L (integralClosure R L)
  obtain ⟨ϖ, hϖ⟩ := (IsPrincipalIdealRing.principal P.asIdeal).principal
  have hπ0 : algebraMap R (integralClosure R L) π ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective R (integralClosure R L))).mpr hπ.ne_zero
  have hmem := mem_prime π hπ P.asIdeal P.ne_bot
  have hdiv : ϖ ∣ algebraMap R (integralClosure R L) π := by
    rw [hϖ] at hmem
    exact Ideal.mem_span_singleton.mp hmem
  have hπ'' : ∃ s, E' (algebraMap (integralClosure R L) L (algebraMap R (integralClosure R L) π)) =
      algebraMap (integralClosure R L) L (algebraMap R (integralClosure R L) π * s) := by
    rw [← IsScalarTower.algebraMap_apply]
    exact hπ'
  obtain ⟨δ, hδ0, hδ⟩ := exists_den (R := R) (S := integralClosure R L) (L := L) E' hR'
  have hle : ∀ x : integralClosure R L, P.valuation L (algebraMap _ L x) ≤ 1 :=
    fun x => P.valuation_le_one x
  have hlt : ∀ x : integralClosure R L, P.valuation L (algebraMap _ L x) < 1 ↔ ϖ ∣ x := by
    intro x
    rw [P.valuation_lt_one_iff_mem, hϖ]
    exact Ideal.mem_span_singleton
  have hc := core hnat (P.valuation L) ϖ hle hlt E' I hI _ hπ0 hdiv hπ'' δ hδ0 hδ
  refine ⟨hc.1, fun hIP => hc.2.2 (by rw [hϖ] at hIP; exact hIP)⟩

end dvr2
end GlobalTheory.CompanionTheory.TraceJac

namespace GlobalTheory.CompanionTheory.TraceJac

section dvr3
variable {R F L : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field F] [Field L]
  [Algebra R F] [IsFractionRing R F] [Algebra F L] [Algebra R L] [IsScalarTower R F L]
  [FiniteDimensional F L] [Algebra.IsSeparable F L]

private theorem det_rowop_lemma {n K : Type*} [Fintype n] [DecidableEq n] [CommRing K]
    (A : Matrix n n K) (j : n) (c : n → K) :
    (Matrix.of fun k l => if k = j then A k l else A k l - c k * A j l).det = A.det := by
  have key : ∀ s : Finset n, j ∉ s →
      (Matrix.of fun k l => if k ∈ s then A k l - c k * A j l else A k l).det = A.det := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _
      congr 1
    | insert k s hks ih =>
      intro hj
      have hjk : k ≠ j := fun h => hj (h ▸ Finset.mem_insert_self k s)
      have hjs : j ∉ s := fun h => hj (Finset.mem_insert_of_mem h)
      have heq : (Matrix.of fun k' l => if k' ∈ insert k s then A k' l - c k' * A j l else A k' l) =
          (Matrix.of fun k' l => if k' ∈ s then A k' l - c k' * A j l else A k' l).updateRow k
            ((Matrix.of fun k' l => if k' ∈ s then A k' l - c k' * A j l else A k' l) k +
              (-c k) • (Matrix.of fun k' l => if k' ∈ s then A k' l - c k' * A j l else A k' l) j) := by
        ext k' l
        by_cases hk' : k' = k
        · subst hk'
          simp [hks, hjs, sub_eq_add_neg, mul_comm]
        · simp [Matrix.updateRow_ne hk', hk']
      rw [heq, Matrix.det_updateRow_add_smul_self _ hjk, ih hjs]
  have h1 := key (Finset.univ.erase j) (Finset.notMem_erase j _)
  rw [← h1]
  congr 1
  ext k l
  by_cases hk : k = j
  · simp [hk]
  · simp [hk]

private theorem val_det_le_lemma_2 {n K Γ : Type*} [Fintype n] [DecidableEq n] [CommRing K]
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) (A : Matrix n n K)
    (h : ∀ k l, v (A k l) ≤ 1) : v A.det ≤ 1 := by
  rw [Matrix.det_apply]
  refine v.map_sum_le (fun σ _ => ?_)
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
  · rw [hs, one_smul, map_prod]
    exact Finset.prod_le_one' (fun i _ => h _ _)
  · rw [hs, Units.neg_smul, one_smul, Valuation.map_neg, map_prod]
    exact Finset.prod_le_one' (fun i _ => h _ _)

private theorem val_det_lt_lemma_3 {n K Γ : Type*} [Fintype n] [DecidableEq n] [CommRing K]
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) (A : Matrix n n K)
    (h : ∀ k l, v (A k l) ≤ 1) (j : n) (hj : ∀ l, v (A j l) < 1) : v A.det < 1 := by
  rw [Matrix.det_eq_sum_mul_adjugate_row A j]
  refine v.map_sum_lt one_ne_zero (fun l _ => ?_)
  rw [map_mul]
  have hadj : v (A.adjugate l j) ≤ 1 := by
    rw [Matrix.adjugate_apply]
    refine val_det_le_lemma_2 v _ (fun k m => ?_)
    by_cases hk : k = j
    · subst hk
      rw [Matrix.updateRow_self]
      by_cases hm : m = l
      · subst hm
        simp
      · simp [Pi.single_apply, hm]
    · rw [Matrix.updateRow_ne hk]
      exact h k m
  exact lt_of_le_of_lt (mul_le_of_le_one_right' hadj) (hj l)

open IsDedekindDomain in
include F in
theorem trace_jac_dvr {n : Type*} [Fintype n] [DecidableEq n]
    (hnat : ∀ m : ℕ, m ≠ 0 → IsUnit (m : R))
    (E : n → Derivation ℤ L L)
    (hR : ∀ k (r : R), ∃ r' : R, E k (algebraMap R L r) = algebraMap R L r')
    (π : R) (hπ : Irreducible π) (j : n) (u : Rˣ) (hj : E j (algebraMap R L π) = algebraMap R L u)
    (c : L) (hc : IsIntegral R c) (b : n → L) (hb : ∀ l, IsIntegral R (b l)) :
    ∃ r : R, algebraMap R F r = Algebra.trace F L (c * (Matrix.of fun k l => E k (b l)).det) := by
  classical
  haveI : IsDedekindDomain (integralClosure R L) :=
    IsIntegralClosure.isDedekindDomain R F L (integralClosure R L)
  haveI : IsFractionRing (integralClosure R L) L :=
    IsIntegralClosure.isFractionRing_of_finite_extension R F L (integralClosure R L)
  haveI : IsPrincipalIdealRing (integralClosure R L) := isPID_integralClosure (F := F)
  haveI := faithful_integralClosure (R := R) (F := F) (L := L)
  have hπS : algebraMap R (integralClosure R L) π ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective R (integralClosure R L))).mpr hπ.ne_zero
  have hsc : ∀ r : R, algebraMap R L r = algebraMap (integralClosure R L) L (algebraMap R _ r) :=
    fun r => IsScalarTower.algebraMap_apply R (integralClosure R L) L r
  choose rk hrk using fun k => hR k π
  set α : n → L := fun k => algebraMap R L (rk k * ↑u⁻¹) with hα
  have hE'π : ∀ k, (E k - α k • E j) (algebraMap R L π) = 0 := by
    intro k
    rw [Derivation.sub_apply, Derivation.smul_apply, hrk k, hj, smul_eq_mul, hα, ← map_mul, mul_assoc,
      Units.inv_mul, mul_one, sub_self]
  have hE'R : ∀ k (r : R), ∃ r' : R, (E k - α k • E j) (algebraMap R L r) = algebraMap R L r' := by
    intro k r
    obtain ⟨r1, h1⟩ := hR k r
    obtain ⟨r2, h2⟩ := hR j r
    refine ⟨r1 - rk k * ↑u⁻¹ * r2, ?_⟩
    rw [Derivation.sub_apply, Derivation.smul_apply, h1, h2, smul_eq_mul, hα, map_sub, map_mul]
  have hE''R : ∀ r : R, ∃ r' : R, (algebraMap R L π • E j) (algebraMap R L r) = algebraMap R L r' := by
    intro r
    obtain ⟨r2, h2⟩ := hR j r
    exact ⟨π * r2, by rw [Derivation.smul_apply, h2, smul_eq_mul, map_mul]⟩
  have hvb : ∀ P : IsDedekindDomain.HeightOneSpectrum (integralClosure R L),
      (∀ k, ∀ x : integralClosure R L,
        P.valuation L ((E k - α k • E j) (algebraMap (integralClosure R L) L x)) ≤ 1) ∧
      (∀ x : integralClosure R L,
        P.valuation L ((algebraMap R L π • E j) (algebraMap (integralClosure R L) L x)) < 1) := by
    intro P
    refine ⟨fun k => ?_, ?_⟩
    · refine (valuation_bounds (F := F) hnat π hπ P (E k - α k • E j) ⊤ (fun r => ?_) (hE'R k)
        ⟨0, by rw [hE'π k, mul_zero, map_zero]⟩).1
      obtain ⟨r', hr'⟩ := hE'R k r
      exact ⟨algebraMap R _ r', Submodule.mem_top, by rw [hr', hsc]⟩
    · refine (valuation_bounds (F := F) hnat π hπ P (algebraMap R L π • E j)
        (Ideal.span {algebraMap R (integralClosure R L) π}) (fun r => ?_) hE''R
        ⟨algebraMap R _ u, ?_⟩).2 ?_
      · obtain ⟨r2, h2⟩ := hR j r
        refine ⟨algebraMap R _ π * algebraMap R _ r2,
          Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _), ?_⟩
        rw [Derivation.smul_apply, h2, smul_eq_mul, map_mul, hsc, hsc]
      · rw [Derivation.smul_apply, hj, smul_eq_mul, map_mul, hsc, hsc]
      · rw [Ideal.span_singleton_le_iff_mem]
        exact mem_prime π hπ P.asIdeal P.ne_bot
  set M : Matrix n n L := Matrix.of fun k l => E k (b l) with hM
  set M2 : Matrix n n L := (Matrix.of fun k l => if k = j then M k l else M k l - α k * M j l).updateRow j
    (algebraMap R L π • M j) with hM2
  have hdet : M2.det = algebraMap R L π * M.det := by
    rw [hM2, Matrix.det_updateRow_smul, ← det_rowop_lemma M j α]
    congr 2
    ext k l
    by_cases hk : k = j
    · subst hk
      simp
    · simp [Matrix.updateRow_ne hk]
  have hent : ∀ P : IsDedekindDomain.HeightOneSpectrum (integralClosure R L), ∀ k l,
      (k = j → P.valuation L (M2 k l) < 1) ∧ P.valuation L (M2 k l) ≤ 1 := by
    intro P k l
    have hb' : b l = algebraMap (integralClosure R L) L ⟨b l, hb l⟩ := rfl
    by_cases hk : k = j
    · subst hk
      have h1 : M2 k l = (algebraMap R L π • E k) (algebraMap (integralClosure R L) L ⟨b l, hb l⟩) := by
        rw [hM2, Matrix.updateRow_self, Derivation.smul_apply]
        rfl
      have h2 := (hvb P).2 ⟨b l, hb l⟩
      rw [← h1] at h2
      exact ⟨fun _ => h2, h2.le⟩
    · have h1 : M2 k l = (E k - α k • E j) (algebraMap (integralClosure R L) L ⟨b l, hb l⟩) := by
        rw [hM2, Matrix.updateRow_ne hk, Derivation.sub_apply, Derivation.smul_apply]
        simp [hk, hM]
      have h2 := (hvb P).1 k ⟨b l, hb l⟩
      rw [← h1] at h2
      exact ⟨fun h => absurd h hk, h2⟩
  have hw : ∀ P : IsDedekindDomain.HeightOneSpectrum (integralClosure R L),
      P.valuation L (c * M2.det) < 1 := by
    intro P
    have hcS : c = algebraMap (integralClosure R L) L ⟨c, hc⟩ := rfl
    rw [map_mul]
    refine lt_of_le_of_lt (mul_le_of_le_one_left' ?_) ?_
    · rw [hcS]
      exact P.valuation_le_one _
    · exact val_det_lt_lemma_3 (P.valuation L) M2 (fun k l => (hent P k l).2) j (fun l => (hent P j l).1 rfl)
  obtain ⟨w0, hw0⟩ : c * M2.det ∈ (algebraMap (integralClosure R L) L).range :=
    IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one L _ (fun P => (hw P).le)
  have hrad : w0 ∈ (Ideal.span {algebraMap R (integralClosure R L) π}).radical := by
    rw [Ideal.radical_eq_sInf, Submodule.mem_sInf]
    rintro J ⟨hJ, hJp⟩
    have hJb : J ≠ ⊥ := by
      intro h0
      rw [h0] at hJ
      exact hπS ((Submodule.mem_bot _).mp (hJ (Ideal.mem_span_singleton_self _)))
    have h1 := hw ⟨J, hJp, hJb⟩
    rw [← hw0] at h1
    exact (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem ⟨J, hJp, hJb⟩ w0).mp h1
  obtain ⟨N, hN⟩ := hrad
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.mp hN
  obtain ⟨r, hr⟩ := trace_radical (F := F) π hπ w0 z N (by rw [← hz, mul_comm])
  refine ⟨r, ?_⟩
  have hw0' : ((w0 : integralClosure R L) : L) = algebraMap R L π * (c * M.det) := by
    rw [show ((w0 : integralClosure R L) : L) = algebraMap (integralClosure R L) L w0 from rfl, hw0, hdet]
    ring
  rw [hw0', IsScalarTower.algebraMap_apply R F L, ← smul_eq_mul, ← Algebra.smul_def,
    LinearMap.map_smul, smul_eq_mul, map_mul] at hr
  have hπF : algebraMap R F π ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R F)).mpr hπ.ne_zero
  exact mul_left_cancel₀ hπF hr

end dvr3
end GlobalTheory.CompanionTheory.TraceJac
