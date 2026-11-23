import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.Published.PoitouTate.Model

theorem exists_containsAbove (F : Type) [Field F] [NumberField F] (l : ℕ) [hl : Fact l.Prime] :
    ∃ S : Finset (HeightOneSpectrum (𝓞 F)), ContainsAbove S l := by
  have h0 : Ideal.span {((l : ℕ) : 𝓞 F)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact Nat.cast_ne_zero.mpr hl.out.ne_zero
  refine ⟨(Ideal.finite_factors h0).toFinset, fun v hv => ?_⟩
  rw [Set.Finite.mem_toFinset]
  exact Ideal.dvd_span_singleton.2 hv

theorem exists_data (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (l : ℕ) [hl : Fact l.Prime] (r : ℕ) :
    ∃ ζ : Ω, IsPrimitiveRoot ζ (l ^ r) ∧
    ∃ S : Finset (HeightOneSpectrum (𝓞 F)), ContainsAbove S l ∧
    ∃ Av : S → ValuationSubring Ω, (∀ v, IsPlaceOver (Av v) v.1) ∧
    ∃ μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ,
      μ.comp (toGS Ω _) = cycMod F Ω l r ∧ ContAction (charRep μ) := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  have : NeZero ((l : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr hl.out.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ r)
  obtain ⟨S, hS⟩ := exists_containsAbove F l
  obtain ⟨μ, hμ⟩ := exists_lift_cycMod (Ω := Ω) (r := r) hS
  exact ⟨ζ, hζ, S, hS, fun v => placeOf Ω v.1, fun v => isPlaceOver_placeOf Ω v.1, μ, hμ,
    contAction_charRep hμ⟩

abbrev Qi : Type := CyclotomicField 4 ℚ

instance : IsTotallyComplex Qi :=
  haveI : IsCyclotomicExtension {4} ℚ Qi := CyclotomicField.isCyclotomicExtension 4 ℚ
  IsCyclotomicExtension.Rat.isTotallyComplex (n := 4) Qi (by norm_num)

theorem card_H2_gaussian_field (h : PoitouTateTotallyComplex) (v : HeightOneSpectrum (𝓞 Qi)) :
    Nat.card (H2 (muLoc Qi 2 2 (placeOf (AlgebraicClosure Qi) v))) = 4 := by
  obtain ⟨ζ, hζ, -⟩ := exists_data Qi (AlgebraicClosure Qi) 2 2
  obtain ⟨inv, hinv, -⟩ := h Qi (AlgebraicClosure Qi) 2 2 (by norm_num) ζ hζ
  rw [Nat.card_eq_of_bijective _ (hinv.1 _ v (isPlaceOver_placeOf _ v)).1]
  simp

theorem exists_kummer {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] {l : ℕ} [hl : Fact l.Prime] {r : ℕ} {ζ : Ω} (hζ : IsPrimitiveRoot ζ (l ^ r))
    (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F))
    (χ : Dec (F := F) A → ZMod (l ^ r)) (hχ : ∀ g h, χ (g * h) = χ g + χ h) (hc : Continuous χ) :
    ∃ (ϖ : 𝓞 F) (y : Ω) (κ : Dec (F := F) A → ZMod (l ^ r)) (z : Z2 (muLoc F l r A)),
      ϖ ∈ v.asIdeal ∧ ϖ ∉ v.asIdeal ^ 2 ∧ y ^ (l ^ r) = algebraMap F Ω (ϖ : F) ∧
      (∀ g : Dec (F := F) A, (g : G F Ω) y = ζ ^ (κ g).val * y) ∧
      ∀ g h, z.1 (g, h) = κ g * χ h := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  have : NeZero ((l : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr hl.out.ne_zero⟩
  have hN : 0 < l ^ r := pow_pos hl.out.pos r
  have : NeZero (l ^ r) := ⟨hN.ne'⟩
  obtain ⟨ϖ, h1, h2⟩ := Ideal.exists_mem_pow_notMem_pow_succ v.asIdeal v.ne_bot v.isPrime.ne_top 1
  rw [pow_one] at h1
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap F Ω (ϖ : F)) hN
  have hϖ : (ϖ : F) ≠ 0 := fun e => h2 (by
    have : ϖ = 0 := by exact_mod_cast e
    rw [this]; exact zero_mem _)
  have hy0 : y ≠ 0 := fun e => hϖ (by
    rw [e, zero_pow hN.ne'] at hy
    exact (map_eq_zero _).1 hy.symm)
  have inj : ∀ a b : ZMod (l ^ r), ζ ^ a.val = ζ ^ b.val → a = b := fun a b e =>
    ZMod.val_injective _ (hζ.pow_inj (ZMod.val_lt a) (ZMod.val_lt b) e)
  have hval : ∀ n : ℕ, ζ ^ (n : ZMod (l ^ r)).val = ζ ^ n := fun n => by
    rw [ZMod.val_natCast]
    conv_rhs => rw [← Nat.mod_add_div n (l ^ r), pow_add, pow_mul, hζ.pow_eq_one, one_pow, mul_one]
  have ex : ∀ g : G F Ω, ∃ k : ZMod (l ^ r), g y = ζ ^ k.val * y := fun g => by
    have e : (g y / y) ^ (l ^ r) = 1 := by
      rw [div_pow, ← map_pow, hy, AlgEquiv.commutes, div_self]
      rw [← hy]; exact pow_ne_zero _ hy0
    obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one e
    exact ⟨i, by rw [hval, hi, div_mul_cancel₀ _ hy0]⟩
  choose κ hκ using ex
  have hcyc : ∀ g : G F Ω, g ζ = ζ ^ ((cycMod F Ω l r g : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)).val :=
    fun g => cyclotomicCharacter.spec (L := Ω) l (MulSemiringAction.toRingAut (G F Ω) Ω g) ζ
      hζ.pow_eq_one
  have hmul : ∀ g h : G F Ω, κ (g * h) = κ g + (cycMod F Ω l r g : ZMod (l ^ r)) * κ h := by
    intro g h
    apply inj
    apply mul_right_cancel₀ hy0
    rw [← hκ, AlgEquiv.mul_apply, hκ h, map_mul, map_pow, hκ g, hcyc, ← pow_mul, ← mul_assoc,
      ← pow_add, ← hval (_ + _)]
    congr 3
    push_cast
    simp only [ZMod.natCast_val, ZMod.cast_id', id]
    ring
  have hκc : Continuous κ := by
    refine (IsLocallyConstant.iff_eventually_eq κ).2 (fun g => ?_) |>.continuous
    have ho : IsOpen {σ : G F Ω | σ y = g y} := by
      have h0 : IsOpen ((MulAction.stabilizer (G F Ω) y : Subgroup (G F Ω)) : Set (G F Ω)) :=
        stabilizer_isOpen_of_isIntegral y
      have := h0.preimage (continuous_const_mul g⁻¹)
      convert this using 1
      ext σ
      simp only [Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe, MulAction.mem_stabilizer_iff,
        mul_smul, inv_smul_eq_iff]
      rfl
    filter_upwards [ho.mem_nhds rfl] with σ hσ
    apply inj
    apply mul_right_cancel₀ hy0
    rw [← hκ, ← hκ]; exact hσ
  refine ⟨ϖ, y, fun g => κ g, ⟨fun p => κ p.1 * χ p.2,
    ((hκc.comp continuous_subtype_val).comp continuous_fst).mul (hc.comp continuous_snd),
    fun g h k => ?_⟩, h1, h2, hy, fun g => hκ g, fun _ _ => rfl⟩
  show (cycMod F Ω l r g : ZMod (l ^ r)) * (κ h * χ k) - κ ((g : G F Ω) * h) * χ k
    + κ g * χ (h * k) - κ g * χ h = 0
  rw [hmul, hχ]; ring

theorem exists_pow_card {k K : Type} [Field k] [Fintype k] [Field K] [Algebra k K]
    (σ : K →ₐ[k] K) (x : K) (hx : IsIntegral k x) : ∃ i, σ x = x ^ (Fintype.card k ^ i) := by
  let L := IntermediateField.adjoin k ({x} : Set K)
  haveI : FiniteDimensional k L := IntermediateField.adjoin.finiteDimensional hx
  haveI : Finite L := Module.finite_of_finite k
  haveI : IsGalois k L := inferInstance
  obtain ⟨i, hi⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow k L).2
    (σ.restrictNormal' L)
  refine ⟨i.1, ?_⟩
  have e := σ.restrictNormal_commutes L ⟨x, IntermediateField.mem_adjoin_simple_self k x⟩
  have e2 : σ.restrictNormal L ⟨x, IntermediateField.mem_adjoin_simple_self k x⟩ =
      (σ.restrictNormal' L) ⟨x, IntermediateField.mem_adjoin_simple_self k x⟩ := rfl
  rw [e2, ← hi] at e
  simp only [AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate, map_pow] at e
  exact e.symm

theorem exists_pow_normV {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 F)} (hA : IsPlaceOver A v)
    (g : Dec (F := F) A) {N : ℕ} (hN : N ≠ 0) {ξ : Ω} (hξ : ξ ^ N = 1) :
    ∃ i, A.valuation ((g : G F Ω) ξ - ξ ^ (normV v ^ i)) < 1 := by
  have hmem : ∀ x : 𝓞 F, algebraMap F Ω (x : F) ∈ A := fun x => by
    have h : IsIntegral ℤ (algebraMap F Ω (x : F)) := x.isIntegral_coe.map (algebraMap F Ω).toIntAlgHom
    have h' : IsIntegral A (algebraMap F Ω (x : F)) := h.tower_top
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h'
    rw [← hy]; exact y.2
  let f : 𝓞 F →+* A := ((algebraMap F Ω).comp (algebraMap (𝓞 F) F)).codRestrict A.toSubring hmem
  haveI := v.isMaximal
  letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field _
  haveI : Finite (𝓞 F ⧸ v.asIdeal) := v.asIdeal.finiteQuotientOfFreeOfNeBot v.ne_bot
  letI : Fintype (𝓞 F ⧸ v.asIdeal) := Fintype.ofFinite _
  letI : Algebra (𝓞 F ⧸ v.asIdeal) (IsLocalRing.ResidueField A) :=
    (Ideal.Quotient.lift v.asIdeal ((IsLocalRing.residue A).comp f) fun a ha => by
      rw [RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
      exact (hA a).2 ha).toAlgebra
  let g' : A.decompositionSubgroup F := g
  let σ : IsLocalRing.ResidueField A →ₐ[𝓞 F ⧸ v.asIdeal] IsLocalRing.ResidueField A :=
    { MulSemiringAction.toRingHom (A.decompositionSubgroup F) (IsLocalRing.ResidueField A) g' with
      commutes' := fun a => by
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
        show g' • IsLocalRing.residue A (f a) = IsLocalRing.residue A (f a)
        rw [← IsLocalRing.ResidueField.residue_smul]
        congr 1
        exact Subtype.ext ((g : G F Ω).commutes _) }
  have hξA : ξ ∈ A := (A.valuation_le_one_iff ξ).1 (valuation_eq_one_of_pow_eq_one A hN hξ).le
  have hp : IsLocalRing.residue A ⟨ξ, hξA⟩ ^ N = 1 := by
    rw [← map_pow, ← map_one (IsLocalRing.residue A)]
    congr 1
    exact Subtype.ext hξ
  obtain ⟨i, hi⟩ := exists_pow_card σ (IsLocalRing.residue A ⟨ξ, hξA⟩)
    (IsIntegral.of_pow (Nat.pos_of_ne_zero hN) (by rw [hp]; exact isIntegral_one))
  refine ⟨i, ?_⟩
  have hi' : IsLocalRing.residue A (g' • ⟨ξ, hξA⟩ - ⟨ξ, hξA⟩ ^ (normV v ^ i)) = 0 := by
    rw [map_sub, map_pow, IsLocalRing.ResidueField.residue_smul, sub_eq_zero]
    have : normV v = Fintype.card (𝓞 F ⧸ v.asIdeal) := Nat.card_eq_fintype_card
    rw [this]; exact hi
  rw [IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff] at hi'
  exact hi'

theorem exists_unramified {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 F)}
    (hA : IsPlaceOver A v) {n : ℕ} (hn : 2 ≤ n) :
    ∃ χ : Dec (F := F) A → ZMod n, (∀ g h, χ (g * h) = χ g + χ h) ∧ Continuous χ ∧
      (∀ g : Dec (F := F) A, (g : G F Ω) ∈ Ine (F := F) A → χ g = 0) ∧
      ∀ g : Dec (F := F) A, IsFrob (F := F) A (normV v) (g : G F Ω) → χ g = 1 := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  have : NeZero n := ⟨by omega⟩
  haveI : Finite (𝓞 F ⧸ v.asIdeal) := v.asIdeal.finiteQuotientOfFreeOfNeBot v.ne_bot
  haveI : Nontrivial (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.nontrivial_iff.2 v.isPrime.ne_top
  set q := normV v with hq
  have hq2 : 2 ≤ q := Finite.one_lt_card (α := 𝓞 F ⧸ v.asIdeal)
  have hqv : A.valuation (q : Ω) < 1 := by
    have : ((q : ℕ) : 𝓞 F) ∈ v.asIdeal := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
      letI : Fintype (𝓞 F ⧸ v.asIdeal) := Fintype.ofFinite _
      have : q = Fintype.card (𝓞 F ⧸ v.asIdeal) := Nat.card_eq_fintype_card
      rw [this]; exact Nat.cast_card_eq_zero _
    simpa using (hA _).2 this
  have hlt : ∀ i < n, q ^ i < q ^ n - 1 := fun i hi => by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have h1 : q ^ i ≤ q ^ m := Nat.pow_le_pow_right (by omega) (by omega)
    have h2 : q ^ 1 ≤ q ^ m := Nat.pow_le_pow_right (by omega) (by omega)
    have h3 : q ^ m * 2 ≤ q ^ (m + 1) := by rw [pow_succ]; exact Nat.mul_le_mul_left _ hq2
    rw [pow_one] at h2; omega
  obtain ⟨N, hN⟩ : ∃ N, q ^ n = N + 1 := ⟨q ^ n - 1, by have := hlt 0 (by omega); omega⟩
  have hN0 : N ≠ 0 := by have := hlt 0 (by omega); omega
  have hNv : ¬ A.valuation (N : Ω) < 1 := fun h => by
    have e : (1 : Ω) = (q : Ω) ^ n - N := by
      rw [← Nat.cast_pow, hN]; push_cast; ring
    have h2 : A.valuation ((q : Ω) ^ n) < 1 := by
      rw [map_pow]; exact pow_lt_one₀ zero_le hqv (by omega)
    have := Valuation.map_sub_lt _ h2 h
    rw [← e, map_one] at this
    exact lt_irrefl _ this
  have : NeZero N := ⟨hN0⟩
  have : NeZero ((N : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr hN0⟩
  obtain ⟨ξ, hξ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω N
  have hpw : ∀ m : ℕ, (ξ ^ m) ^ N = 1 := fun m => by
    rw [← pow_mul, mul_comm, pow_mul, hξ.pow_eq_one, one_pow]
  have hg : ∀ g : G F Ω, g ξ ^ N = 1 := fun g => by rw [← map_pow, hξ.pow_eq_one, map_one]
  have hper : ∀ a : ℕ, ξ ^ (q ^ (n * a)) = ξ := fun a => by
    induction a with
    | zero => simp
    | succ a ih => rw [Nat.mul_succ, pow_add, pow_mul, ih, hN, pow_succ, hξ.pow_eq_one, one_mul]
  have hval : ∀ m : ℕ, ξ ^ (q ^ (m : ZMod n).val) = ξ ^ (q ^ m) := fun m => by
    rw [ZMod.val_natCast]
    conv_rhs => rw [← Nat.div_add_mod m n, pow_add, pow_mul, hper]
  have inj : ∀ a b : ZMod n, ξ ^ (q ^ a.val) = ξ ^ (q ^ b.val) → a = b := fun a b e => by
    have ha := hlt _ (ZMod.val_lt a)
    have hb := hlt _ (ZMod.val_lt b)
    exact ZMod.val_injective _ (Nat.pow_right_injective hq2
      (hξ.pow_inj (show q ^ a.val < N by omega) (show q ^ b.val < N by omega) e))
  have ex : ∀ g : Dec (F := F) A, ∃ k : ZMod n, (g : G F Ω) ξ = ξ ^ (q ^ k.val) := fun g => by
    obtain ⟨i, hi⟩ := exists_pow_normV hA g hN0 hξ.pow_eq_one
    exact ⟨i, by rw [hval]; exact eq_of_pow_eq_one A hNv (hg _) (hpw _) hi⟩
  choose χ hχ using ex
  have hξA : A.valuation ξ ≤ 1 := (valuation_eq_one_of_pow_eq_one A hN0 hξ.pow_eq_one).le
  refine ⟨χ, fun g h => inj _ _ ?_, ?_, fun g hg' => inj _ _ ?_, fun g hg' => inj _ _ ?_⟩
  · rw [← hχ, Subgroup.coe_mul, AlgEquiv.mul_apply, hχ h, map_pow, hχ g, ← pow_mul, ← pow_add,
      ← hval (_ + _)]
    congr 3
    push_cast
    simp only [ZMod.natCast_val, ZMod.cast_id', id]
  · refine (IsLocallyConstant.iff_eventually_eq χ).2 (fun g => ?_) |>.continuous
    have ho := (isOpen_setOf_apply (F := F) ξ (fun t => t = (g : G F Ω) ξ)).preimage
      (continuous_subtype_val (p := fun σ => σ ∈ Dec (F := F) A))
    filter_upwards [ho.mem_nhds (x := g) rfl] with σ hσ
    apply inj
    rw [← hχ, ← hχ]; exact hσ
  · rw [← hχ, ZMod.val_zero, pow_zero, pow_one]
    exact eq_of_pow_eq_one A hNv (hg _) hξ.pow_eq_one (hg'.2 ξ hξA)
  · rw [← hχ, ← Nat.cast_one, hval, pow_one]
    exact eq_of_pow_eq_one A hNv (hg _) (hpw _) (hg'.2 ξ hξA)

theorem exists_eq_one {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] {l : ℕ} [hl : Fact l.Prime] {r : ℕ} (hr : 0 < r) {ζ : Ω}
    (hζ : IsPrimitiveRoot ζ (l ^ r)) {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 F)}
    (hA : IsPlaceOver A v) :
    ∃ x : H2 (muLoc F l r A), ∀ inv, IsNormalised ζ A v inv → inv x = 1 := by
  obtain ⟨χ, h1, h2, h3, h4⟩ := exists_unramified hA (n := l ^ r) (Nat.one_lt_pow hr.ne' hl.out.one_lt)
  obtain ⟨ϖ, y, κ, z, a, b, c, d, e⟩ := exists_kummer hζ A v χ h1 h2
  exact ⟨Submodule.Quotient.mk z, fun inv h => h ϖ y κ χ z a b c d h1 h3 h4 e⟩

theorem inv_unique {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] {l : ℕ} [hl : Fact l.Prime] {r : ℕ} (hr : 0 < r) {ζ : Ω}
    (hζ : IsPrimitiveRoot ζ (l ^ r)) {inv inv' : InvFam F Ω l r} (h : IsLocalInvariants ζ inv)
    (h' : IsLocalInvariants ζ inv') {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 F)}
    (hA : IsPlaceOver A v) : inv A = inv' A := by
  obtain ⟨x, hx⟩ := exists_eq_one hr hζ hA
  refine LinearMap.ext fun w => ?_
  have e : w = inv A w • x := (h.1 A v hA).1.1 (by
    rw [map_smul, hx _ (h.1 A v hA).2, smul_eq_mul, mul_one])
  conv_rhs => rw [e, map_smul, hx _ (h'.1 A v hA).2, smul_eq_mul, mul_one]

end GlobalTheory.Published.PoitouTate.Model
