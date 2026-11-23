import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChebotarevDegreeOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChebotarevDegreeOneIffCheb
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.PlaceBasic

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2.AuxiliaryInertOddPrime

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]

theorem fix_root {l : ℕ} [Fact l.Prime] {s : G ℚ Ω} (hs : s ∈ (cycBar ℚ Ω l).ker) {n : ℕ} {x : Ω}
    (hx : x ^ (l ^ n) = 1) : s x = x := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have h1 : cycZ ℚ Ω l s = 1 := by
    have h := congrArg Units.val (MonoidHom.mem_ker.1 hs)
    apply Units.ext
    have hinj : Function.Injective ((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom) :=
      (algebraMap ℚ_[l] (Qbar l)).injective.comp Subtype.val_injective
    apply hinj
    simpa [cycBar] using h
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI hE : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => inferInstance
  have h2 := cyclotomicCharacter.spec l (MulSemiringAction.toRingAut (G ℚ Ω) Ω s) x hx
  have h3 : cyclotomicCharacter Ω l (MulSemiringAction.toRingAut (G ℚ Ω) Ω s) = 1 := h1
  rw [h3] at h2
  have h4 : (MulSemiringAction.toRingAut (G ℚ Ω) Ω s) x = s x := rfl
  rw [h4, Units.val_one, map_one, ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod 1 hx, pow_one] at h2
  exact h2

theorem comm_apply {l : ℕ} [Fact l.Prime] {n : ℕ} {a : Ω} (ha : ∀ g : G ℚ Ω, g a = a)
    {s t : G ℚ Ω} (hs : s ∈ (cycBar ℚ Ω l).ker) (ht : t ∈ (cycBar ℚ Ω l).ker) {y : Ω}
    (hy : y ^ (l ^ n) = a) : s (t y) = t (s y) := by
  by_cases h0 : y = 0
  · simp [h0]
  have key : ∀ g : G ℚ Ω, (g y / y) ^ (l ^ n) = 1 := fun g => by
    rw [div_pow, ← map_pow, hy, ha, ← hy]
    exact div_self (pow_ne_zero _ h0)
  obtain ⟨c, hcr, es⟩ : ∃ c : Ω, c ^ (l ^ n) = 1 ∧ s y = c * y :=
    ⟨s y / y, key s, (div_mul_cancel₀ _ h0).symm⟩
  obtain ⟨d, hdr, et⟩ : ∃ d : Ω, d ^ (l ^ n) = 1 ∧ t y = d * y :=
    ⟨t y / y, key t, (div_mul_cancel₀ _ h0).symm⟩
  rw [et, es, map_mul, map_mul, fix_root hs hdr, fix_root ht hcr, es, et]
  ring

theorem comm_fix {l : ℕ} [Fact l.Prime] {n : ℕ} {a : Ω} (ha : ∀ g : G ℚ Ω, g a = a) {σ : G ℚ Ω}
    (hσ : σ ∈ ⁅(cycBar ℚ Ω l).ker, (cycBar ℚ Ω l).ker⁆) {y : Ω} (hy : y ^ (l ^ n) = a) : σ y = y := by
  let K : Subgroup (G ℚ Ω) := ⨅ z : {z : Ω // z ^ (l ^ n) = a}, MulAction.stabilizer (G ℚ Ω) (z : Ω)
  have hK : ∀ g, g ∈ K ↔ ∀ z : Ω, z ^ (l ^ n) = a → g z = z := fun g => by
    simp only [K, Subgroup.mem_iInf, MulAction.mem_stabilizer_iff, AlgEquiv.smul_def, Subtype.forall]
  have hle : ⁅(cycBar ℚ Ω l).ker, (cycBar ℚ Ω l).ker⁆ ≤ K := by
    rw [Subgroup.commutator_le]
    intro s hs t ht
    rw [hK]
    intro z hz
    have hz' : ((t * s)⁻¹ z) ^ (l ^ n) = a := by rw [← map_pow, hz, ha]
    have e : s * t * s⁻¹ * t⁻¹ = (s * t) * (t * s)⁻¹ := by group
    rw [commutatorElement_def, e, AlgEquiv.mul_apply, AlgEquiv.mul_apply, comm_apply ha hs ht hz', ← AlgEquiv.mul_apply,
      ← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
  exact (hK σ).1 (hle hσ) y hy

theorem isOpen_stab (x : Ω) : IsOpen {τ : G ℚ Ω | τ x = x} := by
  have : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  have hx : IsIntegral ℚ x := (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {x}) := IntermediateField.adjoin.finiteDimensional hx
  have h := IntermediateField.fixingSubgroup_isOpen (IntermediateField.adjoin ℚ {x})
  have hle : (IntermediateField.adjoin ℚ {x}).fixingSubgroup ≤ MulAction.stabilizer (G ℚ Ω) x := fun g hg => by
    rw [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def]
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg x (IntermediateField.mem_adjoin_simple_self ℚ x)
  have e : {τ : G ℚ Ω | τ x = x} = (MulAction.stabilizer (G ℚ Ω) x : Set (G ℚ Ω)) := by
    ext τ; simp [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def]
  rw [e]
  exact Subgroup.isOpen_mono hle h

theorem root_mod {B : ValuationSubring Ω} {p m N : ℕ} (hp : p.Prime) (hpB : B.valuation (p : Ω) < 1) (hm : m ≠ 0)
    {α : Ω} (hα : α ^ m = (N : Ω)) (hfr : B.valuation α ≤ 1 → B.valuation (α - α ^ p) < 1) :
    ∃ x : ZMod p, x ^ m = (N : ZMod p) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hαle : B.valuation α ≤ 1 := by
    have h1 : B.valuation α ^ m ≤ 1 := by
      rw [← map_pow, hα]; exact (B.valuation_le_one_iff _).2 (natCast_mem B N)
    exact (pow_le_one_iff hm).1 h1
  have hαB : α ∈ B := (B.valuation_le_one_iff α).1 hαle
  let a : B := ⟨α, hαB⟩
  have hmax : ∀ b : B, B.valuation (b : Ω) < 1 → IsLocalRing.residue B b = 0 := fun b hb =>
    (IsLocalRing.residue_eq_zero_iff b).2 ((B.valuation_lt_one_iff b).2 hb)
  have hpk : ((p : ℕ) : IsLocalRing.ResidueField B) = 0 := by
    have := hmax (p : B) (by simpa using hpB)
    simpa using this
  haveI : CharP (IsLocalRing.ResidueField B) p := (CharP.charP_iff_prime_eq_zero hp).2 hpk
  let φ : ZMod p →+* IsLocalRing.ResidueField B := ZMod.castHom (dvd_refl p) _
  have hφ : Function.Injective φ := φ.injective
  have hr : IsLocalRing.residue B a ^ p = IsLocalRing.residue B a := by
    have := hmax (a - a ^ p) (by simpa [a] using hfr hαle)
    rw [map_sub, map_pow, sub_eq_zero] at this
    exact this.symm
  have hP : (Polynomial.X ^ p - Polynomial.X : Polynomial (IsLocalRing.ResidueField B)) ≠ 0 :=
    FiniteField.X_pow_card_sub_X_ne_zero _ hp.one_lt
  have hsub : Finset.univ.image φ ⊆
      (Polynomial.X ^ p - Polynomial.X : Polynomial (IsLocalRing.ResidueField B)).roots.toFinset := by
    intro y hy
    obtain ⟨b, -, rfl⟩ := Finset.mem_image.1 hy
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hP, Polynomial.IsRoot.def, Polynomial.eval_sub,
      Polynomial.eval_pow, Polynomial.eval_X, ← map_pow, ZMod.pow_card, sub_self]
  have hcard : (Polynomial.X ^ p - Polynomial.X : Polynomial (IsLocalRing.ResidueField B)).roots.toFinset.card ≤
      (Finset.univ.image φ).card := by
    rw [Finset.card_image_of_injective _ hφ, Finset.card_univ, ZMod.card]
    calc _ ≤ Multiset.card (Polynomial.X ^ p - Polynomial.X : Polynomial (IsLocalRing.ResidueField B)).roots :=
          Multiset.toFinset_card_le _
      _ ≤ (Polynomial.X ^ p - Polynomial.X : Polynomial (IsLocalRing.ResidueField B)).natDegree :=
          Polynomial.card_roots' _
      _ = p := FiniteField.X_pow_card_sub_X_natDegree_eq _ hp.one_lt
  have heq := Finset.eq_of_subset_of_card_le hsub hcard
  have hrmem : IsLocalRing.residue B a ∈
      (Polynomial.X ^ p - Polynomial.X : Polynomial (IsLocalRing.ResidueField B)).roots.toFinset := by
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hP, Polynomial.IsRoot.def, Polynomial.eval_sub,
      Polynomial.eval_pow, Polynomial.eval_X, hr, sub_self]
  rw [← heq] at hrmem
  obtain ⟨x, -, hx⟩ := Finset.mem_image.1 hrmem
  refine ⟨x, hφ ?_⟩
  have ha : a ^ m = (N : B) := Subtype.ext (by simp [a, hα])
  rw [map_pow, hx, map_natCast, ← map_pow, ha, map_natCast]

end GlobalTheory.Ord2.AuxiliaryInertOddPrime

namespace GlobalTheory.Ord2.AuxiliaryInertOddPrime

theorem normV_eq_absNorm (v : Pl) : normV v = Ideal.absNorm v.asIdeal := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl

theorem absNorm_dvd_of_mem {I : Ideal (𝓞 ℚ)} {n : ℕ} (h : (n : 𝓞 ℚ) ∈ I) : Ideal.absNorm I ∣ n := by
  have h1 := Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem I).2 h)
  rwa [Ideal.absNorm_span_natCast, RingOfIntegers.rank, Module.finrank_self, pow_one] at h1

theorem natCast_mem_iff (v : Pl) (n : ℕ) : (n : 𝓞 ℚ) ∈ v.asIdeal ↔ normV v ∣ n := by
  rw [normV_eq_absNorm]
  refine ⟨absNorm_dvd_of_mem, ?_⟩
  rintro ⟨c, rfl⟩
  rw [Nat.cast_mul]
  exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem _)

theorem normV_prime' (v : Pl) : (normV v).Prime := by
  have h1 : 1 < normV v := NumberField.HeightOneSpectrum.one_lt_absNorm v
  refine Nat.prime_def.2 ⟨h1, fun m hm => ?_⟩
  obtain ⟨c, hc⟩ := hm
  have h2 := (natCast_mem_iff v _).2 dvd_rfl
  rw [hc, Nat.cast_mul] at h2
  rcases v.isPrime.mem_or_mem h2 with h | h
  · exact Or.inr (Nat.dvd_antisymm ⟨c, hc⟩ ((natCast_mem_iff v _).1 h))
  · have h3 := Nat.dvd_antisymm (Dvd.intro_left m hc.symm) ((natCast_mem_iff v _).1 h)
    rw [h3] at hc
    exact Or.inl (Nat.eq_of_mul_eq_mul_right (by omega) (hc.symm.trans (one_mul _).symm))

theorem val_natCast_lt_one_iff {Ω : Type} [Field Ω] [Algebra ℚ Ω] {A : ValuationSubring Ω} {w : Pl}
    (h : IsPlaceOver A w) (n : ℕ) : A.valuation (n : Ω) < 1 ↔ normV w ∣ n := by
  rw [← natCast_mem_iff, ← h]
  simp

end GlobalTheory.Ord2.AuxiliaryInertOddPrime

namespace GlobalTheory.Ord2.AuxiliaryInertOddPrime

theorem exists_odd_prime_gt_two_bounds : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (n : ℕ)
    (S S' : Finset Pl) (U : Subgroup (G ℚ Ω)) (σ : G ℚ Ω), IsOpen (U : Set (G ℚ Ω)) →
    σ ∈ ⁅(cycBar ℚ Ω l).ker, (cycBar ℚ Ω l).ker⁆ → ∃ (w : Pl) (B : ValuationSubring Ω) (τ : G ℚ Ω),
      w ∉ S ∧ w ∉ S' ∧ IsPlaceOver B w ∧ IsFrob B (normV w) τ ∧ τ ∈ Dec (F := ℚ) B ∧ σ⁻¹ * τ ∈ U ∧
      l ^ n ∣ normV w - 1 ∧ ∀ v ∈ S, ∃ x : ZMod (normV w), x ^ (l ^ n) = (normV v : ZMod (normV w)) := by
  intro l hl Ω _ _ _ n S S' U σ hU hσ
  classical
  haveI hΩ : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have hm : 0 < l ^ n := pow_pos hl.out.pos n
  obtain ⟨ζ, hζ⟩ : ∃ ζ : Ω, IsPrimitiveRoot ζ (l ^ n) := by
    haveI : NeZero ((l ^ n : ℕ) : Ω) := ⟨Nat.cast_ne_zero.2 hm.ne'⟩
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic (l ^ n) Ω)
      (Polynomial.degree_cyclotomic_pos _ Ω hm).ne'
    exact ⟨z, Polynomial.isRoot_cyclotomic_iff.1 hz⟩
  have hα : ∀ v : Pl, ∃ α : Ω, α ^ (l ^ n) = (normV v : Ω) := fun v => IsAlgClosed.exists_pow_nat_eq _ hm
  choose α hα using hα
  let T : Finset Ω := insert ζ (S.image α)
  let O : Set (G ℚ Ω) := {τ | σ⁻¹ * τ ∈ U} ∩ ⋂ x ∈ T, {τ | τ x = x}
  have hO : IsOpen O := (hU.preimage (continuous_mul_left σ⁻¹)).inter
    (isOpen_biInter_finset fun x _ => isOpen_stab x)
  have hσker : σ ∈ (cycBar ℚ Ω l).ker := Subgroup.commutator_le_left _ _ hσ
  have hσO : σ ∈ O := by
    refine ⟨by simp [U.one_mem], Set.mem_iInter₂.2 fun x hx => ?_⟩
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact fix_root hσker hζ.pow_eq_one
    · obtain ⟨v, -, rfl⟩ := Finset.mem_image.1 hx
      exact comm_fix (fun g => map_natCast g _) hσ (hα v)
  have hl0 : Ideal.span {((l : ℕ) : 𝓞 ℚ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact Nat.cast_ne_zero.2 hl.out.ne_zero
  have hTfin : ((S : Set Pl) ∪ (S' : Set Pl) ∪ {v : Pl | v.asIdeal ∣ Ideal.span {((l : ℕ) : 𝓞 ℚ)}}).Finite :=
    ((S.finite_toSet).union (S'.finite_toSet)).union (Ideal.finite_factors hl0)
  have hdense := GlobalTheory.Published.ChebotarevDegreeOne.dense (F := ℚ) (Ω := Ω) GlobalTheory.Published.chebotarevDegreeOne' hTfin
  obtain ⟨τ, hτO, w, hwT, -, B, hB, hτ⟩ := hdense.inter_open_nonempty O hO ⟨σ, hσO⟩
  simp only [Set.mem_union, Finset.mem_coe, Set.mem_setOf_eq, not_or] at hwT
  obtain ⟨⟨hwS, hwS'⟩, hwl⟩ := hwT
  have hlw : ((l : ℕ) : 𝓞 ℚ) ∉ w.asIdeal := fun h =>
    hwl (Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 h))
  have hfix : ∀ x ∈ T, τ x = x := fun x hx => Set.mem_iInter₂.1 hτO.2 x hx
  have hp : (normV w).Prime := normV_prime' w
  have hpB : B.valuation ((normV w : ℕ) : Ω) < 1 := (val_natCast_lt_one_iff hB _).2 dvd_rfl
  have hlB : ¬ B.valuation ((l : ℕ) : Ω) < 1 := fun h => hlw ((hB _).1 (by simpa using h))
  have hnot : ¬ B.valuation ((l ^ n : ℕ) : Ω) < 1 := fun h =>
    hlB ((val_natCast_lt_one_iff hB l).2 (hp.dvd_of_dvd_pow ((val_natCast_lt_one_iff hB (l ^ n)).1 h)))
  have hpows := (ML.placeBasic Ω).2.2.2.2.2.2.1 B (normV w) (l ^ n) τ hτ hnot
  have h1 : ζ ^ normV w = ζ := (hpows ζ hζ.pow_eq_one).symm.trans (hfix ζ (Finset.mem_insert_self _ _))
  have h2 : ζ ^ (normV w - 1) = 1 := by
    have hz : ζ ≠ 0 := hζ.ne_zero hm.ne'
    refine mul_right_cancel₀ hz ?_
    rw [← pow_succ, Nat.sub_add_cancel hp.one_le, one_mul, h1]
  refine ⟨w, B, τ, hwS, hwS', hB, hτ, hτ.1, hτO.1, hζ.dvd_of_pow_eq_one _ h2, fun v hv => ?_⟩
  have hτv : τ (α v) = α v := hfix _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem α hv))
  refine root_mod hp hpB hm.ne' (hα v) fun h => ?_
  have := hτ.2 (α v) h
  rwa [hτv] at this

end GlobalTheory.Ord2.AuxiliaryInertOddPrime
