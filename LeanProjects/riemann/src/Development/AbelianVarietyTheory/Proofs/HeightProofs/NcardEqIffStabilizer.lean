import Mathlib
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LFunctionPositiveConductorFourEight

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldSize.RaySplit

open NumberField IsDedekindDomain Polynomial GlobalTheory.FieldSize GlobalTheory.NT
open scoped IntermediateField Pointwise

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

set_option autoImplicit false in
open NumberField IsDedekindDomain Polynomial in
open scoped IntermediateField Pointwise in
variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] in

theorem _root_.GlobalTheory.FieldSize.RaySplit.ncard_eq_primesOver (𝔭 : HeightOneSpectrum (𝓞 K)) :
    {Q : HeightOneSpectrum (𝓞 L) | Q.asIdeal.comap (algebraMap (𝓞 K) (𝓞 L)) = 𝔭.asIdeal}.ncard =
      (𝔭.asIdeal.primesOver (𝓞 L)).ncard := by
  have hinj : Function.Injective (fun Q : HeightOneSpectrum (𝓞 L) => Q.asIdeal) :=
    fun Q Q' h => HeightOneSpectrum.ext h
  rw [← Set.ncard_image_of_injective _ hinj]
  congr 1
  ext P
  simp only [Set.mem_image, Set.mem_setOf_eq, Ideal.primesOver]
  constructor
  · rintro ⟨Q, hQ, rfl⟩
    exact ⟨Q.isPrime, ⟨hQ.symm⟩⟩
  · rintro ⟨hP, hlies⟩
    refine ⟨⟨P, hP, ?_⟩, hlies.over.symm, rfl⟩
    rintro rfl
    apply 𝔭.ne_bot
    rw [hlies.over, Ideal.under, Ideal.comap_bot_of_injective]
    exact FaithfulSMul.algebraMap_injective _ _

set_option autoImplicit false in
open NumberField IsDedekindDomain Polynomial in
open scoped IntermediateField Pointwise in
variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] in
private theorem ncard_primesOver_eq_finrank_iff_frob_eq_one {F R : Type} [Field F]
    [NumberField F] [Field R] [NumberField R] [Algebra F R] [IsGalois F R]
    {𝔭 : HeightOneSpectrum (𝓞 F)} (hu : _root_.GlobalTheory.NT.UnramIn R 𝔭) {σ : Gal(R/F)}
    (hσ : _root_.GlobalTheory.NT.IsFrob R 𝔭 σ) :
    (𝔭.asIdeal.primesOver (𝓞 R)).ncard = Module.finrank F R ↔ σ = 1 := by
  obtain ⟨P, hPp, hPo, hfrob⟩ := hσ
  haveI := hPp
  haveI := hPo
  have hPne : P ≠ ⊥ := by
    rintro rfl
    apply 𝔭.ne_bot
    rw [hPo.over, Ideal.under, Ideal.comap_bot_of_injective]
    exact FaithfulSMul.algebraMap_injective _ _
  haveI : P.IsMaximal := hPp.isMaximal hPne
  haveI : 𝔭.asIdeal.IsMaximal := 𝔭.isMaximal
  have he : 𝔭.asIdeal.ramificationIdxIn (𝓞 R) = 1 := by
    rw [← Ideal.card_inertia_eq_ramificationIdxIn (G := Gal(R/F)) 𝔭.asIdeal P]
    have hbot : Ideal.inertia Gal(R/F) P = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro τ hτ
      exact hu τ ⟨P, hPp, hPo, fun x => (AddSubgroup.mem_inertia.mp hτ) x⟩
    rw [hbot, Subgroup.card_bot]
  have hf : 𝔭.asIdeal.inertiaDegIn (𝓞 R) = Module.finrank (𝓞 F ⧸ 𝔭.asIdeal) (𝓞 R ⧸ P) := by
    rw [Ideal.inertiaDegIn_eq_inertiaDeg 𝔭.asIdeal P Gal(R/F), ← Ideal.inertiaDeg_eq_inertiaDeg' 𝔭.asIdeal P,
      Ideal.inertiaDeg'_algebraMap]
  have hcount :=
    Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn 𝔭.asIdeal (𝓞 R) Gal(R/F)
  rw [he, one_mul, hf, IsGalois.card_aut_eq_finrank] at hcount
  have hdeg : 0 < Module.finrank F R := Module.finrank_pos
  letI : Field (𝓞 F ⧸ 𝔭.asIdeal) := Ideal.Quotient.field _
  letI : Field (𝓞 R ⧸ P) := Ideal.Quotient.field _
  letI : Fintype (𝓞 F ⧸ 𝔭.asIdeal) := Fintype.ofFinite _
  letI : Fintype (𝓞 R ⧸ P) := Fintype.ofFinite _
  have hq : Ideal.absNorm 𝔭.asIdeal = Fintype.card (𝓞 F ⧸ 𝔭.asIdeal) := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  have hcard : Fintype.card (𝓞 R ⧸ P) =
      Fintype.card (𝓞 F ⧸ 𝔭.asIdeal) ^ Module.finrank (𝓞 F ⧸ 𝔭.asIdeal) (𝓞 R ⧸ P) :=
    Module.card_eq_pow_finrank
  have hq1 : 1 < Fintype.card (𝓞 F ⧸ 𝔭.asIdeal) := Fintype.one_lt_card
  have hsplit : (𝔭.asIdeal.primesOver (𝓞 R)).ncard = Module.finrank F R ↔
      Module.finrank (𝓞 F ⧸ 𝔭.asIdeal) (𝓞 R ⧸ P) = 1 := by
    constructor
    · intro h
      rw [h] at hcount
      exact Nat.eq_of_mul_eq_mul_left hdeg (hcount.trans (mul_one _).symm)
    · intro h
      rw [h, mul_one] at hcount
      exact hcount
  rw [hsplit]
  constructor
  · intro h1
    have hcq : Fintype.card (𝓞 R ⧸ P) = Fintype.card (𝓞 F ⧸ 𝔭.asIdeal) := by
      rw [hcard, h1, pow_one]
    apply hu σ
    refine ⟨P, hPp, hPo, fun x => ?_⟩
    have hxq : x ^ Ideal.absNorm 𝔭.asIdeal - x ∈ P := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, sub_eq_zero, hq, ← hcq]
      exact FiniteField.pow_card _
    have hsum := P.add_mem (hfrob x) hxq
    rwa [sub_add_sub_cancel] at hsum
  · intro h1
    subst h1
    have hall : ∀ y : 𝓞 R ⧸ P, y ^ Fintype.card (𝓞 F ⧸ 𝔭.asIdeal) = y := by
      intro y
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
      have hx := hfrob x
      rw [one_smul, ← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, sub_eq_zero, hq] at hx
      exact hx.symm
    have hroots := Polynomial.card_le_degree_of_subset_roots
      (p := (X ^ Fintype.card (𝓞 F ⧸ 𝔭.asIdeal) - X : (𝓞 R ⧸ P)[X])) (Z := Finset.univ)
      (fun y _ => by
        rw [Polynomial.mem_roots (FiniteField.X_pow_card_sub_X_ne_zero _ hq1)]
        simp [hall y])
    rw [Finset.card_univ, FiniteField.X_pow_card_sub_X_natDegree_eq _ hq1, hcard] at hroots
    have hle := (Nat.pow_le_pow_iff_right hq1).mp (hroots.trans (pow_one _).symm.le)
    have hpos : 0 < Module.finrank (𝓞 F ⧸ 𝔭.asIdeal) (𝓞 R ⧸ P) := by
      rcases Nat.eq_zero_or_pos (Module.finrank (𝓞 F ⧸ 𝔭.asIdeal) (𝓞 R ⧸ P)) with h0 | h0
      · rw [h0, mul_zero] at hcount
        omega
      · exact h0
    omega

set_option autoImplicit false in
open NumberField IsDedekindDomain Polynomial in
open scoped IntermediateField Pointwise in
variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] in
private theorem eq_one_iff_forall_char_eq_one_of_finite_commutative {G : Type} [Group G] [Finite G]
    [IsMulCommutative G] (σ : G) : σ = 1 ↔ ∀ χ : G →* ℂˣ, χ σ = 1 := by
  refine ⟨fun h χ => by rw [h, map_one], fun h => ?_⟩
  letI : CommGroup G := { (inferInstance : Group G) with mul_comm := mul_comm' }
  by_contra hσ
  haveI : NeZero (Monoid.exponent G) := ⟨Monoid.exponent_ne_zero_of_finite⟩
  obtain ⟨χ, hχ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity G ℂ hσ
  exact hχ (h χ)

set_option autoImplicit false in
open NumberField IsDedekindDomain Polynomial in
open scoped IntermediateField Pointwise in
variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] in
private theorem heckeIdeal_asIdeal_eq_heckeVal {F R : Type} [Field F] [NumberField F]
    [Field R] [NumberField R] [Algebra F R] (χ : Gal(R/F) →* ℂˣ) (𝔭 : HeightOneSpectrum (𝓞 F)) :
    _root_.GlobalTheory.NT.heckeIdeal R χ 𝔭.asIdeal = _root_.GlobalTheory.NT.heckeVal R χ 𝔭 := by
  unfold _root_.GlobalTheory.NT.heckeIdeal
  have hirr : ∀ 𝔮 : HeightOneSpectrum (𝓞 F), Irreducible (Associates.mk 𝔮.asIdeal) := fun 𝔮 =>
    Associates.irreducible_mk.mpr (Ideal.prime_of_isPrime 𝔮.ne_bot 𝔮.isPrime).irreducible
  rw [finprod_eq_single _ 𝔭]
  · rw [Associates.count_self (hirr 𝔭), pow_one]
  · intro 𝔮 h𝔮
    rw [Associates.count_eq_zero_of_ne (hirr 𝔮) (hirr 𝔭), pow_zero]
    intro h
    exact h𝔮 (HeightOneSpectrum.ext (associated_iff_eq.mp (Associates.mk_eq_mk_iff_associated.mp h)))

set_option autoImplicit false in
open NumberField IsDedekindDomain Polynomial in
open scoped IntermediateField Pointwise in
variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] in
private theorem false_of_ringHom_real_of_isTotallyComplex {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]
    (φ : F →+* ℝ) : False := by
  have h := IsTotallyComplex.isComplex (InfinitePlace.mk ((algebraMap ℝ ℂ).comp φ))
  rw [← InfinitePlace.not_isReal_iff_isComplex, InfinitePlace.isReal_mk_iff] at h
  apply h
  rw [ComplexEmbedding.isReal_iff]
  ext x
  simp [ComplexEmbedding.conjugate_coe_eq]

set_option autoImplicit false in
open NumberField IsDedekindDomain Polynomial in
open scoped IntermediateField Pointwise in
variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] in

theorem _root_.GlobalTheory.FieldSize.RaySplit.ncard_eq_finrank_iff : ∀ (K R : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Field R] [NumberField R]
    [Algebra K R] [IsAbelianGalois K R] (n : ℕ), 0 < n → _root_.GlobalTheory.FieldSize.IsRay R (Ideal.span {(n : 𝓞 K)}) →
    ∀ 𝔭 : HeightOneSpectrum (𝓞 K), (n : 𝓞 K) ∉ 𝔭.asIdeal →
      ({Q : HeightOneSpectrum (𝓞 R) | Q.asIdeal.comap (algebraMap (𝓞 K) (𝓞 R)) = 𝔭.asIdeal}.ncard = Module.finrank K R ↔
        ∃ π : 𝓞 K, 𝔭.asIdeal = Ideal.span {π} ∧ π - 1 ∈ Ideal.span {(n : 𝓞 K)}) := by
  intro K R _ _ _ _ _ _ _ n _ hray 𝔭 hn𝔭
  obtain ⟨hunr, -, hart⟩ := hray
  have hnot : ¬ 𝔭.asIdeal ∣ Ideal.span {(n : 𝓞 K)} := by
    rw [Ideal.dvd_span_singleton]
    exact hn𝔭
  have hcop : IsCoprime 𝔭.asIdeal (Ideal.span {(n : 𝓞 K)}) := by
    rw [Ideal.isCoprime_iff_sup_eq]
    by_contra h
    have heq := 𝔭.isMaximal.eq_of_le h le_sup_left
    apply hn𝔭
    rw [heq]
    exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
  have hu := hunr 𝔭 hnot
  obtain ⟨σ, hσ⟩ := _root_.GlobalTheory.NT.exists_isFrob R 𝔭
  rw [_root_.GlobalTheory.FieldSize.RaySplit.ncard_eq_primesOver,
    ncard_primesOver_eq_finrank_iff_frob_eq_one hu hσ]
  have hchar : σ = 1 ↔
      ∀ χ : Gal(R/K) →* ℂˣ, _root_.GlobalTheory.NT.heckeIdeal R χ 𝔭.asIdeal = 1 := by
    refine (eq_one_iff_forall_char_eq_one_of_finite_commutative σ).trans (forall_congr' fun χ => ?_)
    rw [heckeIdeal_asIdeal_eq_heckeVal, _root_.GlobalTheory.NT.heckeVal_of_unramIn R χ hu hσ,
      Units.val_eq_one]
  rw [hchar, hart 𝔭.asIdeal 𝔭.ne_bot hcop]
  constructor
  · rintro ⟨α, β, ⟨-, hβ, -, hβcop, hαβ, -⟩, hI⟩
    have hdvd : β ∣ α := by
      rw [← Ideal.span_singleton_le_span_singleton, ← hI]
      exact Submodule.mul_le.mpr fun a _ b hb => Ideal.mul_mem_left _ a hb
    obtain ⟨π, rfl⟩ := hdvd
    refine ⟨π, ?_, ?_⟩
    · have hβ0 : Ideal.span {β} ≠ 0 := by
        rwa [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      apply mul_right_cancel₀ hβ0
      rw [hI, ← Ideal.span_singleton_mul_span_singleton, mul_comm]
    · rw [Ideal.isCoprime_iff_sup_eq, Ideal.eq_top_iff_one, Submodule.mem_sup] at hβcop
      obtain ⟨u, hu', v, hv, huv⟩ := hβcop
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp hu'
      have key : π - 1 = c * (β * π - β) + (π - 1) * v := by
        linear_combination (1 - π) * huv
      rw [key]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hαβ) (Ideal.mul_mem_left _ _ hv)
  · rintro ⟨π, hπ, hπ1⟩
    refine ⟨π, 1, ⟨?_, one_ne_zero, ?_, ?_, hπ1, fun φ => (false_of_ringHom_real_of_isTotallyComplex φ).elim⟩, ?_⟩
    · rintro rfl
      exact 𝔭.ne_bot (hπ.trans (Ideal.span_singleton_eq_bot.mpr rfl))
    · rw [← hπ]
      exact hcop
    · rw [Ideal.span_singleton_one, Ideal.isCoprime_iff_sup_eq]
      exact top_sup_eq _
    · rw [Ideal.span_singleton_one, Ideal.mul_top, hπ]

end GlobalTheory.FieldSize.RaySplit

end
