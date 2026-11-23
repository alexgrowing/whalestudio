import Formalism.LocalToGlobal.GroupLattices.PerfectRings.GoodRingWittExtension
import Formalism.LocalToGlobal.GroupLattices.PerfectRings.IsLocalRingOfComplete
import Formalism.LocalToGlobal.GroupLattices.LevelGatherings.StdSubPlacesConst

noncomputable section

namespace Formalism.L2.G

open Formalism.MainNotions.G Formalism.BasicNotions.Examples₂ IsLocalRing IntermediateField

variable (p : ℕ) [hp : Fact p.Prime] (n : ℕ)

instance charZero_witt_quadratic : CharZero (W2 p n) := by
  obtain ⟨q, hq⟩ := CharP.exists (W2 p n)
  rcases CharP.char_is_prime_or_zero (W2 p n) q with h | h
  · exfalso
    have h0 : ((q : ℕ) : W2 p n) = 0 := CharP.cast_eq_zero _ q
    have h1 : ((q : ℕ) : F2 p n) = 0 := by
      have := congrArg (WittVector.constantCoeff (p := p) (R := F2 p n)) h0
      rwa [map_natCast, map_zero] at this
    have h2 : p ∣ q := (CharP.cast_eq_zero_iff (F2 p n) p q).1 h1
    have h3 : p = q := (Nat.prime_dvd_prime_iff_eq hp.out h).1 h2
    exact (WittVector.irreducible p (k := F2 p n)).ne_zero (h3 ▸ h0)
  · subst h
    exact CharP.charP_to_charZero _

instance instCharZeroOO : CharZero (OO p n) := charZero_of_injective_algebraMap (Quad.algebraMap_injective _)

instance instCharZeroKO : CharZero (KO p n) :=
  charZero_of_injective_algebraMap (IsFractionRing.injective (OO p n) (KO p n))

theorem completeOO : IsAdicComplete (maximalIdeal (OO p n)) (OO p n) :=
  GatR.isAdicComplete (WittVector.irreducible p) inferInstance

section Fin

variable (L : Type) [Field L] [Algebra (KO p n) L] [FiniteDimensional (KO p n) L] [Algebra (OO p n) L]
  [IsScalarTower (OO p n) (KO p n) L]

abbrev OL : Type := integralClosure (OO p n) L

instance instDvrOL : IsDiscreteValuationRing (OL p n L) := IntCl.isDVR (OO p n) (KO p n) L (completeOO p n)

def extOf : ExtOf (OO p n) (KO p n) (OL p n L) L where
  φ := algebraMap _ _
  φK := algebraMap _ _
  comm := fun x => (IsScalarTower.algebraMap_apply (OO p n) (KO p n) L x).symm
  fin := RingHom.finite_algebraMap.2 (IntCl.finite (OO p n) (KO p n) L)
  frac := IntCl.frac (OO p n) (KO p n) L
  complete := IntCl.complete (OO p n) (KO p n) L (completeOO p n)

theorem settingOL (h5 : 5 ≤ p) (h2 : 2 ≤ n) (he : Even n) :
    HidaSetting p n (WQ p n) (QQ p n) (OL p n L) L ((extOf p n L).φK.comp (iota p n)) (sig p n)
      ((extOf p n L).φ.comp (jO p n)) ((extOf p n L).φ (wU p n)) :=
  setting_ext (settingStd p n h5 h2 he) (extOf p n L)

end Fin

section NF

abbrev Om : Type := AlgebraicClosure (KO p n)

variable {p n} {LL : Type} [Field LL] [NumberField LL] (τ : LL →+* Om p n)

def Lt : IntermediateField (KO p n) (Om p n) := adjoin (KO p n) (Set.range τ)

theorem range_le_simple (θ : LL) (hθ : ℚ⟮θ⟯ = ⊤) (x : LL) : τ x ∈ (KO p n)⟮τ θ⟯ := by

  let T : Subfield LL := ((KO p n)⟮τ θ⟯).toSubfield.comap τ
  have hQ : ∀ q : ℚ, algebraMap ℚ LL q ∈ T := fun q => by
    simp [T, Subfield.mem_comap, eq_ratCast, map_ratCast, SubfieldClass.ratCast_mem]
  have key : ℚ⟮θ⟯ ≤ T.toIntermediateField hQ := by
    rw [IntermediateField.adjoin_simple_le_iff]
    exact IntermediateField.mem_adjoin_simple_self _ _
  have hx : x ∈ ℚ⟮θ⟯ := by rw [hθ]; exact IntermediateField.mem_top
  exact key hx

instance instFinLt : FiniteDimensional (KO p n) (Lt τ) := by
  obtain ⟨θ, hθ⟩ := Field.exists_primitive_element ℚ LL
  have hle : Lt τ ≤ (KO p n)⟮τ θ⟯ := by
    unfold Lt
    rw [adjoin_le_iff]
    rintro _ ⟨x, rfl⟩
    exact range_le_simple τ θ hθ x
  have : FiniteDimensional (KO p n) (KO p n)⟮τ θ⟯ :=
    adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral _)
  exact FiniteDimensional.of_injective (inclusion hle).toLinearMap (inclusion_injective hle)

def embL : LL →+* Lt τ := τ.codRestrict (Lt τ) (fun x => subset_adjoin _ _ ⟨x, rfl⟩)

theorem embL_val (x : LL) : ((embL τ x : Lt τ) : Om p n) = τ x := rfl

abbrev Ot : Type := OL p n (Lt τ)

def extOt : ExtOf (OO p n) (KO p n) (Ot τ) (Lt τ) := extOf p n (Lt τ)

end NF

section Place

open NumberField IsDedekindDomain

variable {p n} {LL : Type} [Field LL] [NumberField LL] (τ : LL →+* Om p n)

theorem embL_integral (x : 𝓞 LL) :
    ((embL τ).comp (algebraMap (𝓞 LL) LL)) x ∈ integralClosure (OO p n) (Lt τ) := by
  rw [mem_integralClosure_iff]
  have h : IsIntegral ℤ (algebraMap (𝓞 LL) LL x) := RingOfIntegers.isIntegral_coe x
  exact (h.map (((embL τ).comp (RingHom.id LL)).toIntAlgHom)).tower_top

def embO : 𝓞 LL →+* Ot τ :=
  ((embL τ).comp (algebraMap (𝓞 LL) LL)).codRestrict (integralClosure (OO p n) (Lt τ)) (embL_integral τ)

theorem embO_val (x : 𝓞 LL) : ((embO τ x : Ot τ) : Lt τ) = embL τ (x : LL) := rfl

def placeIdeal : Ideal (𝓞 LL) := (maximalIdeal (Ot τ)).comap (embO τ)

instance : (placeIdeal τ).IsPrime := Ideal.comap_isPrime _ _

theorem wU_mem_max : wU p n ∈ maximalIdeal (OO p n) := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu

  have h0 : IsUnit (Quad.toRes (p : W2 p n) (wU p n)) := hu.map _
  rw [Quad.toRes_apply] at h0
  have hre : (wU p n).re = 0 := rfl
  rw [hre, map_zero, isUnit_zero_iff] at h0
  have h1 : (1 : W2 p n) ∈ Ideal.span {(p : W2 p n)} := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_one]
    exact h0.symm
  rw [Ideal.mem_span_singleton] at h1
  have hpu : IsUnit (p : W2 p n) := isUnit_of_dvd_one h1
  have h2 : IsUnit ((p : W2 p n).coeff 0) := hpu.map (WittVector.constantCoeff (p := p) (R := F2 p n))
  rw [WittVector.coeff_p_zero] at h2
  exact not_isUnit_zero h2

theorem under_max (L : Type) [Field L] [Algebra (KO p n) L] [FiniteDimensional (KO p n) L] [Algebra (OO p n) L]
    [IsScalarTower (OO p n) (KO p n) L] :
    (maximalIdeal (OL p n L)).comap (algebraMap (OO p n) (OL p n L)) = maximalIdeal (OO p n) :=
  IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (maximalIdeal _))

theorem p_mem_max (L : Type) [Field L] [Algebra (KO p n) L] [FiniteDimensional (KO p n) L] [Algebra (OO p n) L]
    [IsScalarTower (OO p n) (KO p n) L] : (p : OL p n L) ∈ maximalIdeal (OL p n L) := by
  have hw2 : wU p n * wU p n = (p : OO p n) := by
    ext <;> simp [wU]
  have h1 : (p : OO p n) ∈ maximalIdeal (OO p n) := hw2 ▸ Ideal.mul_mem_left _ _ wU_mem_max
  rw [← under_max L, Ideal.mem_comap, map_natCast] at h1
  exact h1

theorem p_mem_placeIdeal : (p : 𝓞 LL) ∈ placeIdeal τ := by
  show embO τ (p : 𝓞 LL) ∈ maximalIdeal (Ot τ)
  rw [map_natCast]
  exact p_mem_max (Lt τ)

def placeOf : HeightOneSpectrum (𝓞 LL) where
  asIdeal := placeIdeal τ
  isPrime := inferInstance
  ne_bot := by
    intro h
    have := p_mem_placeIdeal τ
    rw [h, Ideal.mem_bot] at this
    exact hp.out.ne_zero (by exact_mod_cast this)

theorem isUnit_embO {d : 𝓞 LL} (hd : d ∉ placeIdeal τ) : IsUnit (embO τ d) := by
  by_contra h
  exact hd ((IsLocalRing.mem_maximalIdeal _).mpr h)

theorem induces (x : LL) :
    (placeOf τ).valuation LL x ≤ 1 ↔ embL τ x ∈ Set.range (algebraMap (Ot τ) (Lt τ)) := by
  constructor
  · intro hv
    obtain ⟨c, d, h⟩ := (placeOf τ).exists_primeCompl_mul_eq_of_integer x hv
    obtain ⟨u, hu⟩ := isUnit_embO τ (d := d) d.2
    refine ⟨embO τ c * (u⁻¹ : (Ot τ)ˣ), ?_⟩
    have h1 : embL τ x * embL τ ((d : 𝓞 LL) : LL) = embL τ (c : LL) := by rw [← map_mul]; exact congrArg _ h
    have h2 : (embL τ ((d : 𝓞 LL) : LL)) * (((u⁻¹ : (Ot τ)ˣ) : Ot τ) : Lt τ) = 1 := by
      rw [← embO_val, ← hu]
      have : ((u : Ot τ) * ((u⁻¹ : (Ot τ)ˣ) : Ot τ)) = 1 := u.mul_inv
      exact congrArg Subtype.val this
    show ((embO τ c : Ot τ) : Lt τ) * (((u⁻¹ : (Ot τ)ˣ) : Ot τ) : Lt τ) = embL τ x
    rw [embO_val, ← h1, mul_assoc, h2, mul_one]
  · rintro ⟨y, hy⟩
    by_contra hv
    rw [not_le] at hv
    have hx : x ≠ 0 := by
      rintro rfl
      simp at hv
    have hv' : (placeOf τ).valuation LL x⁻¹ < 1 := by
      rw [map_inv₀]
      exact inv_lt_one_of_one_lt₀ hv
    obtain ⟨c, d, h⟩ := (placeOf τ).exists_primeCompl_mul_eq_of_integer x⁻¹ hv'.le
    have hc : c ∈ placeIdeal τ := by
      have : (placeOf τ).valuation LL (algebraMap (𝓞 LL) LL c) < 1 := by
        rw [← h, map_mul]
        exact mul_lt_one_of_lt_of_le hv' ((placeOf τ).valuation_le_one _)
      exact ((placeOf τ).valuation_lt_one_iff_mem c).1 this
    have h3 : y * embO τ c = embO τ d := by
      apply Subtype.ext
      show (y : Lt τ) * ((embO τ c : Ot τ) : Lt τ) = ((embO τ d : Ot τ) : Lt τ)
      have hy' : (y : Lt τ) = embL τ x := hy
      rw [hy', embO_val, embO_val, ← map_mul]
      congr 1
      show x * algebraMap (𝓞 LL) LL c = _
      rw [← h, ← mul_assoc, mul_inv_cancel₀ hx, one_mul]
    have : embO τ d ∈ maximalIdeal (Ot τ) := h3 ▸ Ideal.mul_mem_left _ _ hc
    exact d.2 this

end Place

end Formalism.L2.G
