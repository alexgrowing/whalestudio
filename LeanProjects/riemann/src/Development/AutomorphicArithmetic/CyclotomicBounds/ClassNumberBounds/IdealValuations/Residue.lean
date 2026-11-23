import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.IdealValuations.ResidueUnit

open NumberField NumberField.IsCMField NumberField.Units IsDedekindDomain
open scoped nonZeroDivisors

namespace KStar.IdealValuations

variable {K : Type*} [Field K] [NumberField K]

private theorem residueHom_algebraMap (P : Ideal (𝓞 K)) [P.IsMaximal] (a : 𝓞 K) :
    residueHom P (algebraMap (𝓞 K) (locAt P) a) = Ideal.Quotient.mk P a := by
  unfold residueHom
  exact IsLocalization.lift_eq _ a

theorem isResidue_iff (P : Ideal (𝓞 K)) [P.IsMaximal] (x : K) (r : 𝓞 K ⧸ P) :
    IsResidue P x r ↔ ∃ y : locAt P, (y : K) = x ∧ residueHom P y = r := by
  constructor
  · rintro ⟨a, b, hb, h1, h2⟩
    have hb0 : (b : K) ≠ 0 := by
      intro h
      have : b = 0 := by exact_mod_cast h
      exact hb (this ▸ P.zero_mem)
    have hx : x ∈ locAt P := ⟨a, b, hb, by
      have : x = (a : K) * (b : K)⁻¹ := by rw [← h1]; field_simp
      exact this⟩
    refine ⟨⟨x, hx⟩, rfl, ?_⟩
    have e : (⟨x, hx⟩ : locAt P) * algebraMap (𝓞 K) (locAt P) b
        = algebraMap (𝓞 K) (locAt P) a := Subtype.ext h1
    have e2 := congrArg (residueHom P) e
    rw [map_mul, residueHom_algebraMap, residueHom_algebraMap, ← h2] at e2
    have hb' : Ideal.Quotient.mk P b ≠ 0 := fun h => hb (Ideal.Quotient.eq_zero_iff_mem.mp h)
    exact mul_right_cancel₀ hb' e2
  · rintro ⟨y, rfl, rfl⟩
    obtain ⟨⟨a, b⟩, e⟩ := IsLocalization.surj P.primeCompl y
    refine ⟨a, b, b.2, congrArg Subtype.val e, ?_⟩
    have e2 := congrArg (residueHom P) e
    rwa [map_mul, residueHom_algebraMap, residueHom_algebraMap] at e2

private theorem valuation_eq_exp_count_int (v : HeightOneSpectrum (𝓞 K)) (a : 𝓞 K) (ha : a ≠ 0) :
    v.valuation K (a : K) = WithZero.exp (-FractionalIdeal.count K v
      (FractionalIdeal.spanSingleton (𝓞 K)⁰ (a : K))) := by
  have h1 : v.valuation K (a : K) = v.intValuation a := v.valuation_of_algebraMap a
  have h2 : FractionalIdeal.spanSingleton (𝓞 K)⁰ (a : K)
      = ((Ideal.span {a} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) :=
    (FractionalIdeal.coeIdeal_span_singleton a).symm
  rw [h1, h2, v.intValuation_if_neg ha, FractionalIdeal.count_coe K v (by simpa using ha)]

private theorem valuation_eq_exp_count (v : HeightOneSpectrum (𝓞 K)) (x : K) (hx : x ≠ 0) :
    v.valuation K x = WithZero.exp (-FractionalIdeal.count K v
      (FractionalIdeal.spanSingleton (𝓞 K)⁰ x)) := by
  obtain ⟨a, b, hb, e⟩ := IsFractionRing.div_surjective (𝓞 K) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbK : (b : K) ≠ 0 := by exact_mod_cast hb0
  have ha0 : a ≠ 0 := by
    rintro rfl
    apply hx
    simp [← e]
  have e' : x * (b : K) = (a : K) := by
    rw [← e]; exact div_mul_cancel₀ _ hbK
  have h1 := valuation_eq_exp_count_int v a ha0
  have h2 := valuation_eq_exp_count_int v b hb0
  rw [← e', map_mul, h2, ← FractionalIdeal.spanSingleton_mul_spanSingleton,
    FractionalIdeal.count_mul K v (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hx)
      (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hbK), neg_add, WithZero.exp_add] at h1
  exact mul_right_cancel₀ WithZero.exp_ne_zero h1

private theorem mem_locAt_iff (v : HeightOneSpectrum (𝓞 K)) (x : K) :
    x ∈ locAt v.asIdeal ↔ v.valuation K x ≤ 1 := by
  have h : x ∈ locAt v.asIdeal ↔ x ∈ v.valuationSubringAtPrime K := Iff.rfl
  rw [h, HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring,
    Valuation.mem_valuationSubring_iff]

theorem exists_unit_locAt_iff (v : HeightOneSpectrum (𝓞 K)) (x : Kˣ) :
    (∃ u : (locAt v.asIdeal)ˣ, ((u : locAt v.asIdeal) : K) = (x : K)) ↔
      FractionalIdeal.count K v
        ((toPrincipalIdeal (𝓞 K) K x : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
          FractionalIdeal (𝓞 K)⁰ K) = 0 := by
  have key : v.valuation K (x : K) = 1 ↔ FractionalIdeal.count K v
      (FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K)) = 0 := by
    rw [valuation_eq_exp_count v _ x.ne_zero, ← WithZero.exp_zero, WithZero.exp_inj, neg_eq_zero]
  rw [coe_toPrincipalIdeal, ← key]
  constructor
  · rintro ⟨u, hu⟩
    have h1 := (mem_locAt_iff v _).mp (u : locAt v.asIdeal).2
    have h2 := (mem_locAt_iff v _).mp ((u⁻¹ : (locAt v.asIdeal)ˣ) : locAt v.asIdeal).2
    have h3 : ((u : locAt v.asIdeal) : K) * (((u⁻¹ : (locAt v.asIdeal)ˣ) : locAt v.asIdeal) : K)
        = 1 := congrArg Subtype.val u.mul_inv
    have h4 := congrArg (v.valuation K) h3
    rw [map_mul, map_one] at h4
    rw [← hu]
    exact eq_one_of_one_le_mul_left h1 h2 h4.ge
  · intro h
    have h1 : (x : K) ∈ locAt v.asIdeal := (mem_locAt_iff v _).mpr h.le
    have h2 : (x : K)⁻¹ ∈ locAt v.asIdeal := (mem_locAt_iff v _).mpr (by rw [map_inv₀, h]; simp)
    exact ⟨⟨⟨_, h1⟩, ⟨_, h2⟩, Subtype.ext (mul_inv_cancel₀ x.ne_zero),
      Subtype.ext (inv_mul_cancel₀ x.ne_zero)⟩, rfl⟩

end KStar.IdealValuations
