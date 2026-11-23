import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteAdeleBaseChangeEquiv
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsNormOneIdeleOrderOneTrivialElsewhere
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct

theorem GlobalTheory.TwV.Xc.exists_pow_lt_of_lt_one_intZ (x γ : WithZero (Multiplicative ℤ)) (hx : x ≠ 0) (hγ : γ < 1) :
    ∃ n : ℕ, γ ^ n < x := by
  by_cases h0 : γ = 0
  · exact ⟨1, by simp [h0, zero_lt_iff.2 hx]⟩
  obtain ⟨a, rfl⟩ := WithZero.ne_zero_iff_exists.1 hx
  obtain ⟨g, rfl⟩ := WithZero.ne_zero_iff_exists.1 h0
  have hg : Multiplicative.toAdd g < 0 := by
    have : g < 1 := by exact_mod_cast hγ
    exact this
  refine ⟨(Multiplicative.toAdd a).natAbs + 1, ?_⟩
  rw [← WithZero.coe_pow, WithZero.coe_lt_coe]
  show Multiplicative.toAdd (g ^ ((Multiplicative.toAdd a).natAbs + 1)) < Multiplicative.toAdd a
  rw [toAdd_pow, nsmul_eq_mul]
  push_cast
  have h1 := neg_abs_le (Multiplicative.toAdd a)
  have h2 : Multiplicative.toAdd g ≤ -1 := by omega
  have h3 := abs_nonneg (Multiplicative.toAdd a)
  nlinarith

theorem GlobalTheory.TwV.Xc.adIso_comp_zero_of_div : ∀ {F E F' E' : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [Field F'] [NumberField F'] [Field E'] [NumberField E'] [Algebra F' E'] (iE : E' ≃+* E) (iA : AfE F' E' ≃+* AfE F E), (∀ x : E', iA (x ⊗ₜ[F'] 1) = iE x ⊗ₜ[F] 1) → (∀ y, iA y ∈ RInt F E ↔ y ∈ RInt F' E') → ∀ (ι : AfE F' E' ≃+* FiniteAdeleRing (𝓞 E') E'), GlobalTheory.TwU.IsAdIso ι → ∀ (z : AfE F E) (ℓ D : ℕ), 0 < ℓ → 0 < D → (∀ n : ℕ, (((D : E) / (ℓ : E) ^ n) ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F)) * z ∈ RInt F E) → ∀ (P : HeightOneSpectrum (𝓞 E')), ((ℓ : ℕ) : 𝓞 E') ∈ P.asIdeal → ι (iA.symm z) P = 0 := by
  intro F E F' E' _ _ _ _ _ _ _ _ _ _ iE iA hrat hint ι hι z ℓ D hℓ hD hdiv P hP
  set y := ι (iA.symm z) with hy

  have hc : ∀ n : ℕ, iA.symm (((D : E) / (ℓ : E) ^ n) ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F))
      = ((D : E') / (ℓ : E') ^ n) ⊗ₜ[F'] (1 : FiniteAdeleRing (𝓞 F') F') := by
    intro n
    rw [RingEquiv.symm_apply_eq, hrat]
    simp [map_div₀, map_pow, map_natCast]
  have hbound : ∀ n : ℕ, Valued.v (((D : E') / (ℓ : E') ^ n : E') : P.adicCompletion E') * Valued.v (y P) ≤ 1 := by
    intro n
    have hmem := hdiv n
    have h1 : iA.symm ((((D : E) / (ℓ : E) ^ n) ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F)) * z) ∈ RInt F' E' := by
      rw [← hint, RingEquiv.apply_symm_apply]; exact hmem
    have h2 := (hι.2 _).1 h1 P
    rw [map_mul, hc, map_mul, hι.1, ← hy] at h2
    rw [← map_mul]
    simpa using h2
  have hval : ∀ c : E', Valued.v ((c : E') : P.adicCompletion E') = P.valuation E' c :=
    fun c => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P c
  have hℓE : ((ℓ : 𝓞 E') : E') = (ℓ : E') := by simp
  have hlt : P.valuation E' (ℓ : E') < 1 := by
    rw [← hℓE]
    exact (HeightOneSpectrum.valuation_lt_one_iff_mem P _).2 hP
  have hℓ0 : P.valuation E' (ℓ : E') ≠ 0 := by
    rw [Ne, map_eq_zero]; exact_mod_cast hℓ.ne'
  have hD0 : P.valuation E' (D : E') ≠ 0 := by
    rw [Ne, map_eq_zero]; exact_mod_cast hD.ne'
  by_contra hyP
  have hyv : Valued.v (y P) ≠ 0 := by
    rw [Ne, map_eq_zero]; exact hyP
  obtain ⟨n, hn⟩ := GlobalTheory.TwV.Xc.exists_pow_lt_of_lt_one_intZ
    (P.valuation E' (D : E') * Valued.v (y P)) (P.valuation E' (ℓ : E')) (mul_ne_zero hD0 hyv) hlt
  have hb := hbound n
  rw [hval, map_div₀, map_pow] at hb
  have hpos : (0 : WithZero (Multiplicative ℤ)) < P.valuation E' (ℓ : E') ^ n :=
    zero_lt_iff.2 (pow_ne_zero _ hℓ0)
  have : P.valuation E' (D : E') * Valued.v (y P) ≤ P.valuation E' (ℓ : E') ^ n := by
    have he : P.valuation E' (D : E') * Valued.v (y P)
        = P.valuation E' (D : E') / P.valuation E' (ℓ : E') ^ n * Valued.v (y P) * P.valuation E' (ℓ : E') ^ n := by
      rw [div_mul_eq_mul_div, div_mul_cancel₀ _ (pow_ne_zero _ hℓ0)]
    rw [he]
    simpa using mul_le_mul' hb (le_refl (P.valuation E' (ℓ : E') ^ n))
  exact absurd hn (not_lt.2 this)
