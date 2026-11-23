import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.StmtFields
import Development.AutomorphicArithmetic.QuadraticCharacters.GaussRoot

open NumberField Formalism.HC UpperTheory.Top UpperTheory.V

theorem UpperTheory.V.isCMField_of_isChiField :
    ∀ (ψ : PChar) (e q d : ℕ), q.Prime → q % 4 = 3 → ∀ (E : Type) [Field E] [NumberField E], IsChiField ψ e q d E → IsCMField E := by
  intro ψ e q d hq hq4 E _ _ hE
  obtain ⟨N, hN, j, ζ, -, -, hqN, -, hζ, hτ⟩ := hE
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : NeZero (N : ℚ) := ⟨by exact_mod_cast hN.out⟩
  haveI : IsCyclotomicExtension {N} ℚ (CyclotomicField N ℚ) := CyclotomicField.isCyclotomicExtension N ℚ
  haveI : IsAbelianGalois ℚ (CyclotomicField N ℚ) :=
    IsCyclotomicExtension.isAbelianGalois {N} ℚ (CyclotomicField N ℚ)
  haveI : IsAbelianGalois ℚ E := IsAbelianGalois.of_algHom j
  have hζq : IsPrimitiveRoot (ζ ^ (N / q)) q :=
    hζ.pow (NeZero.pos N) (Nat.div_mul_cancel hqN).symm
  obtain ⟨G, hG2, hGσ⟩ := HostParam.SlopeTestRemainingChoices.GaussRoot.exists_gauss hq4 hζq
  have hGL : G ∈ j.fieldRange := by
    rw [← IsGalois.fixedField_fixingSubgroup j.fieldRange, IntermediateField.mem_fixedField_iff]
    intro τ hτL
    rw [IntermediateField.mem_fixingSubgroup_iff] at hτL
    have hfix : ∀ x : E, τ (j x) = j x := fun x => hτL _ (AlgHom.mem_fieldRange.2 ⟨x, rfl⟩)
    obtain ⟨a, -, ha⟩ := hζ.eq_pow_of_pow_eq_one (ξ := τ ζ) (by rw [← map_pow, hζ.pow_eq_one, map_one])
    obtain ⟨-, -, hjq, -⟩ := (hτ τ a ha.symm).1 hfix
    have hprim : IsPrimitiveRoot (ζ ^ a) N := by
      rw [ha]
      exact hζ.map_of_injective τ.injective
    have hcop : a.Coprime q :=
      Nat.Coprime.coprime_dvd_right hqN ((hζ.pow_iff_coprime (NeZero.pos N) a).1 hprim)
    have hquad : quadraticChar (ZMod q) (a : ZMod q) = 1 := by
      have h := jacobiSym.legendreSym.to_jacobiSym q (a : ℤ)
      rw [hjq] at h
      unfold legendreSym at h
      rw [Int.cast_natCast] at h
      exact h
    have h := hGσ (τ : CyclotomicField N ℚ →+* CyclotomicField N ℚ) a hcop (by
      rw [RingHom.coe_coe, map_pow, ← ha, ← pow_mul, ← pow_mul, mul_comm])
    rw [hquad] at h
    simpa using h
  obtain ⟨x, hx⟩ := AlgHom.mem_fieldRange.1 hGL
  have hx2 : x ^ 2 = -(q : E) := by
    apply j.injective
    change j (x ^ 2) = j (-(q : E))
    rw [map_pow, hx, hG2, map_neg, map_natCast]
  haveI : IsTotallyComplex E := ⟨fun w => by
    rw [← InfinitePlace.not_isReal_iff_isComplex, InfinitePlace.isReal_iff,
      ComplexEmbedding.isReal_iff]
    intro hr
    have hc := RingHom.congr_fun hr x
    rw [ComplexEmbedding.conjugate_coe_eq] at hc
    have him : (w.embedding x).im = 0 := Complex.conj_eq_iff_im.1 hc
    have hz2 : (w.embedding x) ^ 2 = -(q : ℂ) := by
      rw [← map_pow, hx2, map_neg, map_natCast]
    have hre := congrArg Complex.re hz2
    simp [sq, him] at hre
    have hqpos : (0:ℝ) < q := by exact_mod_cast hq.pos
    nlinarith [mul_self_nonneg (w.embedding x).re]⟩
  exact NumberField.IsCMField.of_isAbelianGalois E
