import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneAddSmulVecMulVecMulVec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntMultipleOfIntegerStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharacterTrivialOnUnitTransvectionsStatement

open ReciprocityTheory.ChartRestriction.G.FD NumberField GlobalTheory.UnipKill

namespace GlobalTheory.UnipKill

theorem killsTransv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (X : Data E N),
    1 < Module.finrank ℚ E / 2 → ∀ (φ : X.Γ →* Multiplicative ℝ) (ξ : Fin N → E) (s : E),
    ξ ∈ X.Λ → herm X.Gm ξ ξ = 0 → cc s = s → IsIntegral ℤ s → ∀ γ : X.Γ,
    ((γ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) = transvMat X.Gm ξ (X.m * s * X.κ0) →
    φ γ = 1 := by
  intro E _ _ _ N X hE φ ξ s hξ hiso hs hsint γ hγ
  by_cases h0 : ξ = 0
  · subst h0
    have h1 : ((γ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) = 1 := by
      rw [hγ]; ext a b; simp [transvMat, Matrix.one_apply]
    have : γ = 1 := by
      apply Subtype.ext; apply Units.ext; simpa using h1
    rw [this, map_one]
  obtain ⟨u, hu0, hureal, hkill⟩ := GlobalTheory.T.character_trivial_on_unit_transvections E N X hE φ ξ hξ h0 hiso
  obtain ⟨c, hc0, u', hu'⟩ := GlobalTheory.T.exists_int_multiple_of_integer E u hu0
  have hcE : (c : E) = (u : E) * (u' : E) := by
    have := congrArg (fun x : 𝓞 E => (x : E)) hu'
    simpa using this
  have huE : (u : E) ≠ 0 := by
    intro h; exact hu0 (RingOfIntegers.coe_eq_zero_iff.mp h)
  have hu'real : cc (u' : E) = u' := by
    have e : (u' : E) = (c : E) * (u : E)⁻¹ := by
      rw [hcE]; field_simp
    rw [e, cc_mul, cc_inv, cc_intCast, hureal]
  have hu'int : IsIntegral ℤ (u' : E) := RingOfIntegers.isIntegral_coe u'
  set n := c.natAbs with hn
  have hnpos : n ≠ 0 := Int.natAbs_ne_zero.mpr hc0
  obtain ⟨t, ht, htint, hut⟩ : ∃ t : E, cc t = t ∧ IsIntegral ℤ t ∧
      (u : E) * t = (n : E) * s := by
    rcases Int.natAbs_eq c with h | h
    · refine ⟨(u' : E) * s, by rw [cc_mul, hu'real, hs], hu'int.mul hsint, ?_⟩
      have : ((n : ℤ) : E) = (c : E) := by rw [← h]
      rw [← Int.cast_natCast, this, hcE]; ring
    · refine ⟨-((u' : E) * s), by rw [cc_neg, cc_mul, hu'real, hs], (hu'int.mul hsint).neg, ?_⟩
      have : ((n : ℤ) : E) = -(c : E) := by rw [h, Int.cast_neg, neg_neg]
      rw [← Int.cast_natCast, this, hcE]; ring
  have hmat : ((γ ^ n : X.Γ) : GL (Fin N) E) = (γ : GL (Fin N) E) ^ n := Subgroup.coe_pow _ _ _
  have hγn : (((γ ^ n : X.Γ) : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) =
      transvMat X.Gm ξ (X.m * (u * t) * X.κ0) := by
    rw [hmat, Units.val_pow_eq_pow_val, hγ, transvMat_pow X.Gm ξ hiso, hut]
    congr 1; ring
  have hk := hkill t ht htint (γ ^ n) hγn
  rw [map_pow] at hk
  have h2 : n • Multiplicative.toAdd (φ γ) = 0 := by
    rw [← toAdd_pow, hk, toAdd_one]
  rw [nsmul_eq_mul, mul_eq_zero] at h2
  rcases h2 with h2 | h2
  · exact absurd (by exact_mod_cast h2) hnpos
  · exact Multiplicative.toAdd.injective (by rw [h2, toAdd_one])

end GlobalTheory.UnipKill
