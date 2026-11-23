import Mathlib
import Formalism.LocalToGlobal.NormalizedHeckeFactors.RingHomOfBaseOrderToFraction
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemZpowersOfTameGen
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTameGenAtOfValuationSubring
open NumberField IsDedekindDomain

open Pointwise

namespace GlobalTheory.TameMove

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]

theorem val_smul_lt_one_iff (A : ValuationSubring Ω) (g : Formalism.ConjugateSelfDual.G E Ω) (y : Ω) :
    (g • A).valuation (g y) < 1 ↔ A.valuation y < 1 := by
  have h1 : ∀ z : Ω, g z ∈ g • A ↔ z ∈ A := by
    intro z
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def,
      ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
  rw [ReciprocityTheory.Gal.valuation_lt_one_iff', ReciprocityTheory.Gal.valuation_lt_one_iff', h1, ← map_inv₀, h1,
    map_eq_zero_iff _ g.injective]

theorem val_smul_le_one_iff (A : ValuationSubring Ω) (g : Formalism.ConjugateSelfDual.G E Ω) (y : Ω) :
    (g • A).valuation (g y) ≤ 1 ↔ A.valuation y ≤ 1 := by
  rw [ValuationSubring.valuation_le_one_iff, ValuationSubring.valuation_le_one_iff,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def,
    ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]

theorem conj_mem_Ine_smul {A : ValuationSubring Ω} {g σ : Formalism.ConjugateSelfDual.G E Ω}
    (hσ : σ ∈ ReciprocityTheory.Gal.Ine (F := E) A) : g * σ * g⁻¹ ∈ ReciprocityTheory.Gal.Ine (F := E) (g • A) := by
  refine ⟨?_, fun x hx => ?_⟩
  · show (g * σ * g⁻¹) • (g • A) = g • A
    have h : σ • A = A := hσ.1
    rw [← mul_smul, inv_mul_cancel_right, mul_smul, h]
  · have hy : A.valuation (g⁻¹ x) ≤ 1 := by
      rw [← val_smul_le_one_iff A g, ReciprocityTheory.Gal.mul_inv_apply]; exact hx
    have e : (g * σ * g⁻¹) x - x = g (σ (g⁻¹ x) - g⁻¹ x) := by
      rw [map_sub, ReciprocityTheory.Gal.mul_inv_apply]; rfl
    rw [e, val_smul_lt_one_iff]
    exact hσ.2 _ hy

theorem exists_mul_eq_of_not_mem_sq (P : HeightOneSpectrum (𝓞 E)) {ϖ ϖ₀ : 𝓞 E}
    (h₀ : ϖ₀ ∈ P.asIdeal) (h : ϖ ∈ P.asIdeal) (h2 : ϖ ∉ P.asIdeal ^ 2) :
    ∃ s t : 𝓞 E, s ∉ P.asIdeal ∧ s * ϖ₀ = t * ϖ := by
  have hle : Ideal.span {ϖ} ≤ P.asIdeal := (Ideal.span_singleton_le_iff_mem _).mpr h
  obtain ⟨I, hI⟩ := Ideal.dvd_iff_le.mpr hle
  have hIP : ¬ I ≤ P.asIdeal := by
    intro hIP
    apply h2
    have : Ideal.span {ϖ} ≤ P.asIdeal ^ 2 := by
      rw [hI, pow_two]; exact Ideal.mul_mono_right hIP
    exact this (Ideal.mem_span_singleton_self ϖ)
  obtain ⟨s, hsI, hsP⟩ := Set.not_subset.mp hIP
  have hm : s * ϖ₀ ∈ Ideal.span {ϖ} := by
    rw [hI, mul_comm s]; exact Ideal.mul_mem_mul h₀ hsI
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp hm
  exact ⟨s, t, hsP, ht.symm⟩

theorem val_le_one (A : ValuationSubring Ω) (t : 𝓞 E) : A.valuation (algebraMap E Ω (t : E)) ≤ 1 := by
  rw [A.valuation_le_one_iff]
  apply ReciprocityTheory.Gal.mem_of_isIntegral_int
  exact (NumberField.RingOfIntegers.isIntegral_coe t).map (algebraMap E Ω).toIntAlgHom

theorem val_eq_of_not_mem_sq (A : ValuationSubring Ω) (P : HeightOneSpectrum (𝓞 E))
    (hA : Formalism.ConjugateSelfDual.IsPlaceOver A P) {ϖ ϖ₀ : 𝓞 E} (h : ϖ ∈ P.asIdeal) (h2 : ϖ ∉ P.asIdeal ^ 2)
    (h₀ : ϖ₀ ∈ P.asIdeal) (h02 : ϖ₀ ∉ P.asIdeal ^ 2) :
    A.valuation (algebraMap E Ω (ϖ : E)) = A.valuation (algebraMap E Ω (ϖ₀ : E)) := by
  have key : ∀ a b : 𝓞 E, a ∈ P.asIdeal → b ∈ P.asIdeal → b ∉ P.asIdeal ^ 2 →
      A.valuation (algebraMap E Ω (a : E)) ≤ A.valuation (algebraMap E Ω (b : E)) := by
    intro a b ha hb hb2
    obtain ⟨s, t, hs, hst⟩ := exists_mul_eq_of_not_mem_sq P ha hb hb2
    have hvs : A.valuation (algebraMap E Ω (s : E)) = 1 :=
      le_antisymm (val_le_one A s) (not_lt.mp fun hlt => hs ((hA s).mp hlt))
    have e : algebraMap E Ω (s : E) * algebraMap E Ω (a : E) =
        algebraMap E Ω (t : E) * algebraMap E Ω (b : E) := by
      have := congrArg (fun z : 𝓞 E => algebraMap E Ω (z : E)) hst
      simpa using this
    have e2 := congrArg A.valuation e
    rw [Valuation.map_mul, Valuation.map_mul, hvs, one_mul] at e2
    rw [e2]
    calc A.valuation (algebraMap E Ω (t : E)) * A.valuation (algebraMap E Ω (b : E))
        ≤ 1 * A.valuation (algebraMap E Ω (b : E)) := mul_le_mul_left (val_le_one A t) _
      _ = _ := one_mul _
  exact le_antisymm (key _ _ h h₀ h02) (key _ _ h₀ h h2)

end GlobalTheory.TameMove

open Pointwise

namespace GlobalTheory.TameMove

theorem tameRep_move : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (P : HeightOneSpectrum (𝓞 E)) (e : ℤ) (σ : Formalism.ConjugateSelfDual.G E Ω) (u : 𝓞 E) (A₀ : ValuationSubring Ω) (ϖ₀ : 𝓞 E) (π₀ : Ω),
    Formalism.ConjugateSelfDual.IsPlaceOver A₀ P → ϖ₀ ∈ P.asIdeal → ϖ₀ ∉ P.asIdeal ^ 2 →
    π₀ ^ (Formalism.ConjugateSelfDual.normV P - 1) = algebraMap E Ω (ϖ₀ : E) → Formalism.L2.NX.TameRep P e σ u →
    ∃ g : Formalism.ConjugateSelfDual.G E Ω, g * σ * g⁻¹ ∈ ReciprocityTheory.Gal.Ine (F := E) A₀ ∧
      A₀.valuation ((g * σ * g⁻¹) π₀ / π₀ - (algebraMap E Ω (u : E)) ^ e) < 1 := by
  intro E Ω _ _ _ _ _ P e σ u A₀ ϖ₀ π₀ hA₀ h₀ h02 hπ₀ hT
  obtain ⟨A, hA, hσ, ϖ, π, h, h2, hπ, hv⟩ := hT
  obtain ⟨g, rfl⟩ := ReciprocityTheory.Gal.exists_smul_eq_of_isPlaceOver hA hA₀
  have hσ'I : g * σ * g⁻¹ ∈ ReciprocityTheory.Gal.Ine (F := E) (g • A) := conj_mem_Ine_smul hσ
  refine ⟨g, hσ'I, ?_⟩
  set B := g • A with hB
  set σ' := g * σ * g⁻¹ with hσ'
  set N := Formalism.ConjugateSelfDual.normV P - 1 with hN
  set U := (algebraMap E Ω (u : E)) ^ e with hU
  have hne : ∀ b : 𝓞 E, b ∉ P.asIdeal ^ 2 → algebraMap E Ω (b : E) ≠ 0 := by
    intro b hb hz
    apply hb
    have hb0 : b = 0 := by
      have : (b : E) = 0 := (map_eq_zero_iff _ (algebraMap E Ω).injective).mp hz
      exact_mod_cast this
    rw [hb0]; exact Ideal.zero_mem _
  have hw : algebraMap E Ω (ϖ : E) ≠ 0 := hne ϖ h2
  have hw₀ : algebraMap E Ω (ϖ₀ : E) ≠ 0 := hne ϖ₀ h02
  have hN0 : N ≠ 0 := by
    intro hz
    rw [hz, pow_zero] at hπ₀
    have := (hA₀ ϖ₀).mpr h₀
    rw [← hπ₀, map_one] at this
    exact lt_irrefl _ this
  have hπ₀0 : π₀ ≠ 0 := by
    rintro rfl; rw [zero_pow hN0] at hπ₀; exact hw₀ hπ₀.symm

  have hπ' : (g π) ^ N = algebraMap E Ω (ϖ : E) := by
    rw [← map_pow, hπ]; exact AlgEquiv.commutes g _
  have hπ'0 : g π ≠ 0 := by
    intro hz; rw [hz, zero_pow hN0] at hπ'; exact hw hπ'.symm
  have hgg : g⁻¹ (g π) = π := by
    rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
  have ha : B.valuation (σ' (g π) / g π - U) < 1 := by
    have e1 : σ' (g π) / g π - U = g (σ π / π - U) := by
      have e2 : σ' (g π) = g (σ π) := by
        show g (σ (g⁻¹ (g π))) = g (σ π)
        rw [hgg]
      have e3 : g U = U := by
        rw [hU, map_zpow₀]; congr 1; exact AlgEquiv.commutes g _
      rw [map_sub, map_div₀, e2, e3]
    rw [e1, hB, val_smul_lt_one_iff]; exact hv

  set x := g π / π₀ with hx
  have hxπ : g π = x * π₀ := by rw [hx, div_mul_cancel₀ _ hπ₀0]
  have hx0 : x ≠ 0 := div_ne_zero hπ'0 hπ₀0
  have hvx : B.valuation x = 1 := by
    have hxN : x ^ N = algebraMap E Ω (ϖ : E) / algebraMap E Ω (ϖ₀ : E) := by
      rw [hx, div_pow, hπ', hπ₀]
    have hvN : B.valuation x ^ N = 1 := by
      rw [← Valuation.map_pow, hxN, map_div₀, val_eq_of_not_mem_sq B P hA₀ h h2 h₀ h02,
        div_self ((Valuation.ne_zero_iff _).mpr hw₀)]
    rcases lt_trichotomy (B.valuation x) 1 with h1 | h1 | h1
    · exact absurd hvN (pow_lt_one₀ zero_le h1 hN0).ne
    · exact h1
    · exact absurd hvN (one_lt_pow₀ h1 hN0).ne'
  have hc : B.valuation (σ' x / x - 1) < 1 := by
    have e : σ' x / x - 1 = (σ' x - x) / x := by field_simp
    rw [e, map_div₀, hvx, div_one]
    exact hσ'I.2 x hvx.le

  have hb : (σ' π₀ / π₀) ^ N = 1 := by
    rw [div_pow, ← map_pow, hπ₀, AlgEquiv.commutes, div_self hw₀]
  have hvb : B.valuation (σ' π₀ / π₀) = 1 := ReciprocityTheory.Gal.valuation_eq_one_of_pow_eq_one B hN0 hb
  have hprod : σ' (g π) / g π = (σ' x / x) * (σ' π₀ / π₀) := by
    rw [hxπ, map_mul]; field_simp
  have e4 : σ' π₀ / π₀ - U = (σ' (g π) / g π - U) + -((σ' x / x - 1) * (σ' π₀ / π₀)) := by
    rw [hprod]; ring
  rw [e4]
  refine Valuation.map_add_lt _ ha ?_
  rw [Valuation.map_neg, Valuation.map_mul, hvb, mul_one]
  exact hc

end GlobalTheory.TameMove
