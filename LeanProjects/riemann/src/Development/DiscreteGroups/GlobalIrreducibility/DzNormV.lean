import Mathlib
import Formalism.ConjugateSelfDual.Statement
import Development.DiscreteGroups.GlobalIrreducibility.ExistsOfMemKOne

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Filter Topology

set_option linter.all false

noncomputable section

namespace DiscreteGroups.sglob.DzType

variable {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (g : ℕ) [hg : Fact g.Prime]

theorem val_lt_one_of_norm_lt_one (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i) (u : ℚ_[g])
    (hu : ‖u‖ < 1) : Valued.v (i u) < 1 := by
  have := DiscreteGroups.sglob.DzIso.norm_lt_of_lt i hi hu
  rwa [Valued.toNormedField.norm_lt_one_iff] at this

theorem mem_of_val_lt_one (y : 𝓞 E) (h : Valued.v (algebraMap E (w.adicCompletion E) (y : E)) < 1) :
    y ∈ w.asIdeal := by
  rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := E)]
  have e : Valued.v (algebraMap E (w.adicCompletion E) (y : E)) = w.valuation E (y : E) :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (R := 𝓞 E) w (y : E)
  rwa [e] at h

theorem val_le_one_int (y : 𝓞 E) : Valued.v (algebraMap E (w.adicCompletion E) (y : E)) ≤ 1 := by
  have e : Valued.v (algebraMap E (w.adicCompletion E) (y : E)) = w.valuation E (y : E) :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (R := 𝓞 E) w (y : E)
  rw [e]
  exact w.valuation_le_one y

theorem alg_sub_natCast (y : 𝓞 E) (a : ℕ) : algebraMap E (w.adicCompletion E) (((y - (a : 𝓞 E) : 𝓞 E)) : E) =
    algebraMap E (w.adicCompletion E) (y : E) - (a : w.adicCompletion E) := by
  simp

theorem alg_natCast (a : ℕ) : algebraMap E (w.adicCompletion E) (((a : 𝓞 E)) : E) = (a : w.adicCompletion E) := by
  simp

theorem normV_eq_of_padic (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i) : normV w = g := by
  classical
  have hres : ∀ y : 𝓞 E, ∃ a : ℕ, y - (a : 𝓞 E) ∈ w.asIdeal := by
    intro y
    set x := i.symm (algebraMap E (w.adicCompletion E) (y : E)) with hx
    have hxy : i x = algebraMap E (w.adicCompletion E) (y : E) := by rw [hx, RingEquiv.apply_symm_apply]
    have hxn : ‖x‖ ≤ 1 := by
      by_contra hc
      push Not at hc
      have hx0 : x ≠ 0 := by intro h; rw [h, norm_zero] at hc; exact absurd hc (by norm_num)
      have h1 : ‖x⁻¹‖ < 1 := by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hc
      have h2 := val_lt_one_of_norm_lt_one w g i hi _ h1
      rw [map_inv₀, hxy, map_inv₀] at h2
      have h3 := val_le_one_int w y
      have hy0 : Valued.v (algebraMap E (w.adicCompletion E) (y : E)) ≠ 0 := by
        intro h0
        rw [h0, inv_zero] at h2
        have : i x ≠ 0 := (map_ne_zero i).mpr hx0
        rw [hxy] at this
        exact this ((Valuation.zero_iff _).mp h0)
      have h4 : 1 ≤ (Valued.v (algebraMap E (w.adicCompletion E) (y : E)))⁻¹ := one_le_inv₀ (zero_lt_iff.mpr hy0) |>.mpr h3
      exact absurd h2 (not_lt.mpr h4)
    let xz : ℤ_[g] := ⟨x, hxn⟩
    obtain ⟨a, -, ha⟩ := PadicInt.exists_mem_range xz
    refine ⟨a, mem_of_val_lt_one w _ ?_⟩
    have h5 : ‖x - a‖ < 1 := by
      have h := (PadicInt.mem_nonunits).mp ha
      rw [PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_natCast] at h
      exact h
    have h6 := val_lt_one_of_norm_lt_one w g i hi _ h5
    rw [map_sub, hxy, map_natCast] at h6
    rw [alg_sub_natCast]
    exact h6
  have hgw : ((g : ℕ) : 𝓞 E) ∈ w.asIdeal := by
    apply mem_of_val_lt_one w
    have := val_lt_one_of_norm_lt_one w g i hi (g : ℚ_[g]) Padic.norm_p_lt_one
    rw [map_natCast] at this
    rw [alg_natCast]
    exact this
  haveI : w.asIdeal.IsPrime := w.isPrime
  have hgQ : ((g : ℕ) : 𝓞 E ⧸ w.asIdeal) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk w.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
    exact hgw
  haveI : CharP (𝓞 E ⧸ w.asIdeal) g := (CharP.charP_iff_prime_eq_zero hg.out).mpr hgQ
  let f : ZMod g →+* 𝓞 E ⧸ w.asIdeal := ZMod.castHom (dvd_refl g) _
  have hinj : Function.Injective f := f.injective
  have hsurj : Function.Surjective f := by
    intro q
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective q
    obtain ⟨a, ha⟩ := hres y
    refine ⟨(a : ZMod g), ?_⟩
    rw [ZMod.castHom_apply, ZMod.cast_natCast (dvd_refl g), ← map_natCast (Ideal.Quotient.mk w.asIdeal),
      Ideal.Quotient.eq]
    rw [← neg_mem_iff, neg_sub]
    exact ha
  unfold normV
  rw [← Nat.card_congr (RingEquiv.ofBijective f ⟨hinj, hsurj⟩).toEquiv, Nat.card_zmod]

end DiscreteGroups.sglob.DzType

end
