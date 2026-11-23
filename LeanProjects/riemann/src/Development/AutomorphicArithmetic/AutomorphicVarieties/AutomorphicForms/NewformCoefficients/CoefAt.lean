import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.CuspCritAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.Places

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V.Sd UpperTheory.V.Af UpperTheory.V.Af.Nf

private theorem ord_diff (w : HeightOneSpectrum (𝓞 ℚ)) : ordI w (differentIdeal ℤ (𝓞 ℚ)) = 0 := by
  have h : differentIdeal ℤ (𝓞 ℚ) = ⊤ := by
    rw [← Ideal.absNorm_eq_one_iff, absNorm_differentIdeal ℚ (𝓞 ℚ), discr_rat]; rfl
  rw [h, ordI, ← Ideal.one_eq_top, Associates.mk_one, Associates.factors_one, Associates.count_zero w.associates_irreducible]

private theorem eq_of_ord {I J : Ideal (𝓞 ℚ)} (hI : I ≠ ⊥) (hJ : J ≠ ⊥) (h : ∀ w, ordI w I = ordI w J) : I = J := by
  rw [← Ideal.finprod_heightOneSpectrum_factorization hI, ← Ideal.finprod_heightOneSpectrum_factorization hJ]
  refine finprod_congr fun w => ?_
  exact congrArg (fun n => w.asIdeal ^ n) (h w)

private theorem val_unit {u : (Af ℚ)ˣ} (hu : IsZU u) (w : HeightOneSpectrum (𝓞 ℚ)) :
    Valued.v (pLoc ℚ w (u : Af ℚ)) = 1 := by
  have h1 : Valued.v (pLoc ℚ w (u : Af ℚ)) ≤ 1 := Subring.mem_iInf.1 hu.1 w
  have h2 : Valued.v (pLoc ℚ w ((u⁻¹ : (Af ℚ)ˣ) : Af ℚ)) ≤ 1 := Subring.mem_iInf.1 hu.2 w
  have h3 : Valued.v (pLoc ℚ w (u : Af ℚ)) * Valued.v (pLoc ℚ w ((u⁻¹ : (Af ℚ)ˣ) : Af ℚ)) = 1 := by
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  refine le_antisymm h1 ?_
  calc 1 = _ := h3.symm
    _ ≤ Valued.v (pLoc ℚ w (u : Af ℚ)) * 1 := mul_le_mul_right h2 _
    _ = _ := mul_one _

private theorem genD_iff (q : ℚ) {u : (Af ℚ)ˣ} (hu : IsZU u) (𝔪 : Ideal (𝓞 ℚ)) :
    GenD (algebraMap ℚ (Af ℚ) q * (u : Af ℚ)) 𝔪 ↔
      𝔪 ≠ ⊥ ∧ ∀ w : HeightOneSpectrum (𝓞 ℚ), w.valuation ℚ q = WithZero.exp (-(ordI w 𝔪 : ℤ)) := by
  refine and_congr_right fun _ => forall_congr' fun w => ?_
  have h : Valued.v (pLoc ℚ w (algebraMap ℚ (Af ℚ) q)) = w.valuation ℚ q :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w q
  rw [map_mul, map_mul, val_unit hu, mul_one, h, ord_diff, Nat.cast_zero, zero_sub]

private theorem val_nat {n : ℕ} (hn : n ≠ 0) (w : HeightOneSpectrum (𝓞 ℚ)) :
    w.valuation ℚ (n : ℚ) = WithZero.exp (-(ordI w (Ideal.span {(n : 𝓞 ℚ)}) : ℤ)) := by
  rw [← map_natCast (algebraMap (𝓞 ℚ) ℚ) n, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.intValuation_if_neg w (Nat.cast_ne_zero.2 hn)]
  rfl

theorem UpperTheory.V.Af.Nf.coefAt :
    UpperTheory.V.Af.Nf.CoefAt := by
  intro a q hq u hu
  by_cases hd : q.den = 1
  · rw [if_pos hd]
    have hnum : 0 < q.num := Rat.num_pos.2 hq
    have hn : q.num.toNat ≠ 0 := by omega
    have hqn : q = (q.num.toNat : ℚ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hnum.le]
      exact ((Rat.den_eq_one_iff q).1 hd).symm
    have hb : Ideal.span {((q.num.toNat : ℕ) : 𝓞 ℚ)} ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]; exact Nat.cast_ne_zero.2 hn
    have hv : ∀ w : HeightOneSpectrum (𝓞 ℚ),
        w.valuation ℚ q = WithZero.exp (-(ordI w (Ideal.span {((q.num.toNat : ℕ) : 𝓞 ℚ)}) : ℤ)) := fun w => by
      rw [← val_nat hn w, ← hqn]
    have hex : ∃ 𝔪, GenD (algebraMap ℚ (Af ℚ) q * (u : Af ℚ)) 𝔪 := ⟨_, (genD_iff q hu _).2 ⟨hb, hv⟩⟩
    obtain ⟨h1, h2⟩ := (genD_iff q hu _).1 hex.choose_spec
    have he : hex.choose = Ideal.span {((q.num.toNat : ℕ) : 𝓞 ℚ)} := eq_of_ord h1 hb fun w => by
      have := WithZero.exp_injective ((h2 w).symm.trans (hv w))
      omega
    rw [UpperTheory.V.Sd.coefAt, dif_pos hex, he, Ideal.absNorm_span_natCast, RingOfIntegers.rank, Module.finrank_self, pow_one]
  · rw [if_neg hd, UpperTheory.V.Sd.coefAt, dif_neg]
    rintro ⟨𝔪, h⟩
    obtain ⟨r, hr⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 ℚ) ℚ q fun w => by
      rw [((genD_iff q hu _).1 h).2 w, ← WithZero.exp_zero, WithZero.exp_le_exp]
      omega
    obtain ⟨m, rfl⟩ := Rat.ringOfIntegersEquiv.symm.surjective r
    apply hd
    rw [← hr, eq_intCast Rat.ringOfIntegersEquiv.symm m, map_intCast]
    rfl
