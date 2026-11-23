import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.IntegralDeterminants.PlaceConjAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.IntegralDeterminants.PlaceHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharFinprodLocKMulInfEqOne
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsPowLocKMulInf
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContinuousIdeleCharLocalFactorization
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsDvrFrobeniusLift

open NumberField IsDedekindDomain Matrix Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.GalOfCusp UpperTheory.V.Af
open scoped Classical

namespace UpperTheory.V.Z.Int

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E]

private theorem locK_level (κ : HChar E) (v : HeightOneSpectrum (𝓞 E)) :
    ∃ n : ℕ, ∀ y : Eˣ, v.valuation E ((y : E) - 1) ≤ WithZero.exp (-(n : ℤ)) → κ.locK v y = 1 := by
  obtain ⟨-, hlev, -⟩ := GlobalTheory.HeckeSplit.continuous_char_factor E κ.1 κ.2.1
  obtain ⟨n, hn⟩ := hlev v
  refine ⟨n, fun y hy => hn (atFin v y) ?_⟩
  have e : ((atFin v y : (v.adicCompletion E)ˣ) : v.adicCompletion E) - 1 =
      algebraMap E (v.adicCompletion E) ((y : E) - 1) := by
    rw [map_sub, map_one]
    rfl
  rw [e]
  exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _).le.trans hy

private theorem pow_congr_one (v : HeightOneSpectrum (𝓞 E)) (n : ℕ) :
    ∃ m : ℕ, 0 < m ∧ ∀ r : 𝓞 E, r ∉ v.asIdeal → r ^ m - 1 ∈ v.asIdeal ^ (n + 1) := by
  set J := v.asIdeal ^ (n + 1) with hJ
  have hfin : Finite (𝓞 E ⧸ J) := Ideal.finiteQuotientOfFreeOfNeBot _ (pow_ne_zero _ v.ne_bot)
  refine ⟨Nat.card (𝓞 E ⧸ J)ˣ, Nat.card_pos, fun r hr => ?_⟩
  obtain ⟨y, i, hi, e⟩ := v.isMaximal.exists_inv hr
  have hunit : IsUnit (Ideal.Quotient.mk J r) := by
    refine IsUnit.of_mul_eq_one (Ideal.Quotient.mk J (y * ∑ j ∈ Finset.range (n + 1), i ^ j)) ?_
    rw [← map_mul, ← map_one (Ideal.Quotient.mk J), Ideal.Quotient.eq]
    have hg := mul_neg_geom_sum i (n + 1)
    have hyr : y * r = 1 - i := by linear_combination e
    have hval : r * (y * ∑ j ∈ Finset.range (n + 1), i ^ j) - 1 = -(i ^ (n + 1)) := by
      calc r * (y * ∑ j ∈ Finset.range (n + 1), i ^ j) - 1
          = (y * r) * (∑ j ∈ Finset.range (n + 1), i ^ j) - 1 := by ring
        _ = -(i ^ (n + 1)) := by rw [hyr, hg]; ring
    rw [hval]
    exact neg_mem (Ideal.pow_mem_pow hi _)
  have h1 := congrArg Units.val (pow_card_eq_one' (x := hunit.unit))
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, map_one, sub_eq_zero]
  rwa [Units.val_pow_eq_pow_val, IsUnit.unit_spec, Units.val_one] at h1

private theorem locK_finite_order (κ : HChar E) (v : HeightOneSpectrum (𝓞 E)) :
    ∃ m : ℕ, 0 < m ∧ ∀ u : Eˣ, v.valuation E (u : E) = 1 → κ.locK v u ^ m = 1 := by
  obtain ⟨n, hn⟩ := locK_level κ v
  obtain ⟨m, hm, H⟩ := pow_congr_one v n
  refine ⟨m, hm, fun u hu => ?_⟩
  obtain ⟨r, s, hs, hrs⟩ := (GlobalTheory.UnramCompletion.intAt_iff v (u : E)).2 hu.le
  have hs1 : v.valuation E (algebraMap (𝓞 E) E s) = 1 :=
    (HeightOneSpectrum.valuation_eq_one_iff_notMem v).2 hs
  have hr1 : v.valuation E (algebraMap (𝓞 E) E r) = 1 := by
    rw [← hrs, map_mul, hs1, hu, one_mul]
  have hr : r ∉ v.asIdeal := (HeightOneSpectrum.valuation_eq_one_iff_notMem v).1 hr1
  have hmem : r ^ m - s ^ m ∈ v.asIdeal ^ (n + 1) := by
    simpa using (v.asIdeal ^ (n + 1)).sub_mem (H r hr) (H s hs)
  have hle : v.valuation E (algebraMap (𝓞 E) E (r ^ m - s ^ m)) ≤ WithZero.exp (-((n + 1 : ℕ) : ℤ)) := by
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    exact (v.intValuation_le_pow_iff_mem _ _).2 hmem
  have e : algebraMap (𝓞 E) E (r ^ m - s ^ m) = algebraMap (𝓞 E) E s ^ m * (((u ^ m : Eˣ) : E) - 1) := by
    rw [map_sub, map_pow, map_pow, ← hrs, Units.val_pow_eq_pow_val]
    ring
  rw [e, map_mul, map_pow, hs1, one_pow, one_mul] at hle
  rw [← map_pow]
  refine hn _ (hle.trans ?_)
  rw [WithZero.exp_le_exp]
  push_cast
  omega

private theorem isUnitAt_atFin (v : HeightOneSpectrum (𝓞 E)) (y : Eˣ) (hy : v.valuation E (y : E) = 1) :
    IsUnitAt v (atFin v y) :=
  (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (y : E)).trans hy

end SlopeTestRemainingChoices

section Nu

variable {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ)

private noncomputable def nuHom : ℂ →*₀ ℝ where
  toFun := nu ι
  map_zero' := by simp [nu]
  map_one' := by simp [nu]
  map_mul' x y := by simp [nu]

private theorem nuHom_apply (x : ℂ) : nuHom ι x = nu ι x := rfl

private theorem nu_eq_one {E : Type} [Field E] [NumberField E] {φ : E →+* ℂ}
    {u : HeightOneSpectrum (𝓞 E)} {ψ : u.adicCompletion E →+* ℂ}
    (hψ : ∀ x : E, ψ (algebraMap E _ x) = φ x) (hb : ∀ x, nu ι (ψ x) ≤ 1 ↔ Valued.v x ≤ 1)
    (y : Eˣ) (hy : u.valuation E (y : E) = 1) : nu ι (φ (y : E)) = 1 := by
  have hle : ∀ t : Eˣ, u.valuation E (t : E) = 1 → nu ι (φ (t : E)) ≤ 1 := fun t ht => by
    rw [← hψ]
    exact (hb _).2 (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' u (t : E) ▸ ht.le)
  have h1 := hle y hy
  have h2 := hle y⁻¹ (by rw [Units.val_inv_eq_inv_val, map_inv₀, hy, inv_one])
  have h3 : nu ι (φ (y : E)) * nu ι (φ ((y⁻¹ : Eˣ) : E)) = 1 := by
    rw [← nuHom_apply, ← nuHom_apply, ← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  have h4 : 0 ≤ nu ι (φ (y : E)) := norm_nonneg _
  nlinarith

end Nu

end UpperTheory.V.Z.Int

theorem UpperTheory.V.Z.Int.charVal :
    UpperTheory.V.Z.Int.CharVal := by
  intro l _ ι E _ _ _ κ m hκ w hw

  obtain ⟨h, a, hh, haw, hav⟩ := GlobalTheory.TamePow.exists_gen w
  choose o ho hou using fun v => locK_finite_order κ v
  have hfinS := Filter.eventually_cofinite.mp (Formalism.L2.Fam.IdTrans.unrAe κ)
  set S := hfinS.toFinset with hS
  set M := ∏ v ∈ S, o v with hM
  have hMpos : 0 < M := Finset.prod_pos fun v _ => ho v
  set N := h * M with hN
  have hNpos : 0 < N := Nat.mul_pos hh hMpos
  set z : Eˣ := a ^ M with hz

  have hzv : ∀ v, v ≠ w → v.valuation E (z : E) = 1 := fun v hv => by
    rw [hz, Units.val_pow_eq_pow_val, map_pow, hav v hv, one_pow]
  have hunif : w.valuation E ((unif w : Eˣ) : E) = WithZero.exp (-1 : ℤ) :=
    (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _).symm.trans (unif_spec w)
  set y : Eˣ := z / unif w ^ N with hy
  have hyw : w.valuation E (y : E) = 1 := by
    rw [hy, Units.val_div_eq_div_val, map_div₀, hz, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val,
      map_pow, map_pow, haw, hunif, ← WithZero.exp_nsmul, ← WithZero.exp_nsmul, hN]
    rw [div_eq_one_iff_eq (by simp)]
    congr 1
    simp only [smul_eq_mul, nsmul_eq_mul]
    push_cast
    ring
  have hzy : z = y * unif w ^ N := by rw [hy, div_mul_cancel]

  have hloc : ∀ v, v ≠ w → κ.locK v z = 1 := fun v hv => by
    by_cases hvS : v ∈ S
    · obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem o hvS
      have hva : v.valuation E (a : E) = 1 := hav v hv
      rw [hz, map_pow, hM, hc, pow_mul, hou v a hva, one_pow]
    · have hU : κ.UnrAt v := by
        by_contra hn
        exact hvS (by rw [hS, Set.Finite.mem_toFinset]; exact hn)
      exact hU _ (isUnitAt_atFin v z (hzv v hv))
  have hlocw : κ.locK w z = κ.val w ^ N := by
    have e : κ.locK w y = 1 := hw _ (isUnitAt_atFin w y hyw)
    rw [hzy, map_mul, map_pow, e, one_mul]
    rfl
  obtain ⟨-, hp⟩ := GlobalTheory.HCharUnit.finprod_locK_mul_inf E κ z
  rw [finprod_eq_single _ w fun v hv => hloc v hv, hlocw] at hp
  have hC : (κ.val w : ℂ) ^ N * ∏ φ : E →+* ℂ, φ (z : E) ^ m φ = 1 := by
    have := congrArg Units.val hp
    rw [Units.val_mul, Units.val_pow_eq_pow_val, hκ z, Units.val_one] at this
    exact this

  have hterm : ∀ φ : E →+* ℂ, nu ι (φ (z : E)) ^ m φ =
      if φ ∈ Ov ι w then (nu ι (φ ((unif w : Eˣ) : E)) ^ m φ) ^ N else 1 := fun φ => by
    obtain ⟨u, ψ, hψ, hb, hOv⟩ := placeHom l ι E φ
    split_ifs with hφ
    · have hu : w = u := (hOv w).1 hφ
      subst hu
      have h1 := nu_eq_one ι hψ hb y hyw
      have h2 : nu ι (φ (z : E)) = nu ι (φ ((unif w : Eˣ) : E)) ^ N := by
        rw [hzy, ← nuHom_apply, Units.val_mul, map_mul, map_mul, nuHom_apply, h1, one_mul,
          Units.val_pow_eq_pow_val, map_pow, map_pow, nuHom_apply]
      rw [h2, ← zpow_natCast, ← zpow_natCast, ← _root_.zpow_mul, ← _root_.zpow_mul, mul_comm]
    · have hu : u ≠ w := fun e => hφ ((hOv w).2 e.symm)
      rw [nu_eq_one ι hψ hb z (hzv u hu), _root_.one_zpow]
  have hR : (nu ι (κ.val w : ℂ) * ∏ τ ∈ Ov ι w, nu ι (τ ((unif w : Eˣ) : E)) ^ m τ) ^ N = 1 := by
    have h1 := congrArg (nuHom ι) hC
    rw [map_mul, map_pow, map_prod, map_one] at h1
    simp only [map_zpow₀, nuHom_apply] at h1
    rw [Finset.prod_congr rfl fun φ _ => hterm φ, Finset.prod_ite_mem, Finset.univ_inter,
      Finset.prod_pow] at h1
    rw [mul_pow]
    exact h1
  have hnn : 0 ≤ nu ι (κ.val w : ℂ) * ∏ τ ∈ Ov ι w, nu ι (τ ((unif w : Eˣ) : E)) ^ m τ :=
    mul_nonneg (norm_nonneg _) (Finset.prod_nonneg fun τ _ => zpow_nonneg (norm_nonneg _) _)
  exact (pow_eq_one_iff_of_nonneg hnn hNpos.ne').1 hR
