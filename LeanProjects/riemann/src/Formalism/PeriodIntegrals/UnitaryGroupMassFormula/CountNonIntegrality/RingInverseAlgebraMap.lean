import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountNonIntegrality.LGDefs

noncomputable section

namespace PI.CntNotIntW

open NumberField IsDedekindDomain Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem star_coeF (D : Formalism.BasicNotions.D7) (t : D.host.F) : star (t : D.host.E) = t := by
  haveI := D.host.isCMField_hostE
  first
  | exact (NumberField.IsCMField.complexConj_eq_self_iff _).mpr t.2
  | exact (NumberField.IsCMField.complexConj_eq_self_iff (K := D.host.E) (t : D.host.E)).mpr t.2
  | exact NumberField.IsCMField.complexConj_apply_of_mem_maximalRealSubfield t.2
  | exact NumberField.IsCMField.complexConj_apply_eq_self_of_mem t.2
  | exact (NumberField.IsCMField.star_eq_self_iff _).mpr t.2
  | exact (NumberField.IsCMField.mem_maximalRealSubfield_iff_star_eq _).mp t.2
  | exact (NumberField.IsCMField.complexConj D.host.E).commutes t

theorem resChar_mem' (D : Formalism.BasicNotions.D7) (p : PlF D) : ((Loc.resChar p : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  first
  | exact ringChar.Nat.cast_ringChar
  | (unfold Loc.resChar; exact ringChar.Nat.cast_ringChar)

theorem val_resChar_lt (D : Formalism.BasicNotions.D7) (p : PlF D) :
    valuation (D.s.atP p).Fp (((Loc.resChar p : ℕ) : (D.s.atP p).Fp)) < 1 := by
  have hmem := resChar_mem' D p
  have h1 : ((Loc.resChar p : ℕ) : (D.s.atP p).Fp) =
      (D.s.atP p).ιF ((Loc.resChar p : ℕ) : D.host.F) := (map_natCast _ _).symm
  rw [h1]
  have hv : p.valuation D.host.F ((Loc.resChar p : ℕ) : D.host.F) < 1 := by
    have := (p.valuation_lt_one_iff_mem (K := D.host.F) ((Loc.resChar p : ℕ) : 𝓞 D.host.F)).mpr hmem
    simpa using this
  have hnot : ¬ ((D.s.atP p).ιF 1 ≤ᵥ (D.s.atP p).ιF ((Loc.resChar p : ℕ) : D.host.F)) := by
    rw [(D.s.atP p).val, map_one]
    exact not_le.mpr hv
  rw [map_one] at hnot
  rw [← not_le, ← map_one (valuation (D.s.atP p).Fp)]
  first
  | exact fun h => hnot ((Valuation.Compatible.vle_iff_le (v := valuation (D.s.atP p).Fp) _ _).mpr h)
  | exact fun h => hnot ((Valuation.Compatible.rel_iff_le (v := valuation (D.s.atP p).Fp) _ _).mpr h)
  | exact fun h => hnot (ValuativeRel.valuation_le_valuation.mp h)
  | exact fun h => hnot ((ValuativeRel.valuation_le_valuation_iff _ _).mp h)
  | simpa using hnot
  | simpa [ValuativeRel.valuation_le_valuation] using hnot

theorem locDiff_of (hT : TrDual) (hA : DualApprox) (hS : PowSmall) : LocDiff := by
  intro D δ M hag p
  haveI := (D.s.atP p).lf
  haveI := (D.s.atP p).ellPrime
  have hδ : δ p ≠ 0 := (hag p).2.1
  have hz := hT D δ M hag p
  obtain ⟨k, hk⟩ := hS (D.s.atP p).Fp (δ p) ((Loc.resChar p : ℕ) : (D.s.atP p).Fp) (val_resChar_lt D p)
  obtain ⟨t, htr, μ, hμ, hι⟩ := hA D.host.F p (D.s.atP p).Fp (D.s.atP p).qlCont (D.s.atP p).qlFin
    (D.s.atP p).ιF (D.s.atP p).dense (D.s.atP p).val (δ p)⁻¹ hz k
  refine ⟨t, htr, ?_⟩
  have he : δ p * (D.s.atP p).ιF t =
      1 + ((Loc.resChar p : ℕ) : (D.s.atP p).Fp) ^ k * δ p * μ := by
    rw [hι, mul_add, mul_inv_cancel₀ hδ]
    ring
  have hμ' : valuation (D.s.atP p).Fp μ ≤ 1 := (Valuation.mem_integer_iff _ _).mp hμ
  have hwv : valuation (D.s.atP p).Fp (((Loc.resChar p : ℕ) : (D.s.atP p).Fp) ^ k * δ p * μ) < 1 := by
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' hμ') hk
  have h1 : valuation (D.s.atP p).Fp (1 + ((Loc.resChar p : ℕ) : (D.s.atP p).Fp) ^ k * δ p * μ) = 1 := by
    rw [Valuation.map_add_eq_of_lt_left _ (by rwa [map_one]), map_one]
  rw [he]
  refine ⟨?_, ?_, ?_⟩
  · intro h0
    have h2 := congrArg (valuation (D.s.atP p).Fp) h0
    rw [h1, map_zero] at h2
    exact one_ne_zero h2
  · exact (Valuation.mem_integer_iff _ _).mpr (le_of_eq h1)
  · exact (Valuation.mem_integer_iff _ _).mpr (by rw [map_inv₀, h1, inv_one])

theorem unitAt_mul_natCast (D : Formalism.BasicNotions.D7) (p : PlF D) : ∃ n : ℕ, (uP p : ℚ) * n = 1 := by
  have h0 : (D.host.g 0 : ℚ) ≠ 0 := by exact_mod_cast (D.host.g_prime 0).ne_zero
  have h1 : (D.host.g 1 : ℚ) ≠ 0 := by exact_mod_cast (D.host.g_prime 1).ne_zero
  unfold uP gpart Lat.gS
  split_ifs with ha hb
  · refine ⟨D.host.g 1, ?_⟩
    push_cast
    first
    | (field_simp; done)
    | (field_simp; ring)
  · refine ⟨D.host.g 0, ?_⟩
    push_cast
    first
    | (field_simp; done)
    | (field_simp; ring)
  · refine ⟨D.host.g 0 * D.host.g 1, ?_⟩
    push_cast
    first
    | (field_simp; done)
    | (field_simp; ring)

theorem algMap_mem_O (D : Formalism.BasicNotions.D7) (p : PlF D) (c : (D.s.atP p).Fp) (hc : c ∈ 𝒪[(D.s.atP p).Fp]) :
    algebraMap (D.s.atP p).Fp (D.s.atP p).Ep c ∈ (D.s.atP p).O := by
  rw [(D.s.atP p).O_def]
  have e : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep c =
      algebraMap 𝒪[(D.s.atP p).Fp] (D.s.atP p).Ep ⟨c, hc⟩ := rfl
  rw [e]
  exact isIntegral_algebraMap

theorem ringInverse_algebraMap {A B : Type*} [Field A] [CommRing B] [Algebra A B] (y : A) (hy : y ≠ 0) :
    Ring.inverse (algebraMap A B y) = algebraMap A B y⁻¹ := by
  have h := Ring.inverse_unit (Units.map (algebraMap A B : A →* B) (Units.mk0 y hy))
  simpa using h

theorem locGen_of (hD : LocDiff) (hP : DualPow) : LocGen := by
  intro D δ M hag p m
  obtain ⟨t, htr, hu0, -, hinv⟩ := hD D δ M hag p
  obtain ⟨n, hn⟩ := unitAt_mul_natCast D p
  have hx : ((t : D.host.E) * (n : D.host.E)) ^ m ∈
      ((ddS D) ^ (-(m : ℤ)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
    rw [mul_pow]
    have h := Submodule.smul_mem
      ((ddS D) ^ (-(m : ℤ)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E).coeToSubmodule
      ((n : 𝓞 D.host.E) ^ m) (hP D t htr m)
    rw [Algebra.smul_def] at h
    simpa [mul_comm] using h
  have hstar : star (((t : D.host.E) * (n : D.host.E)) ^ m) = ((t : D.host.E) * (n : D.host.E)) ^ m := by
    rw [star_pow, star_mul', star_coeF D t, star_natCast]
  have hnE : ((uP p : ℚ) : D.host.E) * (n : D.host.E) = 1 := by
    have h := congrArg (fun q : ℚ => (q : D.host.E)) hn
    simpa using h
  have ha : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p) * (D.s.atP p).ιE (t : D.host.E) =
      algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p * (D.s.atP p).ιF t) := by
    show algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p) *
      (D.s.atP p).ιE (algebraMap D.host.F D.host.E t) = _
    rw [(D.s.atP p).compat t, ← map_mul]
  have key : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p) * (D.s.atP p).ιE (uP p : D.host.E) *
      algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p * (D.s.atP p).ιF t)⁻¹ *
      ((D.s.atP p).ιE (t : D.host.E) * (D.s.atP p).ιE (n : D.host.E)) = 1 := by
    have e1 : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p) * (D.s.atP p).ιE (uP p : D.host.E) *
        algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p * (D.s.atP p).ιF t)⁻¹ *
        ((D.s.atP p).ιE (t : D.host.E) * (D.s.atP p).ιE (n : D.host.E)) =
        (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p) * (D.s.atP p).ιE (t : D.host.E)) *
        algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p * (D.s.atP p).ιF t)⁻¹ *
        ((D.s.atP p).ιE (uP p : D.host.E) * (D.s.atP p).ιE (n : D.host.E)) := by ring
    rw [e1, ha, ← map_mul (D.s.atP p).ιE, hnE, map_one, mul_one, ← map_mul, mul_inv_cancel₀ hu0, map_one]
  have alg : ∀ (R : Type) [CommRing R] (a b c d e : R), a * b * c * (d * e) = 1 →
      (a * b) ^ m * (c ^ m * (d * e) ^ m) = 1 := by
    intro R _ a b c d e h
    calc (a * b) ^ m * (c ^ m * (d * e) ^ m) = (a * b * c * (d * e)) ^ m := by ring
      _ = 1 := by rw [h, one_pow]
  have hprod : (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p) * (D.s.atP p).ιE (uP p : D.host.E)) ^ m *
      ((algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p * (D.s.atP p).ιF t)⁻¹) ^ m *
        (D.s.atP p).ιE (((t : D.host.E) * (n : D.host.E)) ^ m)) = 1 := by
    rw [map_pow, map_mul]
    exact alg _ _ _ _ _ _ key
  refine ⟨((t : D.host.E) * (n : D.host.E)) ^ m, hx, hstar,
    (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p * (D.s.atP p).ιF t)⁻¹) ^ m,
    Subring.pow_mem _ (algMap_mem_O D p _ hinv) m, ?_⟩
  exact Ring.inverse_unit ⟨_, _, hprod, by rw [mul_comm]; exact hprod⟩

end PI.CntNotIntW
