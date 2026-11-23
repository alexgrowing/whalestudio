import Development.WeilBound.RepresentationTheoryGL.PeriodRingBases.PeriodRingUnits.DieudonneManinBasisModification
import GroundTheory.PAdicHodge.ExistsNormLeOfNormLtOneFinite

noncomputable section

namespace period_ring_base

open Formalism.Per6 hiding σB aB
open GroundTheory.PAdicHodge DeRhamPotentiallySemistable.DRPst PfDRPst Matrix

section cont

variable {l : ℕ} [Fact l.Prime]

local notation "φi" => RingEquiv.symm (_root_.frobeniusEquiv (PreTilt (normInteger ℂ_[l]) l) l)

theorem exists_coe_eq_untilt_pFlat (m : ℕ) : ∃ z : PadicAlgCl l,
    (z : ℂ_[l]) = ((PreTilt.untilt (φi^[m] (pFlat l)) : normInteger ℂ_[l]) : ℂ_[l]) := by
  have hN : l ^ m ≠ 0 := pow_ne_zero _ (Fact.out : l.Prime).ne_zero
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (l : PadicAlgCl l) (Nat.pos_of_ne_zero hN)
  have hπ : ((PreTilt.untilt (φi^[m] (pFlat l)) : normInteger ℂ_[l]) : ℂ_[l]) ^ l ^ m = (l : ℂ_[l]) := by
    rw [← SubmonoidClass.coe_pow, PreTilt.untilt_iterate_frobeniusEquiv_symm_pow, coe_untilt_pFlat]
  have hyl : algebraMap (PadicAlgCl l) ℂ_[l] y ^ l ^ m = (l : ℂ_[l]) := by
    rw [← map_pow, hy, map_natCast]
  have hy0 : algebraMap (PadicAlgCl l) ℂ_[l] y ≠ 0 := by
    intro h0
    rw [h0, zero_pow hN] at hyl
    exact natCast_p_ne_zero_cp (p := l) hyl.symm
  obtain ⟨w, hw⟩ := exists_coe_eq_of_pow_eq_one hN
    (x := ((PreTilt.untilt (φi^[m] (pFlat l)) : normInteger ℂ_[l]) : ℂ_[l]) * (algebraMap (PadicAlgCl l) ℂ_[l] y)⁻¹)
    (by rw [mul_pow, inv_pow, hπ, hyl, mul_inv_cancel₀ (natCast_p_ne_zero_cp (p := l))])
  refine ⟨y * w, ?_⟩
  change algebraMap (PadicAlgCl l) ℂ_[l] (y * w) = _
  rw [map_mul, show algebraMap (PadicAlgCl l) ℂ_[l] w = _ from hw, mul_comm, mul_assoc, inv_mul_cancel₀ hy0,
    mul_one]

theorem toZModPow_kummerC_eq (m : ℕ) {g h : GQ l} {z : PadicAlgCl l}
    (hz : (z : ℂ_[l]) = ((PreTilt.untilt (φi^[m] (pFlat l)) : normInteger ℂ_[l]) : ℂ_[l])) (hgh : h z = g z) :
    PadicInt.toZModPow m (kummerC (untilt_epsilon (p := l)) untilt_frobeniusEquiv_symm_epsilon_ne_one (toBot h)) =
      PadicInt.toZModPow m (kummerC (untilt_epsilon (p := l)) untilt_frobeniusEquiv_symm_epsilon_ne_one (toBot g)) := by
  have e : ∀ σ : GQ l, (toBot σ) • ((PreTilt.untilt (φi^[m] (pFlat l)) : normInteger ℂ_[l]) : ℂ_[l]) =
      ((PreTilt.untilt (φi^[m] (pFlat l)) : normInteger ℂ_[l]) : ℂ_[l]) *
        ((PreTilt.untilt (φi^[m] (epsilon l)) : normInteger ℂ_[l]) : ℂ_[l]) ^
          (PadicInt.toZModPow m (kummerC (untilt_epsilon (p := l)) untilt_frobeniusEquiv_symm_epsilon_ne_one
            (toBot σ))).val := fun σ =>
    gal_smul_untilt_iterate_of_eq_mul untilt_epsilon
      (tiltGal_eq_mul_epsPow untilt_epsilon untilt_frobeniusEquiv_symm_epsilon_ne_one pFlat_ne_zero
        gal_smul_coe_untilt_pFlat (toBot σ)) m
  have hs : ∀ σ : GQ l, (toBot σ) • ((PreTilt.untilt (φi^[m] (pFlat l)) : normInteger ℂ_[l]) : ℂ_[l]) =
      ((σ z : PadicAlgCl l) : ℂ_[l]) := fun σ => by
    rw [← hz, ← galCp_apply, galCp_coe]
    rfl
  have hπ0 : ((PreTilt.untilt (φi^[m] (pFlat l)) : normInteger ℂ_[l]) : ℂ_[l]) ≠ 0 := by
    intro h0
    have hπ : ((PreTilt.untilt (φi^[m] (pFlat l)) : normInteger ℂ_[l]) : ℂ_[l]) ^ l ^ m = (l : ℂ_[l]) := by
      rw [← SubmonoidClass.coe_pow, PreTilt.untilt_iterate_frobeniusEquiv_symm_pow, coe_untilt_pFlat]
    rw [h0, zero_pow (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)] at hπ
    exact natCast_p_ne_zero_cp (p := l) hπ.symm
  have h2 := (e h).symm.trans ((hs h).trans (hgh ▸ (hs g).symm |>.trans (e g)))
  have h3 := mul_left_cancel₀ hπ0 h2
  have hprim : IsPrimitiveRoot ((PreTilt.untilt (φi^[m] (epsilon l)) : normInteger ℂ_[l]) : ℂ_[l]) (l ^ m) :=
    IsPrimitiveRoot.coe_submonoidClass_iff.2
      (isPrimitiveRoot_untilt_iterate untilt_epsilon untilt_frobeniusEquiv_symm_epsilon_ne_one m)
  exact ZMod.val_injective _ (hprim.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h3)

end cont

theorem continuous_κ (l : ℕ) [Fact l.Prime] : Continuous (κ : GQ l → ℚ_[l]) := by
  have hc : Continuous fun g : GQ l =>
      kummerC (untilt_epsilon (p := l)) untilt_frobeniusEquiv_symm_epsilon_ne_one (toBot g) := by
    refine continuous_iff_continuousAt.2 fun g0 => Metric.tendsto_nhds.2 fun ε hε => ?_
    obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hε
      (inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt : (1 : ℝ) < l))
    obtain ⟨z, hz⟩ := exists_coe_eq_untilt_pFlat (l := l) m
    have : FiniteDimensional ℚ_[l] (IntermediateField.adjoin ℚ_[l] {z}) :=
      IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral z)
    have hU : IsOpen {h : GQ l | g0⁻¹ * h ∈ (IntermediateField.adjoin ℚ_[l] {z}).fixingSubgroup} :=
      (IntermediateField.fixingSubgroup_isOpen _).preimage (continuous_const_mul _)
    have h1 : g0 ∈ {h : GQ l | g0⁻¹ * h ∈ (IntermediateField.adjoin ℚ_[l] {z}).fixingSubgroup} := by
      simp only [Set.mem_setOf_eq, inv_mul_cancel]
      exact Subgroup.one_mem _
    filter_upwards [hU.mem_nhds h1] with h hh
    have hfix := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hh z (IntermediateField.mem_adjoin_simple_self _ _)
    have hgh : h z = g0 z := by
      have := congrArg g0 hfix
      simpa using this
    have e := toZModPow_kummerC_eq m hz hgh
    rw [dist_eq_norm]
    have hmem : kummerC (untilt_epsilon (p := l)) untilt_frobeniusEquiv_symm_epsilon_ne_one (toBot h) -
        kummerC (untilt_epsilon (p := l)) untilt_frobeniusEquiv_symm_epsilon_ne_one (toBot g0) ∈
          Ideal.span {(l : ℤ_[l]) ^ m} := by
      rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, e, sub_self]
    calc _ ≤ (l : ℝ) ^ (-(m : ℤ)) := (PadicInt.norm_le_pow_iff_mem_span_pow _ m).2 hmem
      _ = (l : ℝ)⁻¹ ^ m := by rw [_root_.zpow_neg, zpow_natCast, inv_pow]
      _ < ε := hm
  exact continuous_subtype_val.comp hc

end period_ring_base
