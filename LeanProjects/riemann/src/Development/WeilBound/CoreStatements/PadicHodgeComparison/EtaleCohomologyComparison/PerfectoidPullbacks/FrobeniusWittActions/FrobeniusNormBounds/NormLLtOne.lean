import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.IsUnitWitt
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BcrisRegularPeriodRing
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusWittActions.FrobeniusNormBounds.WFixAlg

set_option backward.isDefEq.respectTransparency false

noncomputable section

open GroundTheory.PAdicHodge

namespace CrystallineSemistableComparison.Pb.G3

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem norm_l_lt_one : ‖((l : ℕ) : ℂ_[l])‖ < 1 := by
  exact IsPerfectoidField.norm_natCast_lt_one

theorem tilt_fix (r : Res l K) (σ : Gal(PadicAlgCl l/K)) (c : r.k) (f : ℕ) (hf : 0 < f) (hc : c ^ (l ^ f) = c) :
    preTiltMap l (galCp σ : ℂ_[l] →+* ℂ_[l]) (AInf.norm_galCp_toRingHom σ) (r.s c) = r.s c := by
  set τ := preTiltMap l (galCp σ : ℂ_[l] →+* ℂ_[l]) (AInf.norm_galCp_toRingHom σ) with hτ
  obtain ⟨x, rfl⟩ := r.surj c
  set a := r.s (r.ρ x) with ha
  have hd : (τ a - a) ^ (l ^ f) = τ a - a := by
    rw [sub_pow_char_pow, ← map_pow, ha, ← map_pow, hc]
  have h1 : ‖((PreTilt.untilt (τ a) : OC l) : ℂ_[l]) - ((PreTilt.untilt a : OC l) : ℂ_[l])‖ < 1 := by
    have hx := r.hs x
    rw [← ha] at hx
    push_cast at hx
    have e1 : ((PreTilt.untilt (τ a) : OC l) : ℂ_[l]) = galCp σ ((PreTilt.untilt a : OC l) : ℂ_[l]) :=
      coe_untilt_preTiltMap _ _ a
    have e2 : galCp σ ((okToOC l K x : OC l) : ℂ_[l]) = ((okToOC l K x : OC l) : ℂ_[l]) :=
      congrArg Subtype.val (galOC_okToOC σ x)
    have h2 : ‖((PreTilt.untilt (τ a) : OC l) : ℂ_[l]) - ((okToOC l K x : OC l) : ℂ_[l])‖ < 1 := by
      rw [e1, ← e2, ← map_sub]
      exact (AInf.norm_galCp_toRingHom σ _).trans_lt hx
    have e3 : ((PreTilt.untilt (τ a) : OC l) : ℂ_[l]) - ((PreTilt.untilt a : OC l) : ℂ_[l]) =
        (((PreTilt.untilt (τ a) : OC l) : ℂ_[l]) - ((okToOC l K x : OC l) : ℂ_[l])) +
          -(((PreTilt.untilt a : OC l) : ℂ_[l]) - ((okToOC l K x : OC l) : ℂ_[l])) := by ring
    rw [e3]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt h2 (by rw [norm_neg]; exact hx))
  have h3 : ‖((PreTilt.untilt (τ a - a) : OC l) : ℂ_[l])‖ < 1 := by
    have hm : Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) (PreTilt.untilt (τ a - a)) =
        Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) (PreTilt.untilt (τ a) - PreTilt.untilt a) := by
      simp only [IsPerfectoidField.mk_untilt, map_sub]
    obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 hm)
    have e4 : ((PreTilt.untilt (τ a - a) : OC l) : ℂ_[l]) = (((z * (l : OC l) : OC l)) : ℂ_[l]) +
        (((PreTilt.untilt (τ a) : OC l) : ℂ_[l]) - ((PreTilt.untilt a : OC l) : ℂ_[l])) := by
      rw [hz]; push_cast; ring
    rw [e4]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ h1)
    push_cast
    rw [norm_mul]
    calc ‖(z : ℂ_[l])‖ * ‖((l : ℕ) : ℂ_[l])‖ ≤ 1 * ‖((l : ℕ) : ℂ_[l])‖ :=
          mul_le_mul_of_nonneg_right (mem_normInteger.1 z.2) (norm_nonneg _)
      _ < 1 := by rw [one_mul]; exact norm_l_lt_one
  have h4 : ‖((PreTilt.untilt (τ a - a) : OC l) : ℂ_[l])‖ ^ (l ^ f) = ‖((PreTilt.untilt (τ a - a) : OC l) : ℂ_[l])‖ := by
    conv_rhs => rw [← hd]
    rw [map_pow, SubmonoidClass.coe_pow, norm_pow]
  have h5 : ‖((PreTilt.untilt (τ a - a) : OC l) : ℂ_[l])‖ = 0 := by
    by_contra hne
    have hpos := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
    have hl : 1 < l ^ f := Nat.one_lt_pow hf.ne' (Fact.out : l.Prime).one_lt
    exact (pow_lt_self_of_lt_one₀ hpos h3 hl).ne h4
  have h6 : PreTilt.untilt (τ a - a) = 0 := Subtype.ext (by rw [norm_eq_zero.1 h5]; rfl)
  exact sub_eq_zero.1 ((IsPerfectoidField.untilt_eq_zero_iff l).1 h6)

theorem w_fix (r : Res l K) [FiniteDimensional ℚ_[l] K] (g : K.fixingSubgroup) (w : WittVector l r.k) :
    (per l K).σA g (r.w w) = r.w w := by
  change ACris.galCris (IntermediateField.fixingSubgroupEquiv K g) ((algebraMap (Ainf l) (Acris l)) (WittVector.map r.s w)) =
    (algebraMap (Ainf l) (Acris l)) (WittVector.map r.s w)
  rw [← ACris.gal_smul_def, ACris.gal_smul_algebraMap, AInf.gal_smul_def]
  congr 1
  change WittVector.map _ (WittVector.map r.s w) = _
  ext n
  rw [WittVector.map_coeff, WittVector.map_coeff]
  obtain ⟨f, hf, hc⟩ := alg_pow r (w.coeff n)
  exact tilt_fix r _ _ f hf hc

end CrystallineSemistableComparison.Pb.G3
