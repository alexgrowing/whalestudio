import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatCDefs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DividedPowerFiltrationSpanPow

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatPdpB

variable (l : ℕ) [Fact l.Prime]

theorem span_xi_eq_span_fontaine_t :
    Ideal.span {wittToBDeRhamPlus (normInteger ℂ_[l]) l (xi0 l)} = Ideal.span {tBdR l} := by
  haveI : IsPerfectoidField ℂ_[l] l := IsPerfectoidField.padicComplex l
  have hg := IsPerfectoidField.ker_fontaineTheta_eq_span_kerThetaGenerator ℂ_[l] l
  generalize IsPerfectoidField.kerThetaGenerator ℂ_[l] l = g at hg
  have hnorm : ∀ z : normInteger ℂ_[l], ‖(z : ℂ_[l])‖ ≤ 1 := fun z => mem_normInteger.1 z.2
  have hbound : ∀ w : WittVector l (PreTilt (normInteger ℂ_[l]) l),
      WittVector.fontaineTheta (normInteger ℂ_[l]) l w = 0 →
      ‖((PreTilt.untilt (WittVector.constantCoeff w) : normInteger ℂ_[l]) : ℂ_[l])‖ ≤
        ‖((l : normInteger ℂ_[l]) : ℂ_[l])‖ := by
    intro w hw
    have h1 : Ideal.Quotient.mk (Ideal.span {(l : normInteger ℂ_[l])})
        (PreTilt.untilt (WittVector.constantCoeff w)) = 0 := by
      rw [PreTilt.mk_untilt_eq_coeff_zero]
      have h2 := WittVector.mk_fontaineTheta (R := normInteger ℂ_[l]) (p := l) w
      rw [hw, map_zero] at h2
      exact h2.symm
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at h1
    obtain ⟨z, hz⟩ := h1
    rw [← hz, Subring.coe_mul, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (hnorm z)
  have hx : xi0 l ∈ RingHom.ker (WittVector.fontaineTheta (normInteger ℂ_[l]) l) := by
    rw [RingHom.mem_ker, CrystallineSemistableComparison.xi0, map_sub, map_natCast, WittVector.fontaineTheta_teichmuller,
      untilt_pFlat, sub_self]
  rw [hg, Ideal.mem_span_singleton'] at hx
  obtain ⟨c, hc⟩ := hx
  have hg0 : WittVector.fontaineTheta (normInteger ℂ_[l]) l g = 0 := by
    rw [← RingHom.mem_ker, hg]
    exact Ideal.mem_span_singleton_self g
  have hcn : WittVector.fontaineTheta (normInteger ℂ_[l]) l c ≠ 0 := by
    intro hc0
    have hcm : c ∈ RingHom.ker (WittVector.fontaineTheta (normInteger ℂ_[l]) l) := hc0
    rw [hg, Ideal.mem_span_singleton'] at hcm
    obtain ⟨d, hd⟩ := hcm
    have hxe : xi0 l = d * g * g := by rw [← hc, ← hd]
    have hco := congrArg WittVector.constantCoeff hxe
    have hT : WittVector.constantCoeff (WittVector.teichmuller l (pFlat l)) = pFlat l :=
      WittVector.teichmuller_coeff_zero l _
    rw [CrystallineSemistableComparison.xi0, map_sub, map_natCast, hT, map_mul, map_mul,
      CharP.cast_eq_zero (PreTilt (normInteger ℂ_[l]) l) l, zero_sub] at hco
    have hpf : pFlat l = (-WittVector.constantCoeff d) * WittVector.constantCoeff g *
        WittVector.constantCoeff g := by
      rw [neg_mul, neg_mul, ← hco, neg_neg]
    have hu := congrArg (fun y => ‖((PreTilt.untilt y : normInteger ℂ_[l]) : ℂ_[l])‖) hpf
    simp only [map_mul, Subring.coe_mul, norm_mul, untilt_pFlat] at hu
    have hb := hbound g hg0
    have hd1 := hnorm (PreTilt.untilt (-WittVector.constantCoeff d))
    have hpos : 0 < ‖((l : normInteger ℂ_[l]) : ℂ_[l])‖ := by
      rw [norm_pos_iff]; push_cast; exact natCast_p_ne_zero_cp
    have hlt : ‖((l : normInteger ℂ_[l]) : ℂ_[l])‖ < 1 :=
      IsPerfectoidField.norm_natCast_integer_lt_one (K := ℂ_[l]) l
    have hn0 := norm_nonneg ((PreTilt.untilt (WittVector.constantCoeff g) : normInteger ℂ_[l]) : ℂ_[l])
    have hn1 := norm_nonneg ((PreTilt.untilt (-WittVector.constantCoeff d) : normInteger ℂ_[l]) : ℂ_[l])
    nlinarith [mul_le_mul hb hb hn0 hpos.le, mul_le_mul_of_nonneg_right hd1 (mul_nonneg hn0 hn0),
      mul_lt_of_lt_one_left hpos hlt]
  have hcu : IsUnit (wittToBDeRhamPlus (normInteger ℂ_[l]) l c) := by
    by_contra hnu
    have hm : wittToBDeRhamPlus (normInteger ℂ_[l]) l c ∈
        IsLocalRing.maximalIdeal (BDeRhamPlus (normInteger ℂ_[l]) l) :=
      (IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 hnu)
    rw [IsPerfectoidField.maximalIdeal_bDeRhamPlus, RingHom.mem_ker,
      IsPerfectoidField.thetaBDeRhamPlusField_wittToBDeRhamPlus] at hm
    exact hcn (by exact_mod_cast hm)
  rw [← hc, map_mul, Ideal.span_singleton_mul_left_unit hcu,
    ← IsPerfectoidField.maximalIdeal_bDeRhamPlus_eq_span hg, maximalIdeal_eq_span_tBdR]

theorem span_fk_pow (k r : ℕ) :
    Ideal.span {fk l k (xi0 l) ^ r} = Ideal.span {pk l k (tBdR l) ^ r} := by
  have h2 : Ideal.span {wittToBDeRhamPlus (normInteger ℂ_[l]) l (xi0 l) ^ r} =
      Ideal.span {tBdR l ^ r} := by
    rw [← Ideal.span_singleton_pow, ← Ideal.span_singleton_pow, span_xi_eq_span_fontaine_t]
  have h3 := congrArg (Ideal.map (pk l k)) h2
  simp only [Ideal.map_span, Set.image_singleton, map_pow] at h3
  exact h3

theorem pInv_eq_tBdR {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (t : (per l K).P)
    (ht : (t : (per l K).B) = (per l K).tB) : pInv l t = tBdR l := by
  have hi : GroundTheory.PAdicHodge.ACris.iota ℂ_[l] l (Formalism.Per6.tA l) = tBdR l :=
    GroundTheory.PAdicHodge.ACris.iota_periodT (ε := epsilon l) untilt_epsilon
  have key : (algebraMap (Formalism.Per6.BdRp l) (Formalism.Per6.BdR l)).rangeRestrict (tBdR l) = t := by
    apply Subtype.ext
    refine Eq.trans ?_ ht.symm
    show algebraMap (Formalism.Per6.BdRp l) (Formalism.Per6.BdR l) (tBdR l) =
      algebraMap (Formalism.Per6.BdRp l) (Formalism.Per6.BdR l)
        (GroundTheory.PAdicHodge.ACris.iota ℂ_[l] l (Formalism.Per6.tA l))
    rw [hi]
  rw [← key]
  unfold CrystallineSemistableComparison.Pb.Lat.pInv
  simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
  exact (RingEquiv.symm_apply_eq _).2 rfl

end GlobalTheory.CompanionTheory.LatPdpB

open GlobalTheory.CompanionTheory.LatPdpB in

theorem GlobalTheory.CompanionTheory.LatPdpB.dividedPowerFiltration_lev_eq_span_pow : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ} (h : LevHyp l K M) (k : ℕ), ∀ (r : ℕ) (t : (per l K).P), (t : (per l K).B) = (per l K).tB → pdP (lev h k).γB r = Ideal.span {(lev h k).toB t ^ r} := by
  intro l _ K M h k r t ht
  show pdP (γB (fk l k) (xi0 l)) r = Ideal.span {(pk l k) (pInv l t) ^ r}
  rw [GlobalTheory.CompanionTheory.DPFiltration.pdP_γB, pInv_eq_tBdR l t ht, span_fk_pow]
