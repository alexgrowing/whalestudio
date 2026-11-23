import Mathlib
import GroundTheory.PAdicHodge.ThetaBDeRhamPlusFieldCycloUnitBdRZpow
import GroundTheory.PAdicHodge.LogMul
import GroundTheory.PAdicHodge.TiltValuation
set_option maxSynthPendingDepth 1

noncomputable section

open Ideal WittVector IsLocalRing

namespace GroundTheory.PAdicHodge

section Cp

variable {p : ℕ} [hp : Fact p.Prime]

local notation "𝒪" => normInteger ℂ_[p]
local notation "𝒪♭" => PreTilt (normInteger ℂ_[p]) p
local notation "𝔹" => BDeRhamPlus (normInteger ℂ_[p]) p
local notation "𝔪" => maximalIdeal (BDeRhamPlus (normInteger ℂ_[p]) p)

variable (p) in

def pRootSeq : ℕ → ℂ_[p]
  | 0 => p
  | (n + 1) => (IsAlgClosed.exists_pow_nat_eq (pRootSeq n) hp.out.pos).choose

theorem pRootSeq_succ_pow (n : ℕ) : pRootSeq p (n + 1) ^ p = pRootSeq p n :=
  (IsAlgClosed.exists_pow_nat_eq (pRootSeq p n) hp.out.pos).choose_spec

theorem pRootSeq_pow (n : ℕ) : pRootSeq p n ^ p ^ n = p := by
  induction n with
  | zero => simp [pRootSeq]
  | succ n ih => rw [pow_succ, pow_mul', pRootSeq_succ_pow, ih]

theorem norm_pRootSeq_le (n : ℕ) : ‖pRootSeq p n‖ ≤ 1 := by
  have h := congrArg norm (pRootSeq_pow (p := p) n)
  rw [norm_pow] at h
  have hp1 : ‖(p : ℂ_[p])‖ ≤ 1 := by
    have := (IsPerfectoidField.norm_natCast_integer_lt_one (K := ℂ_[p]) (p := p)).le
    simpa using this
  by_contra hlt
  rw [not_le] at hlt
  have : 1 < ‖pRootSeq p n‖ ^ p ^ n := one_lt_pow₀ hlt (pow_ne_zero _ hp.out.ne_zero)
  linarith

variable (p) in

def pRootSeqInt (n : ℕ) : 𝒪 :=
  ⟨pRootSeq p n, mem_normInteger.2 (norm_pRootSeq_le n)⟩

theorem pRootSeqInt_succ_pow (n : ℕ) : pRootSeqInt p (n + 1) ^ p = pRootSeqInt p n :=
  Subtype.ext (by simp [pRootSeqInt, pRootSeq_succ_pow])

variable (p) in

def pFlat : 𝒪♭ :=
  IsPerfectoidField.ofCompatible p (pRootSeqInt p) pRootSeqInt_succ_pow

theorem untilt_pFlat : PreTilt.untilt (pFlat p) = (p : 𝒪) := by
  rw [pFlat, IsPerfectoidField.untilt_ofCompatible]
  exact Subtype.ext (by simp [pRootSeqInt, pRootSeq])

theorem coe_untilt_pFlat : ((PreTilt.untilt (pFlat p) : 𝒪) : ℂ_[p]) = p := by
  rw [untilt_pFlat]
  simp

theorem natCast_p_ne_zero_cp : (p : ℂ_[p]) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero

def qBdR : 𝔹 := algebraMap ℚ 𝔹 (p : ℚ)⁻¹ * wittToBDeRhamPlus 𝒪 p (teichmuller p (pFlat p)) - 1

omit hp in
theorem one_add_qBdR [Fact p.Prime] :
    1 + qBdR (p := p) = algebraMap ℚ 𝔹 (p : ℚ)⁻¹ * wittToBDeRhamPlus 𝒪 p (teichmuller p (pFlat p)) := by
  rw [qBdR]
  ring

theorem qBdR_mem : qBdR (p := p) ∈ 𝔪 := by
  rw [IsPerfectoidField.maximalIdeal_bDeRhamPlus, RingHom.mem_ker, qBdR, map_sub, map_mul,
    IsPerfectoidField.thetaBDeRhamPlusField_wittToBDeRhamPlus, fontaineTheta_teichmuller, untilt_pFlat,
    RingHom.map_rat_algebraMap, map_one]
  have h : ((p : 𝒪) : ℂ_[p]) = p := by simp
  simp only [eq_ratCast, Rat.cast_inv, Rat.cast_natCast, h]
  rw [inv_mul_cancel₀ natCast_p_ne_zero_cp, sub_self]

variable (p) in

def uBdR : 𝔹 := logOnePlus 𝔪 (qBdR (p := p)) qBdR_mem

theorem uBdR_mem : uBdR p ∈ 𝔪 := logOnePlus_mem qBdR_mem

variable {K : IntermediateField ℚ_[p] (PadicAlgCl p)}

theorem coe_untilt_galFlat_pFlat (σ : Gal(PadicAlgCl p/K)) :
    ((PreTilt.untilt (preTiltMap p (galCp σ : ℂ_[p] →+* ℂ_[p]) (AInf.norm_galCp_toRingHom σ) (pFlat p)) : 𝒪) : ℂ_[p]) = p := by
  rw [AInf.coe_untilt_gal, coe_untilt_pFlat, ← galCp_apply, map_natCast]

theorem exists_galFlat_pFlat_eq (σ : Gal(PadicAlgCl p/K)) :
    ∃ η : 𝒪♭, preTiltMap p (galCp σ : ℂ_[p] →+* ℂ_[p]) (AInf.norm_galCp_toRingHom σ) (pFlat p) = pFlat p * η := by
  refine preTilt_dvd_iff_norm_le.2 (le_of_eq ?_)
  rw [preTilt_norm_def, preTilt_norm_def, coe_untilt_pFlat,
    coe_untilt_galFlat_pFlat]

def kummerEta (σ : Gal(PadicAlgCl p/K)) : 𝒪♭ := (exists_galFlat_pFlat_eq σ).choose

theorem pFlat_mul_kummerEta (σ : Gal(PadicAlgCl p/K)) :
    preTiltMap p (galCp σ : ℂ_[p] →+* ℂ_[p]) (AInf.norm_galCp_toRingHom σ) (pFlat p) = pFlat p * kummerEta σ :=
  (exists_galFlat_pFlat_eq σ).choose_spec

theorem untilt_kummerEta (σ : Gal(PadicAlgCl p/K)) : PreTilt.untilt (kummerEta σ) = 1 := by
  have h := congrArg (fun x => ((PreTilt.untilt x : 𝒪) : ℂ_[p])) (pFlat_mul_kummerEta σ)
  simp only [untilt_mul, MulMemClass.coe_mul] at h
  rw [coe_untilt_galFlat_pFlat, coe_untilt_pFlat] at h
  apply Subtype.ext
  rw [OneMemClass.coe_one]
  exact (mul_eq_left₀ natCast_p_ne_zero_cp).1 h.symm

theorem gal_smul_logOnePlus (σ : Gal(PadicAlgCl p/K)) {z : 𝔹} (hz : z ∈ 𝔪) :
    σ • logOnePlus 𝔪 z hz = logOnePlus 𝔪 (σ • z) (gal_smul_mem_maximalIdeal σ hz) := by
  rw [gal_smul_bdR_def, logOnePlus, logOnePlus]
  exact map_seriesEval (galBdRHom σ)
    (Ideal.map_le_iff_le_comap.2 fun x hx => by
      have h := gal_smul_mem_maximalIdeal σ hx
      rw [gal_smul_bdR_def] at h
      exact h) _ _ _

theorem one_add_gal_smul_qBdR (σ : Gal(PadicAlgCl p/K)) :
    1 + σ • qBdR (p := p) = (1 + qBdR) * (1 + muBdR p (kummerEta σ)) := by
  have h1 : σ • (1 + qBdR (p := p)) = 1 + σ • qBdR := by rw [smul_add, smul_one]
  rw [← h1, one_add_qBdR, muBdR_eq, add_sub_cancel, smul_mul', gal_smul_wittToBDeRhamPlus,
    AInf.gal_smul_teichmuller, pFlat_mul_kummerEta, map_mul, map_mul, gal_smul_bdR_def (x := algebraMap _ _ _),
    RingHom.map_rat_algebraMap, mul_assoc]

theorem gal_smul_uBdR (σ : Gal(PadicAlgCl p/K)) :
    σ • uBdR p = uBdR p + fontaineT (kummerEta σ) (untilt_kummerEta σ) := by
  rw [uBdR, gal_smul_logOnePlus, fontaineT]
  exact logOnePlus_mul qBdR_mem (muBdR_mem (untilt_kummerEta σ)) _ (one_add_gal_smul_qBdR σ)

end Cp

end GroundTheory.PAdicHodge
