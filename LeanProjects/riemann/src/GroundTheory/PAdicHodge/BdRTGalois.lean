import Mathlib
import GroundTheory.PAdicHodge.UntiltFrobeniusEquivSymmEpsilonNeOne
set_option maxSynthPendingDepth 1

noncomputable section

open Ideal WittVector IsLocalRing

namespace GroundTheory.PAdicHodge

section LogPoly

variable {R : Type*} [CommRing R]

def logPolyCoeff (k i : ℕ) : ℤ := (-1) ^ (i + 1) * ((k.factorial / i : ℕ) : ℤ)

def logPoly (k : ℕ) (z : R) : R := ∑ i ∈ Finset.Ico 1 k, (logPolyCoeff k i : R) * z ^ i

theorem map_logPoly {S : Type*} [CommRing S] (f : R →+* S) (k : ℕ) (z : R) :
    f (logPoly k z) = logPoly k (f z) := by
  simp [logPoly, map_sum, map_mul, map_intCast, map_pow]

theorem logPoly_sub_mem (k : ℕ) {z w : R} {J : Ideal R} (h : z - w ∈ J) :
    logPoly k z - logPoly k w ∈ J := by
  rw [logPoly, logPoly, ← Finset.sum_sub_distrib]
  refine J.sum_mem fun i _ => ?_
  rw [← mul_sub]
  obtain ⟨c, hc⟩ := sub_dvd_pow_sub_pow z w i
  rw [hc]
  exact J.mul_mem_left _ (J.mul_mem_right _ h)

variable {B : Type*} [CommRing B] [Algebra ℚ B] {I : Ideal B} [IsAdicComplete I B]

theorem factorial_mul_logOnePlus_sub_logPoly_mem {z : B} (hz : z ∈ I) (k : ℕ) :
    (k.factorial : B) * logOnePlus I z hz - logPoly k z ∈ I ^ k := by
  have h := (I ^ k).mul_mem_left (k.factorial : B) (logOnePlus_sub_sum_mem hz k)
  convert h using 1
  rw [mul_sub, logPoly, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  obtain ⟨hi1, hik⟩ := Finset.mem_Ico.1 hi
  rw [← mul_assoc]
  congr 1
  have hdvd : i ∣ k.factorial := Nat.dvd_factorial hi1 hik.le
  have hi0 : (i : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hnat : ((k.factorial / i : ℕ) : ℚ) = (k.factorial : ℚ) / i := Nat.cast_div hdvd hi0
  have hq : ((logPolyCoeff k i : ℤ) : ℚ) = (k.factorial : ℚ) * ((-1) ^ (i + 1) / i) := by
    simp only [logPolyCoeff, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
      Int.cast_natCast, hnat]
    ring
  rw [← map_intCast (algebraMap ℚ B), hq, map_mul, map_natCast]

end LogPoly

section Cp

variable {p : ℕ} [Fact p.Prime]

local notation "𝒪" => normInteger ℂ_[p]
local notation "𝒪♭" => PreTilt (normInteger ℂ_[p]) p
local notation "𝕎𝒪♭" => WittVector p (PreTilt (normInteger ℂ_[p]) p)
local notation "𝔹" => BDeRhamPlus (normInteger ℂ_[p]) p
local notation "𝔪" => maximalIdeal (BDeRhamPlus (normInteger ℂ_[p]) p)
local notation "φi" => RingEquiv.symm (_root_.frobeniusEquiv (PreTilt (normInteger ℂ_[p]) p) p)

theorem exists_coe_eq_of_pow_eq_one {x : ℂ_[p]} {N : ℕ} (hN : N ≠ 0) (hx : x ^ N = 1) :
    ∃ y : PadicAlgCl p, (y : ℂ_[p]) = x := by
  haveI : NeZero N := ⟨hN⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (PadicAlgCl p) N
  have hζ' : IsPrimitiveRoot (algebraMap (PadicAlgCl p) ℂ_[p] ζ) N :=
    hζ.map_of_injective (algebraMap (PadicAlgCl p) ℂ_[p]).injective
  obtain ⟨i, -, hi⟩ := hζ'.eq_pow_of_pow_eq_one hx
  exact ⟨ζ ^ i, by rw [← hi, ← map_pow]; rfl⟩

theorem gal_smul_eq_pow_of_pow_eq_one {L : IntermediateField ℚ_[p] (PadicAlgCl p)}
    (σ : Gal(PadicAlgCl p/L)) {x : ℂ_[p]} {N : ℕ} (hx : x ^ p ^ N = 1) :
    σ • x = x ^ (PadicInt.toZModPow N (cycloChar L σ : ℤ_[p])).val := by
  obtain ⟨y, rfl⟩ := exists_coe_eq_of_pow_eq_one (pow_ne_zero N (Fact.out : p.Prime).ne_zero) hx
  have hy : y ^ p ^ N = 1 := (algebraMap (PadicAlgCl p) ℂ_[p]).injective (by
    rw [map_pow, map_one]; exact hx)
  rw [gal_smul_coe, cycloChar_spec L σ hy]
  exact map_pow (algebraMap (PadicAlgCl p) ℂ_[p]) y _

theorem iterate_frobSymm_mul (x y : 𝒪♭) (n : ℕ) : φi^[n] (x * y) = φi^[n] x * φi^[n] y := by
  induction n generalizing x y with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, map_mul, Function.iterate_succ_apply',
      Function.iterate_succ_apply']

theorem iterate_frobSymm_one (n : ℕ) : φi^[n] (1 : 𝒪♭) = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, map_one]

theorem iterate_frobSymm_pow (x : 𝒪♭) (m n : ℕ) : φi^[n] (x ^ m) = (φi^[n] x) ^ m := by
  induction m with
  | zero => rw [pow_zero, pow_zero, iterate_frobSymm_one]
  | succ m ih => rw [pow_succ, iterate_frobSymm_mul, ih, pow_succ]

theorem iterate_frobSymm_pow_p_pow (x : 𝒪♭) (n : ℕ) : (φi^[n] x) ^ p ^ n = x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply, pow_succ, pow_mul, ih, frobeniusEquiv_symm_pow_p]

theorem preTiltMap_iterate_frobSymm {L : IntermediateField ℚ_[p] (PadicAlgCl p)}
    (σ : Gal(PadicAlgCl p/L)) (x : 𝒪♭) (n : ℕ) :
    preTiltMap p (galCp σ : ℂ_[p] →+* ℂ_[p]) (AInf.norm_galCp_toRingHom σ) (φi^[n] x) =
      φi^[n] (preTiltMap p (galCp σ : ℂ_[p] →+* ℂ_[p]) (AInf.norm_galCp_toRingHom σ) x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
    exact RingHom.map_frobeniusEquiv_symm p _ _

theorem gal_smul_muBdR {L : IntermediateField ℚ_[p] (PadicAlgCl p)} (σ : Gal(PadicAlgCl p/L))
    (ε : 𝒪♭) :
    σ • muBdR p ε = wittToBDeRhamPlus 𝒪 p (teichmuller p
      (preTiltMap p (galCp σ : ℂ_[p] →+* ℂ_[p]) (AInf.norm_galCp_toRingHom σ) ε)) - 1 := by
  rw [muBdR, gal_smul_wittToBDeRhamPlus, AInf.mu, smul_sub, smul_one, AInf.gal_smul_teichmuller,
    map_sub, map_one]

theorem gal_smul_fontaineT_eq {L : IntermediateField ℚ_[p] (PadicAlgCl p)}
    (σ : Gal(PadicAlgCl p/L)) {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1) :
    σ • fontaineT ε hε = logOnePlus 𝔪 (σ • muBdR p ε) (gal_smul_mem_maximalIdeal σ (muBdR_mem hε)) := by
  rw [gal_smul_bdR_def, fontaineT, logOnePlus, logOnePlus]
  exact map_seriesEval (galBdRHom σ)
    (Ideal.map_le_iff_le_comap.2 fun x hx => by
      have h := gal_smul_mem_maximalIdeal σ hx
      rw [gal_smul_bdR_def] at h
      exact h) _ _ _

theorem gal_smul_fontaineT {L : IntermediateField ℚ_[p] (PadicAlgCl p)} (σ : Gal(PadicAlgCl p/L))
    {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1) :
    σ • fontaineT ε hε = algebraMap ℚ_[p] 𝔹 ((cycloChar L σ : ℤ_[p]) : ℚ_[p]) * fontaineT ε hε := by
  set a : ℤ_[p] := (cycloChar L σ : ℤ_[p]) with ha
  rw [← sub_eq_zero]
  refine IsPerfectoidField.eq_zero_of_forall_mem_maximalIdeal_pow fun k => ?_
  have hD : IsUnit ((k.factorial : ℕ) : 𝔹) := by
    have h := (isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero k) :
      ((k.factorial : ℕ) : ℚ) ≠ 0)).map (algebraMap ℚ 𝔹)
    rwa [map_natCast] at h
  refine (Ideal.unit_mul_mem_iff_mem _ hD).1 ?_
  refine IsPerfectoidField.mem_maximalIdeal_pow_of_forall_sub_mem fun M => ?_
  set aN : ℕ := (PadicInt.toZModPow (M + k) a).val with haN

  have hεu : IsUnit ε := (IsPerfectoidField.isUnit_iff_norm_untilt p).2 (by rw [hε]; simp)
  set ε' := preTiltMap p (galCp σ : ℂ_[p] →+* ℂ_[p]) (AInf.norm_galCp_toRingHom σ) ε with hε'
  set η := ε' * ((hεu.unit⁻¹ : 𝒪♭ˣ) : 𝒪♭) ^ aN with hη_def
  set ν := φi^[M + k] η with hν_def
  have hη : ε' = ε ^ aN * η := by
    rw [hη_def, ← mul_assoc, mul_comm (ε ^ aN), mul_assoc, ← mul_pow, IsUnit.mul_val_inv, one_pow,
      mul_one]
  have hνη : ν ^ p ^ (M + k) = η := iterate_frobSymm_pow_p_pow η (M + k)

  have hν : PreTilt.untilt ν = 1 := by
    set ζ := PreTilt.untilt (φi^[M + k] ε) with hζ_def
    have hζ : ((ζ : 𝒪) : ℂ_[p]) ^ p ^ (M + k) = 1 := by
      have h := PreTilt.untilt_iterate_frobeniusEquiv_symm_pow ε (M + k)
      rw [hε] at h
      exact congrArg Subtype.val h
    have h1 : ((PreTilt.untilt (φi^[M + k] ε') : 𝒪) : ℂ_[p]) = ((ζ : 𝒪) : ℂ_[p]) ^ aN := by
      rw [hε', ← preTiltMap_iterate_frobSymm, AInf.coe_untilt_gal, gal_smul_eq_pow_of_pow_eq_one σ hζ]
    have h2 : ((PreTilt.untilt (φi^[M + k] ((hεu.unit⁻¹ : 𝒪♭ˣ) : 𝒪♭)) : 𝒪) : ℂ_[p]) *
        ((ζ : 𝒪) : ℂ_[p]) = 1 := by
      have h3 : φi^[M + k] ((hεu.unit⁻¹ : 𝒪♭ˣ) : 𝒪♭) * φi^[M + k] ε = 1 := by
        rw [← iterate_frobSymm_mul, IsUnit.val_inv_mul, iterate_frobSymm_one]
      have h4 := congrArg (fun x => ((PreTilt.untilt x : 𝒪) : ℂ_[p])) h3
      simp only [map_mul, map_one] at h4
      rw [MulMemClass.coe_mul, OneMemClass.coe_one] at h4
      exact h4
    apply Subtype.ext
    rw [hν_def, hη_def, iterate_frobSymm_mul, iterate_frobSymm_pow, map_mul, map_pow]
    change ((PreTilt.untilt (φi^[M + k] ε') : 𝒪) : ℂ_[p]) *
      ((PreTilt.untilt (φi^[M + k] ((hεu.unit⁻¹ : 𝒪♭ˣ) : 𝒪♭)) : 𝒪) : ℂ_[p]) ^ aN = 1
    rw [h1, ← mul_pow, mul_comm, h2, one_pow]

  have hξ := IsPerfectoidField.ker_fontaineTheta_eq_span_kerThetaGenerator ℂ_[p] p
  set ξ := IsPerfectoidField.kerThetaGenerator ℂ_[p] p
  obtain ⟨c, hc⟩ : ξ ∣ teichmuller p ν - 1 := by
    have h : teichmuller p ν - 1 ∈ RingHom.ker (fontaineTheta 𝒪 p) := by
      rw [RingHom.mem_ker, map_sub, map_one, fontaineTheta_teichmuller, hν, sub_self]
    rwa [hξ, mem_span_singleton] at h
  have hT : (teichmuller p ε' : 𝕎𝒪♭) = teichmuller p ε ^ aN * (1 + ξ * c) ^ p ^ (M + k) := by
    rw [hη, ← hνη, map_mul, map_pow, map_pow, ← hc]
    ring

  set Z1 : 𝕎𝒪♭ := teichmuller p ε' - 1 with hZ1
  set Z0 : 𝕎𝒪♭ := teichmuller p ε ^ aN - 1 with hZ0
  set Zμ : 𝕎𝒪♭ := teichmuller p ε - 1 with hZμ
  have hJ : logPoly k Z1 - logPoly k Z0 ∈ span {(p : 𝕎𝒪♭) ^ M} ⊔ span {ξ ^ k} := by
    apply logPoly_sub_mem
    have h3 := one_add_pow_prime_pow_sub_one_mem (Fact.out : p.Prime) (ξ * c) (M + k) k k
      (Nat.lt_pow_self (Fact.out : p.Prime).one_lt).le
    rw [show M + k - k = M by omega] at h3
    have h4 : span {(ξ * c) ^ k} ≤ span {ξ ^ k} :=
      span_singleton_le_span_singleton.2 (by rw [mul_pow]; exact dvd_mul_right _ _)
    have h5 : Z1 - Z0 = teichmuller p ε ^ aN * ((1 + ξ * c) ^ p ^ (M + k) - 1) := by
      rw [hZ1, hZ0, hT]; ring
    rw [h5]
    exact Ideal.mul_mem_left _ _ (sup_le_sup_left h4 _ h3)
  obtain ⟨α, hα, β, hβ, hαβ⟩ := Submodule.mem_sup.1 hJ
  obtain ⟨α', rfl⟩ := mem_span_singleton.1 hα
  obtain ⟨β', rfl⟩ := mem_span_singleton.1 hβ

  obtain ⟨γ, hγ⟩ : (p : ℤ_[p]) ^ (M + k) ∣ (aN : ℤ_[p]) - a := by
    have h : (aN : ℤ_[p]) - a ∈ RingHom.ker (PadicInt.toZModPow (M + k)) := by
      rw [RingHom.mem_ker, map_sub, map_natCast, haN, ZMod.natCast_zmod_val, sub_self]
    rwa [PadicInt.ker_toZModPow, mem_span_singleton] at h

  set W := wittToBDeRhamPlus 𝒪 p with hW
  set μ := muBdR p ε with hμ_def
  have hμ : μ = W Zμ := by rw [hμ_def, muBdR_eq, hW, hZμ, map_sub, map_one]
  have hσμ : σ • μ = W Z1 := by rw [hμ_def, gal_smul_muBdR, hZ1, map_sub, map_one]
  have hz0mem : (1 + μ) ^ aN - 1 ∈ 𝔪 := by
    obtain ⟨d, hd⟩ := sub_dvd_pow_sub_pow (1 + μ) 1 aN
    rw [one_pow, add_sub_cancel_left] at hd
    rw [hd]
    exact Ideal.mul_mem_right _ _ (muBdR_mem hε)
  have hz0 : (1 + μ) ^ aN - 1 = W Z0 := by
    rw [hμ, hZ0, hZμ]
    simp only [map_sub, map_pow, map_one]
    ring
  have hσmem : σ • μ ∈ 𝔪 := gal_smul_mem_maximalIdeal σ (muBdR_mem hε)
  set t := fontaineT ε hε with ht
  set L1 := logOnePlus 𝔪 (σ • μ) hσmem with hL1
  set tN := logOnePlus 𝔪 ((1 + μ) ^ aN - 1) hz0mem with htN
  have E_σ : σ • t = L1 := gal_smul_fontaineT_eq σ hε
  have E_N : tN = (aN : 𝔹) * t := logOnePlus_pow (muBdR_mem hε) aN hz0mem
  have X1 := factorial_mul_logOnePlus_sub_logPoly_mem hσmem k
  have X0 := factorial_mul_logOnePlus_sub_logPoly_mem hz0mem k
  have X2 := factorial_mul_logOnePlus_sub_logPoly_mem (muBdR_mem hε) k
  have E_P1 : logPoly k (σ • μ) = W (logPoly k Z1) := by rw [hσμ, map_logPoly]
  have E_P0 : logPoly k ((1 + μ) ^ aN - 1) = W (logPoly k Z0) := by rw [hz0, map_logPoly]
  have E_Pμ : logPoly k μ = W (logPoly k Zμ) := by rw [hμ, map_logPoly]
  have E_αβ : W (logPoly k Z1) - W (logPoly k Z0) =
      (p : 𝔹) ^ M * W α' + W ξ ^ k * W β' := by
    rw [← map_sub, ← hαβ, map_add, map_mul, map_mul, map_pow, map_pow, map_natCast]
  have E_a : algebraMap ℚ_[p] 𝔹 (a : ℚ_[p]) =
      (aN : 𝔹) - (p : 𝔹) ^ (M + k) * W (IsPerfectoidField.padicIntToWitt (K := ℂ_[p]) p γ) := by
    have h : a = (aN : ℤ_[p]) - (p : ℤ_[p]) ^ (M + k) * γ := by rw [← hγ]; ring
    rw [h, PadicInt.coe_sub, map_sub, PadicInt.coe_natCast, map_natCast,
      IsPerfectoidField.algebraMap_padic_coe, map_mul, map_mul, map_pow, map_pow, map_natCast,
      map_natCast]
  have hξk : W ξ ^ k * W β' ∈ 𝔪 ^ k := by
    have h1 : W ξ ∈ 𝔪 := by
      rw [IsPerfectoidField.maximalIdeal_bDeRhamPlus_eq_span hξ]
      exact mem_span_singleton_self _
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow h1 k)
  refine ⟨α' + (p : 𝕎𝒪♭) ^ k * IsPerfectoidField.padicIntToWitt (K := ℂ_[p]) p γ * logPoly k Zμ, ?_⟩
  have key : (k.factorial : 𝔹) * (σ • t - algebraMap ℚ_[p] 𝔹 (a : ℚ_[p]) * t) -
      (p : 𝔹) ^ M * W (α' + (p : 𝕎𝒪♭) ^ k *
        IsPerfectoidField.padicIntToWitt (K := ℂ_[p]) p γ * logPoly k Zμ) =
      ((k.factorial : 𝔹) * L1 - logPoly k (σ • μ)) -
        ((k.factorial : 𝔹) * tN - logPoly k ((1 + μ) ^ aN - 1)) + W ξ ^ k * W β' +
        (p : 𝔹) ^ (M + k) * W (IsPerfectoidField.padicIntToWitt (K := ℂ_[p]) p γ) *
          ((k.factorial : 𝔹) * t - logPoly k μ) := by
    rw [map_add, map_mul, map_mul, map_pow, map_natCast]
    linear_combination (k.factorial : 𝔹) * E_σ + (k.factorial : 𝔹) * E_N -
      (k.factorial : 𝔹) * t * E_a + E_P1 - E_P0 + E_αβ +
      (p : 𝔹) ^ (M + k) * W (IsPerfectoidField.padicIntToWitt (K := ℂ_[p]) p γ) * E_Pμ
  rw [key]
  exact add_mem (add_mem (sub_mem X1 X0) hξk) (Ideal.mul_mem_left _ _ X2)

theorem gal_smul_tBdR {L : IntermediateField ℚ_[p] (PadicAlgCl p)} (σ : Gal(PadicAlgCl p/L)) :
    σ • tBdR p = algebraMap ℚ_[p] 𝔹 ((cycloChar L σ : ℤ_[p]) : ℚ_[p]) * tBdR p :=
  gal_smul_fontaineT σ untilt_epsilon

end Cp

end GroundTheory.PAdicHodge
