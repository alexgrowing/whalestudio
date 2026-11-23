import Mathlib
import GroundTheory.PAdicHodge.BStPeriod
import GroundTheory.PAdicHodge.BdRTGalois
set_option maxSynthPendingDepth 1

noncomputable section

open Ideal WittVector IsLocalRing

namespace GroundTheory.PAdicHodge

section Cp

variable {p : ℕ} [hp : Fact p.Prime]

local notation "𝒪" => normInteger ℂ_[p]
local notation "𝒪♭" => PreTilt (normInteger ℂ_[p]) p
local notation "φi" => RingEquiv.symm (_root_.frobeniusEquiv (PreTilt (normInteger ℂ_[p]) p) p)

local instance instNeZeroPowPrime (n : ℕ) : NeZero (p ^ n) := ⟨pow_ne_zero n hp.out.ne_zero⟩

theorem tilt_ext_untilt {x y : 𝒪♭}
    (h : ∀ n, PreTilt.untilt (φi^[n] x) = PreTilt.untilt (φi^[n] y)) : x = y :=
  IsPerfectoidField.preTilt_ext p fun n => by
    rw [← IsPerfectoidField.mk_untilt_iterate, h, IsPerfectoidField.mk_untilt_iterate]

theorem untilt_iterate_ofCompatible (y : ℕ → 𝒪) (hy : ∀ n, y (n + 1) ^ p = y n) (n : ℕ) :
    PreTilt.untilt (φi^[n] (IsPerfectoidField.ofCompatible p y hy)) = y n := by
  have e : φi^[n] (IsPerfectoidField.ofCompatible p y hy) =
      IsPerfectoidField.ofCompatible p (fun m => y (m + n)) (fun m => by
        rw [show m + 1 + n = (m + n) + 1 by omega]; exact hy (m + n)) := by
    refine IsPerfectoidField.preTilt_ext p fun m => ?_
    rw [PreTilt.coeff_iterate_frobeniusEquiv_symm, IsPerfectoidField.coeff_ofCompatible,
      IsPerfectoidField.coeff_ofCompatible]
  rw [e, IsPerfectoidField.untilt_ofCompatible, zero_add]

omit hp in

theorem pow_eq_pow_of_mod_eq {M : Type*} [Monoid M] {ζ : M} {N u v : ℕ} (hζ : ζ ^ N = 1)
    (h : u % N = v % N) : ζ ^ u = ζ ^ v := by
  rw [← Nat.mod_add_div u N, ← Nat.mod_add_div v N, pow_add, pow_add, pow_mul, pow_mul, hζ, one_pow,
    one_pow, h]

theorem val_toZModPow_mod (a : ℤ_[p]) {m n : ℕ} (h : m ≤ n) :
    (PadicInt.toZModPow n a).val % p ^ m = (PadicInt.toZModPow m a).val := by
  rw [← PadicInt.zmod_cast_comp_toZModPow m n h, RingHom.comp_apply, ZMod.castHom_apply,
    ZMod.cast_eq_val, ZMod.val_natCast]

theorem untilt_iterate_pow_eq_one {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1) (n : ℕ) :
    PreTilt.untilt (φi^[n] ε) ^ p ^ n = 1 := by
  rw [PreTilt.untilt_iterate_frobeniusEquiv_symm_pow, hε]

theorem coe_untilt_iterate_pow_eq_one {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1) (n : ℕ) :
    ((PreTilt.untilt (φi^[n] ε) : 𝒪) : ℂ_[p]) ^ p ^ n = 1 := by
  rw [← SubmonoidClass.coe_pow, untilt_iterate_pow_eq_one hε, OneMemClass.coe_one]

def epsSeq (ε : 𝒪♭) (a : ℤ_[p]) (n : ℕ) : 𝒪 :=
  PreTilt.untilt (φi^[n] ε) ^ (PadicInt.toZModPow n a).val

theorem epsSeq_succ_pow {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1) (a : ℤ_[p]) (n : ℕ) :
    epsSeq ε a (n + 1) ^ p = epsSeq ε a n := by
  rw [epsSeq, epsSeq, ← pow_mul, mul_comm, pow_mul, IsPerfectoidField.untilt_iterate_succ_pow]
  exact pow_eq_pow_of_mod_eq (untilt_iterate_pow_eq_one hε n)
    ((val_toZModPow_mod a (Nat.le_succ n)).trans (Nat.mod_eq_of_lt (ZMod.val_lt _)).symm)

def epsPow {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1) (a : ℤ_[p]) : 𝒪♭ :=
  IsPerfectoidField.ofCompatible p (epsSeq ε a) (epsSeq_succ_pow hε a)

theorem untilt_iterate_epsPow {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1) (a : ℤ_[p]) (n : ℕ) :
    PreTilt.untilt (φi^[n] (epsPow hε a)) =
      PreTilt.untilt (φi^[n] ε) ^ (PadicInt.toZModPow n a).val :=
  untilt_iterate_ofCompatible _ _ n

theorem val_toZModPow_zero (a : ℤ_[p]) : (PadicInt.toZModPow 0 a).val = 0 :=
  Nat.lt_one_iff.1 (by simpa using ZMod.val_lt (PadicInt.toZModPow 0 a))

theorem untilt_epsPow {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1) (a : ℤ_[p]) : PreTilt.untilt (epsPow hε a) = 1 := by
  have h := untilt_iterate_epsPow hε a 0
  rw [Function.iterate_zero, id, val_toZModPow_zero, pow_zero] at h
  exact h

theorem epsPow_add {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1) (a b : ℤ_[p]) :
    epsPow hε (a + b) = epsPow hε a * epsPow hε b := by
  refine tilt_ext_untilt fun n => ?_
  rw [iterate_frobSymm_mul, map_mul, untilt_iterate_epsPow, untilt_iterate_epsPow,
    untilt_iterate_epsPow, ← pow_add, map_add]
  refine pow_eq_pow_of_mod_eq (untilt_iterate_pow_eq_one hε n) ?_
  rw [ZMod.val_add, Nat.mod_mod]

theorem epsPow_natCast {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1) (m : ℕ) : epsPow hε (m : ℤ_[p]) = ε ^ m := by
  refine tilt_ext_untilt fun n => ?_
  rw [untilt_iterate_epsPow, iterate_frobSymm_pow, map_pow, map_natCast]
  refine pow_eq_pow_of_mod_eq (untilt_iterate_pow_eq_one hε n) ?_
  rw [ZMod.val_natCast, Nat.mod_mod]

theorem epsPow_one {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1) : epsPow hε 1 = ε := by
  simpa using epsPow_natCast hε 1

theorem epsPow_zero {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1) : epsPow hε 0 = 1 := by
  simpa using epsPow_natCast hε 0

theorem isPrimitiveRoot_untilt_iterate {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1)
    (hζ : PreTilt.untilt (φi ε) ≠ 1) (n : ℕ) :
    IsPrimitiveRoot (PreTilt.untilt (φi^[n] ε)) (p ^ n) := by
  rcases n with _ | m
  · rw [Function.iterate_zero, id, hε, pow_zero]
    exact IsPrimitiveRoot.one
  · have hord : orderOf (PreTilt.untilt (φi^[m + 1] ε)) = p ^ (m + 1) := by
      refine orderOf_eq_prime_pow ?_ (untilt_iterate_pow_eq_one hε (m + 1))
      rw [Function.iterate_succ_apply, PreTilt.untilt_iterate_frobeniusEquiv_symm_pow]
      exact hζ
    rw [← hord]
    exact IsPrimitiveRoot.orderOf _

theorem epsPow_injective {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1) (hζ : PreTilt.untilt (φi ε) ≠ 1) {a b : ℤ_[p]}
    (h : epsPow hε a = epsPow hε b) : a = b := by
  refine PadicInt.ext_of_toZModPow.1 fun n => ZMod.val_injective _ ?_
  have h1 := congrArg (fun x => PreTilt.untilt (φi^[n] x)) h
  simp only [untilt_iterate_epsPow] at h1
  exact (isPrimitiveRoot_untilt_iterate hε hζ n).pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h1

theorem exists_epsPow_eq {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1) (hζ : PreTilt.untilt (φi ε) ≠ 1) {η : 𝒪♭}
    (hη : PreTilt.untilt η = 1) : ∃ a : ℤ_[p], epsPow hε a = η := by
  have hex : ∀ n, ∃ i < p ^ n, PreTilt.untilt (φi^[n] ε) ^ i = PreTilt.untilt (φi^[n] η) :=
    fun n => (isPrimitiveRoot_untilt_iterate hε hζ n).eq_pow_of_pow_eq_one
      (untilt_iterate_pow_eq_one hη n)
  choose k hk hkη using hex
  have hi : ∀ n, (p : ℤ) ^ n ∣ (k (n + 1) : ℤ) - (k n : ℤ) := by
    intro n
    have e : PreTilt.untilt (φi^[n] ε) ^ (k (n + 1) % p ^ n) = PreTilt.untilt (φi^[n] ε) ^ k n := by
      rw [pow_eq_pow_of_mod_eq (untilt_iterate_pow_eq_one hε n) (Nat.mod_mod _ _), hkη n,
        ← IsPerfectoidField.untilt_iterate_succ_pow (x := ε), pow_right_comm, hkη (n + 1),
        IsPerfectoidField.untilt_iterate_succ_pow]
    have hm : k n % p ^ n = k (n + 1) % p ^ n := by
      rw [Nat.mod_eq_of_lt (hk n)]
      exact ((isPrimitiveRoot_untilt_iterate hε hζ n).pow_inj (Nat.mod_lt _ (NeZero.pos _)) (hk n) e).symm
    have := (Nat.modEq_iff_dvd.1 hm)
    exact_mod_cast this
  refine ⟨PadicInt.ofIntSeq _ (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub (fun n => (k n : ℤ)) p hi),
    tilt_ext_untilt fun n => ?_⟩
  rw [untilt_iterate_epsPow, PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub _ p hi, Int.cast_natCast,
    ZMod.val_cast_of_lt (hk n), hkη n]

variable {K : IntermediateField ℚ_[p] (PadicAlgCl p)}

abbrev tiltGal (σ : Gal(PadicAlgCl p/K)) : 𝒪♭ →+* 𝒪♭ :=
  preTiltMap p (galCp σ : ℂ_[p] →+* ℂ_[p]) (AInf.norm_galCp_toRingHom σ)

theorem coe_untilt_iterate_tiltGal (σ : Gal(PadicAlgCl p/K)) (x : 𝒪♭) (n : ℕ) :
    ((PreTilt.untilt (φi^[n] (tiltGal σ x)) : 𝒪) : ℂ_[p]) =
      σ • ((PreTilt.untilt (φi^[n] x) : 𝒪) : ℂ_[p]) := by
  rw [tiltGal, ← preTiltMap_iterate_frobSymm, AInf.coe_untilt_gal]

theorem tiltGal_mul (σ τ : Gal(PadicAlgCl p/K)) (x : 𝒪♭) :
    tiltGal (σ * τ) x = tiltGal σ (tiltGal τ x) := by
  refine tilt_ext_untilt fun n => Subtype.ext ?_
  rw [coe_untilt_iterate_tiltGal, coe_untilt_iterate_tiltGal, coe_untilt_iterate_tiltGal, mul_smul]

theorem tiltGal_epsPow {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1) (σ : Gal(PadicAlgCl p/K)) (a : ℤ_[p]) :
    tiltGal σ (epsPow hε a) = epsPow hε ((cycloChar K σ : ℤ_[p]) * a) := by
  refine tilt_ext_untilt fun n => Subtype.ext ?_
  rw [coe_untilt_iterate_tiltGal, untilt_iterate_epsPow, untilt_iterate_epsPow, SubmonoidClass.coe_pow,
    SubmonoidClass.coe_pow, smul_pow', gal_smul_eq_pow_of_pow_eq_one σ (coe_untilt_iterate_pow_eq_one hε n),
    ← pow_mul, map_mul]
  refine pow_eq_pow_of_mod_eq (coe_untilt_iterate_pow_eq_one hε n) ?_
  rw [ZMod.val_mul, Nat.mod_mod]

theorem tilt_mul_left_cancel {x a b : 𝒪♭} (hx : x ≠ 0) (h : x * a = x * b) : a = b := by
  refine tilt_ext_untilt fun n => ?_
  have h1 := congrArg (fun y => PreTilt.untilt (φi^[n] y)) h
  simp only [iterate_frobSymm_mul, map_mul] at h1
  have hx0 : PreTilt.untilt (φi^[n] x) ≠ 0 := by
    intro h0
    rw [IsPerfectoidField.untilt_eq_zero_iff] at h0
    apply hx
    have h2 := congrArg (fun y => (_root_.frobeniusEquiv 𝒪♭ p)^[n] y) h0
    rwa [Function.LeftInverse.iterate (fun y => RingEquiv.apply_symm_apply _ y) n x,
      Function.iterate_fixed (map_zero _) n] at h2
  exact mul_left_cancel₀ hx0 h1

theorem exists_tiltGal_eq_mul {x : 𝒪♭} (hx : x ≠ 0) {σ : Gal(PadicAlgCl p/K)}
    (hσ : σ • ((PreTilt.untilt x : 𝒪) : ℂ_[p]) = ((PreTilt.untilt x : 𝒪) : ℂ_[p])) :
    ∃ η : 𝒪♭, PreTilt.untilt η = 1 ∧ tiltGal σ x = x * η := by
  have hcoe : ((PreTilt.untilt (tiltGal σ x) : 𝒪) : ℂ_[p]) = ((PreTilt.untilt x : 𝒪) : ℂ_[p]) := by
    rw [tiltGal, AInf.coe_untilt_gal, hσ]
  obtain ⟨η, hη⟩ : x ∣ tiltGal σ x :=
    preTilt_dvd_iff_norm_le.2 (le_of_eq (by rw [preTilt_norm_def, preTilt_norm_def, hcoe]))
  refine ⟨η, ?_, hη⟩
  have h := congrArg (fun y => ((PreTilt.untilt y : 𝒪) : ℂ_[p])) hη
  simp only [map_mul, MulMemClass.coe_mul] at h
  rw [hcoe] at h
  have hx0 : ((PreTilt.untilt x : 𝒪) : ℂ_[p]) ≠ 0 := by
    intro h0
    exact hx ((IsPerfectoidField.untilt_eq_zero_iff (p := p)).1 (Subtype.ext (by simpa using h0)))
  apply Subtype.ext
  rw [OneMemClass.coe_one]
  exact (mul_eq_left₀ hx0).1 h.symm

def kummerCocycle {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1) (hζ : PreTilt.untilt (φi ε) ≠ 1)
    {x : 𝒪♭} (hx : x ≠ 0)
    (hfix : ∀ σ : Gal(PadicAlgCl p/K),
      σ • ((PreTilt.untilt x : 𝒪) : ℂ_[p]) = ((PreTilt.untilt x : 𝒪) : ℂ_[p]))
    (σ : Gal(PadicAlgCl p/K)) : ℤ_[p] :=
  (exists_epsPow_eq hε hζ (exists_tiltGal_eq_mul hx (hfix σ)).choose_spec.1).choose

theorem tiltGal_eq_mul_epsPow {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1) (hζ : PreTilt.untilt (φi ε) ≠ 1) {x : 𝒪♭} (hx : x ≠ 0)
    (hfix : ∀ σ : Gal(PadicAlgCl p/K),
      σ • ((PreTilt.untilt x : 𝒪) : ℂ_[p]) = ((PreTilt.untilt x : 𝒪) : ℂ_[p])) (σ : Gal(PadicAlgCl p/K)) :
    tiltGal σ x = x * epsPow hε (kummerCocycle hε hζ hx hfix σ) := by
  rw [kummerCocycle,
    (exists_epsPow_eq hε hζ (exists_tiltGal_eq_mul hx (hfix σ)).choose_spec.1).choose_spec]
  exact (exists_tiltGal_eq_mul hx (hfix σ)).choose_spec.2

theorem kummerCocycle_eq_of_tiltGal_eq {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1) (hζ : PreTilt.untilt (φi ε) ≠ 1) {x : 𝒪♭} (hx : x ≠ 0)
    (hfix : ∀ σ : Gal(PadicAlgCl p/K),
      σ • ((PreTilt.untilt x : 𝒪) : ℂ_[p]) = ((PreTilt.untilt x : 𝒪) : ℂ_[p])) {σ : Gal(PadicAlgCl p/K)} {a : ℤ_[p]}
    (h : tiltGal σ x = x * epsPow hε a) : kummerCocycle hε hζ hx hfix σ = a :=
  epsPow_injective hε hζ (tilt_mul_left_cancel hx ((tiltGal_eq_mul_epsPow hε hζ hx hfix σ).symm.trans h))

theorem kummerCocycle_mul {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1) (hζ : PreTilt.untilt (φi ε) ≠ 1) {x : 𝒪♭} (hx : x ≠ 0)
    (hfix : ∀ σ : Gal(PadicAlgCl p/K),
      σ • ((PreTilt.untilt x : 𝒪) : ℂ_[p]) = ((PreTilt.untilt x : 𝒪) : ℂ_[p])) (σ τ : Gal(PadicAlgCl p/K)) :
    kummerCocycle hε hζ hx hfix (σ * τ) =
      kummerCocycle hε hζ hx hfix σ + (cycloChar K σ : ℤ_[p]) * kummerCocycle hε hζ hx hfix τ := by
  apply kummerCocycle_eq_of_tiltGal_eq
  rw [tiltGal_mul, tiltGal_eq_mul_epsPow hε hζ hx hfix τ, map_mul,
    tiltGal_eq_mul_epsPow hε hζ hx hfix σ, tiltGal_epsPow, epsPow_add, mul_assoc]

theorem pFlat_ne_zero : pFlat p ≠ 0 := fun h => by
  have h1 := coe_untilt_pFlat (p := p)
  rw [h, IsPerfectoidField.untilt_zero] at h1
  exact natCast_p_ne_zero_cp (p := p) (by simpa using h1.symm)

theorem gal_smul_coe_untilt_pFlat (σ : Gal(PadicAlgCl p/K)) :
    σ • ((PreTilt.untilt (pFlat p) : 𝒪) : ℂ_[p]) = ((PreTilt.untilt (pFlat p) : 𝒪) : ℂ_[p]) := by
  rw [coe_untilt_pFlat, ← galCp_apply, map_natCast]

def kummerC {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1) (hζ : PreTilt.untilt (φi ε) ≠ 1)
    (σ : Gal(PadicAlgCl p/K)) : ℤ_[p] :=
  kummerCocycle hε hζ pFlat_ne_zero gal_smul_coe_untilt_pFlat σ

theorem kummerEta_eq_epsPow {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1) (hζ : PreTilt.untilt (φi ε) ≠ 1)
    (σ : Gal(PadicAlgCl p/K)) : kummerEta σ = epsPow hε (kummerC hε hζ σ) :=
  tilt_mul_left_cancel pFlat_ne_zero ((pFlat_mul_kummerEta σ).symm.trans
    (tiltGal_eq_mul_epsPow hε hζ pFlat_ne_zero gal_smul_coe_untilt_pFlat σ))

theorem kummerC_mul {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1) (hζ : PreTilt.untilt (φi ε) ≠ 1)
    (σ τ : Gal(PadicAlgCl p/K)) :
    kummerC hε hζ (σ * τ) = kummerC hε hζ σ + (cycloChar K σ : ℤ_[p]) * kummerC hε hζ τ :=
  kummerCocycle_mul hε hζ pFlat_ne_zero gal_smul_coe_untilt_pFlat σ τ

local notation "𝕎𝒪♭" => WittVector p (PreTilt (normInteger ℂ_[p]) p)
local notation "𝔹" => BDeRhamPlus (normInteger ℂ_[p]) p
local notation "𝔪" => maximalIdeal (BDeRhamPlus (normInteger ℂ_[p]) p)

theorem fontaineT_congr {η η' : 𝒪♭} (h : η = η') (hη : PreTilt.untilt η = 1)
    (hη' : PreTilt.untilt η' = 1) : fontaineT η hη = fontaineT η' hη' := by
  subst h; rfl

theorem fontaineT_eq_of_forall_untilt {ε ε' : 𝒪♭} (hε : PreTilt.untilt ε = 1)
    (hε' : PreTilt.untilt ε' = 1) (a : ℤ_[p])
    (h : ∀ N, PreTilt.untilt (φi^[N] ε') =
      PreTilt.untilt (φi^[N] ε) ^ (PadicInt.toZModPow N a).val) :
    fontaineT ε' hε' = algebraMap ℚ_[p] 𝔹 (a : ℚ_[p]) * fontaineT ε hε := by
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
  set η := ε' * ((hεu.unit⁻¹ : 𝒪♭ˣ) : 𝒪♭) ^ aN with hη_def
  set ν := φi^[M + k] η with hν_def
  have hη : ε' = ε ^ aN * η := by
    rw [hη_def, ← mul_assoc, mul_comm (ε ^ aN), mul_assoc, ← mul_pow, IsUnit.mul_val_inv, one_pow,
      mul_one]
  have hνη : ν ^ p ^ (M + k) = η := iterate_frobSymm_pow_p_pow η (M + k)
  have hν : PreTilt.untilt ν = 1 := by
    have h2 : PreTilt.untilt (φi^[M + k] ((hεu.unit⁻¹ : 𝒪♭ˣ) : 𝒪♭)) *
        PreTilt.untilt (φi^[M + k] ε) = 1 := by
      rw [← map_mul, ← iterate_frobSymm_mul, IsUnit.val_inv_mul, iterate_frobSymm_one, map_one]
    rw [hν_def, hη_def, iterate_frobSymm_mul, iterate_frobSymm_pow, map_mul, map_pow, h (M + k),
      ← haN, ← mul_pow, mul_comm, h2, one_pow]
  have hξ := IsPerfectoidField.ker_fontaineTheta_eq_span_kerThetaGenerator ℂ_[p] p
  set ξ := IsPerfectoidField.kerThetaGenerator ℂ_[p] p
  obtain ⟨c, hc⟩ : ξ ∣ teichmuller p ν - 1 := by
    have h' : teichmuller p ν - 1 ∈ RingHom.ker (fontaineTheta 𝒪 p) := by
      rw [RingHom.mem_ker, map_sub, map_one, fontaineTheta_teichmuller, hν, sub_self]
    rwa [hξ, mem_span_singleton] at h'
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
    have h' : (aN : ℤ_[p]) - a ∈ RingHom.ker (PadicInt.toZModPow (M + k)) := by
      rw [RingHom.mem_ker, map_sub, map_natCast, haN, ZMod.natCast_zmod_val, sub_self]
    rwa [PadicInt.ker_toZModPow, mem_span_singleton] at h'
  set W := wittToBDeRhamPlus 𝒪 p with hW
  set μ := muBdR p ε with hμ_def
  have hμ : μ = W Zμ := by rw [hμ_def, muBdR_eq, hW, hZμ, map_sub, map_one]
  have hσμ : muBdR p ε' = W Z1 := by rw [muBdR_eq, hW, hZ1, map_sub, map_one]
  have hz0mem : (1 + μ) ^ aN - 1 ∈ 𝔪 := by
    obtain ⟨d, hd⟩ := sub_dvd_pow_sub_pow (1 + μ) 1 aN
    rw [one_pow, add_sub_cancel_left] at hd
    rw [hd]
    exact Ideal.mul_mem_right _ _ (muBdR_mem hε)
  have hz0 : (1 + μ) ^ aN - 1 = W Z0 := by
    rw [hμ, hZ0, hZμ]
    simp only [map_sub, map_pow, map_one]
    ring
  have hσmem : muBdR p ε' ∈ 𝔪 := muBdR_mem hε'
  set t := fontaineT ε hε with ht
  set L1 := logOnePlus 𝔪 (muBdR p ε') hσmem with hL1
  set tN := logOnePlus 𝔪 ((1 + μ) ^ aN - 1) hz0mem with htN
  have E_σ : fontaineT ε' hε' = L1 := rfl
  have E_N : tN = (aN : 𝔹) * t := logOnePlus_pow (muBdR_mem hε) aN hz0mem
  have X1 := factorial_mul_logOnePlus_sub_logPoly_mem hσmem k
  have X0 := factorial_mul_logOnePlus_sub_logPoly_mem hz0mem k
  have X2 := factorial_mul_logOnePlus_sub_logPoly_mem (muBdR_mem hε) k
  have E_P1 : logPoly k (muBdR p ε') = W (logPoly k Z1) := by rw [hσμ, map_logPoly]
  have E_P0 : logPoly k ((1 + μ) ^ aN - 1) = W (logPoly k Z0) := by rw [hz0, map_logPoly]
  have E_Pμ : logPoly k μ = W (logPoly k Zμ) := by rw [hμ, map_logPoly]
  have E_αβ : W (logPoly k Z1) - W (logPoly k Z0) =
      (p : 𝔹) ^ M * W α' + W ξ ^ k * W β' := by
    rw [← map_sub, ← hαβ, map_add, map_mul, map_mul, map_pow, map_pow, map_natCast]
  have E_a : algebraMap ℚ_[p] 𝔹 (a : ℚ_[p]) =
      (aN : 𝔹) - (p : 𝔹) ^ (M + k) * W (IsPerfectoidField.padicIntToWitt (K := ℂ_[p]) p γ) := by
    have h' : a = (aN : ℤ_[p]) - (p : ℤ_[p]) ^ (M + k) * γ := by rw [← hγ]; ring
    rw [h', PadicInt.coe_sub, map_sub, PadicInt.coe_natCast, map_natCast,
      IsPerfectoidField.algebraMap_padic_coe, map_mul, map_mul, map_pow, map_pow, map_natCast,
      map_natCast]
  have hξk : W ξ ^ k * W β' ∈ 𝔪 ^ k := by
    have h1 : W ξ ∈ 𝔪 := by
      rw [IsPerfectoidField.maximalIdeal_bDeRhamPlus_eq_span hξ]
      exact mem_span_singleton_self _
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow h1 k)
  refine ⟨α' + (p : 𝕎𝒪♭) ^ k * IsPerfectoidField.padicIntToWitt (K := ℂ_[p]) p γ * logPoly k Zμ, ?_⟩
  have key : (k.factorial : 𝔹) * (fontaineT ε' hε' - algebraMap ℚ_[p] 𝔹 (a : ℚ_[p]) * t) -
      (p : 𝔹) ^ M * W (α' + (p : 𝕎𝒪♭) ^ k *
        IsPerfectoidField.padicIntToWitt (K := ℂ_[p]) p γ * logPoly k Zμ) =
      ((k.factorial : 𝔹) * L1 - logPoly k (muBdR p ε')) -
        ((k.factorial : 𝔹) * tN - logPoly k ((1 + μ) ^ aN - 1)) + W ξ ^ k * W β' +
        (p : 𝔹) ^ (M + k) * W (IsPerfectoidField.padicIntToWitt (K := ℂ_[p]) p γ) *
          ((k.factorial : 𝔹) * t - logPoly k μ) := by
    rw [map_add, map_mul, map_mul, map_pow, map_natCast]
    linear_combination (k.factorial : 𝔹) * E_σ + (k.factorial : 𝔹) * E_N -
      (k.factorial : 𝔹) * t * E_a + E_P1 - E_P0 + E_αβ +
      (p : 𝔹) ^ (M + k) * W (IsPerfectoidField.padicIntToWitt (K := ℂ_[p]) p γ) * E_Pμ
  rw [key]
  exact add_mem (add_mem (sub_mem X1 X0) hξk) (Ideal.mul_mem_left _ _ X2)

theorem fontaineT_epsPow {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1) (a : ℤ_[p]) :
    fontaineT (epsPow hε a) (untilt_epsPow hε a) = algebraMap ℚ_[p] 𝔹 (a : ℚ_[p]) * fontaineT ε hε :=
  fontaineT_eq_of_forall_untilt hε _ a (untilt_iterate_epsPow hε a)

theorem gal_smul_uBdR_eq {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1) (hζ : PreTilt.untilt (φi ε) ≠ 1)
    (σ : Gal(PadicAlgCl p/K)) :
    σ • uBdR p = uBdR p + algebraMap ℚ_[p] 𝔹 (kummerC hε hζ σ : ℚ_[p]) * fontaineT ε hε := by
  rw [gal_smul_uBdR, fontaineT_congr (kummerEta_eq_epsPow hε hζ σ) _ (untilt_epsPow hε _),
    fontaineT_epsPow]

end Cp

end GroundTheory.PAdicHodge
