import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.StatementG
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.CompInv
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.CurveSer
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.FlowBasic
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.EqWSerSubst
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.LogExp
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.FormalGroupEqWSeries

open PowerSeries

universe u v

noncomputable section

namespace Formalism.L2.Th1.A

namespace ZSer

local notation "FF[" W "](" a ", " b ")" =>
  MvPowerSeries.subst (![a, b] : Fin 2 → PowerSeries _) (fgl W)

section Tools

variable {R : Type u} [CommRing R]

theorem hasSubst_pair {a b : R⟦X⟧} (ha : constantCoeff a = 0) (hb : constantCoeff b = 0) :
    MvPowerSeries.HasSubst (![a, b] : Fin 2 → R⟦X⟧) := by
  apply MvPowerSeries.hasSubst_of_constantCoeff_zero
  intro s
  fin_cases s
  exacts [ha, hb]

theorem subst_pair_subst {a b : R⟦X⟧} (ha : constantCoeff a = 0) (hb : constantCoeff b = 0)
    {g : MvPowerSeries (Fin 2) R} (hg : MvPowerSeries.constantCoeff g = 0) (f : R⟦X⟧) :
    MvPowerSeries.subst (![a, b] : Fin 2 → R⟦X⟧) (f.subst g)
      = f.subst (MvPowerSeries.subst (![a, b] : Fin 2 → R⟦X⟧) g) := by
  have hg' : PowerSeries.HasSubst g := PowerSeries.HasSubst.of_constantCoeff_zero hg
  simp only [PowerSeries.subst]
  rw [MvPowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.const hg') (hasSubst_pair ha hb)]

theorem subst_subst_pair {a b c : R⟦X⟧} (ha : constantCoeff a = 0) (hb : constantCoeff b = 0)
    (hc : constantCoeff c = 0) (g : MvPowerSeries (Fin 2) R) :
    PowerSeries.subst c (MvPowerSeries.subst (![a, b] : Fin 2 → R⟦X⟧) g : R⟦X⟧)
      = MvPowerSeries.subst (![a.subst c, b.subst c] : Fin 2 → R⟦X⟧) g := by
  have hc' := PowerSeries.HasSubst.of_constantCoeff_zero hc
  simp only [PowerSeries.subst]
  rw [MvPowerSeries.subst_comp_subst_apply (hasSubst_pair ha hb) (PowerSeries.HasSubst.const hc')]
  congr 1
  funext s
  fin_cases s <;> rfl

theorem map_subst_pair {S : Type v} [CommRing S] (φ : R →+* S) {a b : R⟦X⟧}
    (ha : constantCoeff a = 0) (hb : constantCoeff b = 0) (g : MvPowerSeries (Fin 2) R) :
    PowerSeries.map φ (MvPowerSeries.subst (![a, b] : Fin 2 → R⟦X⟧) g)
      = MvPowerSeries.subst (![PowerSeries.map φ a, PowerSeries.map φ b] : Fin 2 → S⟦X⟧)
          (MvPowerSeries.map φ g) := by
  refine (MvPowerSeries.map_subst (hasSubst_pair ha hb) (h := φ) g).trans ?_
  congr 1
  funext s
  fin_cases s <;> rfl

theorem map_cc {S : Type v} [CommRing S] (φ : R →+* S) {a : R⟦X⟧} (ha : constantCoeff a = 0) :
    constantCoeff (PowerSeries.map φ a) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, ha, map_zero]

theorem subst_C_mul {s : R⟦X⟧} (hs : HasSubst s) (r : R) (f : R⟦X⟧) :
    (C r * f).subst s = C r * f.subst s := by
  rw [← smul_eq_C_mul, ← smul_eq_C_mul, PowerSeries.subst_smul hs]

theorem cc_subst {g s : R⟦X⟧} (hs : constantCoeff s = 0) :
    constantCoeff (g.subst s) = constantCoeff g := by
  erw [PowerSeries.constantCoeff_subst (HasSubst.of_constantCoeff_zero hs), finsum_eq_single _ 0]
  · simp
  · intro d hd
    simp [hs, hd]
    rw [show MvPowerSeries.constantCoeff s = 0 from hs, zero_pow hd, mul_zero]

theorem coeff_one_subst {f s : R⟦X⟧} (hs : constantCoeff s = 0) :
    coeff 1 (f.subst s) = coeff 1 f * coeff 1 s := by
  have hs' := HasSubst.of_constantCoeff_zero hs
  obtain ⟨t, rfl⟩ : X ∣ s := X_dvd_iff.mpr hs
  erw [PowerSeries.coeff_subst hs', finsum_eq_single _ 1]
  · simp
  · intro d hd
    rcases d with _ | _ | d
    · simp
    · exact absurd rfl hd
    · rw [mul_pow]
      show coeff (d + 1 + 1) f • coeff 1 (X ^ (d + 1 + 1) * t ^ (d + 1 + 1)) = 0
      rw [coeff_X_pow_mul', if_neg (show ¬ (d + 1 + 1 ≤ 1) by omega), smul_zero]

end Tools

section Ring

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

theorem FF_cc {a b : R⟦X⟧} (ha : constantCoeff a = 0) (hb : constantCoeff b = 0) :
    constantCoeff (FF[W](a, b)) = 0 := by
  exact MvPowerSeries.constantCoeff_subst_eq_zero (hasSubst_pair ha hb)
    (fun i => by fin_cases i; exacts [ha, hb]) (Fgl1.fgl_cc W)

theorem FF_map {S : Type v} [CommRing S] (φ : R →+* S) {a b : R⟦X⟧}
    (ha : constantCoeff a = 0) (hb : constantCoeff b = 0) :
    PowerSeries.map φ (FF[W](a, b)) = FF[W.map φ](PowerSeries.map φ a, PowerSeries.map φ b) := by
  rw [map_subst_pair φ ha hb, Fgl1.fgl_map W φ]

theorem iSer_cc : constantCoeff (iSer W) = 0 := by
  rw [iSer, map_mul, constantCoeff_X, zero_mul]

theorem nSer_zero : nSer W 0 = 0 := rfl

theorem nSer_succ (n : ℕ) : nSer W (n + 1) = FF[W](X, nSer W n) := rfl

theorem nSer_cc (n : ℕ) : constantCoeff (nSer W n) = 0 := by
  induction n with
  | zero => rw [nSer_zero, map_zero]
  | succ n ih => rw [nSer_succ]; exact FF_cc W constantCoeff_X ih

theorem zSer_ofNat (n : ℕ) : zSer W (n : ℤ) = nSer W n := rfl

theorem zSer_negSucc (n : ℕ) : zSer W (Int.negSucc n) = (iSer W).subst (nSer W (n + 1)) := rfl

theorem zSer_cc (n : ℤ) : constantCoeff (zSer W n) = 0 := by
  rcases n with n | n
  · exact nSer_cc W n
  · rw [zSer_negSucc, cc_subst (nSer_cc W (n + 1)), iSer_cc]

theorem nSer_map {S : Type v} [CommRing S] (φ : R →+* S) (n : ℕ) :
    PowerSeries.map φ (nSer W n) = nSer (W.map φ) n := by
  induction n with
  | zero => rw [nSer_zero, nSer_zero, map_zero]
  | succ n ih =>
    rw [nSer_succ, nSer_succ, FF_map W φ constantCoeff_X (nSer_cc W n), ih, PowerSeries.map_X]

theorem zSer_map {S : Type v} [CommRing S] (φ : R →+* S) (n : ℤ) :
    PowerSeries.map φ (zSer W n) = zSer (W.map φ) n := by
  rcases n with n | n
  · exact nSer_map W φ n
  · rw [zSer_negSucc, zSer_negSucc]
    refine (PowerSeries.map_subst (HasSubst.of_constantCoeff_zero' (nSer_cc W (n + 1))) (h := φ)
      (iSer W)).trans ?_
    rw [CurveSer.map_iSer]
    exact congrArg (fun t => PowerSeries.subst t (iSer (W.map φ))) (nSer_map W φ (n + 1))

theorem zSer_comp_map {S : Type v} [CommRing S] (φ : R →+* S) (m n : ℤ) :
    PowerSeries.map φ ((zSer W m).subst (zSer W n))
      = (zSer (W.map φ) m).subst (zSer (W.map φ) n) := by
  refine (PowerSeries.map_subst (HasSubst.of_constantCoeff_zero' (zSer_cc W n)) (h := φ)
    (zSer W m)).trans ?_
  rw [zSer_map]
  exact congrArg (fun t => PowerSeries.subst t (zSer (W.map φ) m)) (zSer_map W φ n)

end Ring

section Field

variable {K : Type u} [Field K] [CharZero K] (W : WeierstrassCurve K)

theorem iSerSpec' : ISerSpec.{u} :=
  iSerSpec_of w_series_spec w_series_factorization invariant_differential_units unit_flow chartFlowNegation

theorem log_cc : constantCoeff (logSer W) = 0 := by
  rw [logSer, integ, ← coeff_zero_eq_constantCoeff_apply, coeff_mk, if_pos rfl]

theorem log_one : coeff 1 (logSer W) = 1 := by
  rw [logSer, integ, coeff_mk, if_neg one_ne_zero]
  simp only [Nat.sub_self, coeff_zero_eq_constantCoeff_apply, CurveSer.om_cc, Nat.cast_one, div_one]

theorem log_inj {a b : K⟦X⟧} (ha : constantCoeff a = 0) (hb : constantCoeff b = 0)
    (h : (logSer W).subst a = (logSer W).subst b) : a = b := by
  have hel : (expSer W).subst (logSer W) = X :=
    ((expSpec_of integration_spec composition_inverse_spec invariant_differential_units) K W).2.2.2.1
  exact subst_injective_of_leftInverse (HasSubst.of_constantCoeff_zero' (log_cc W))
    (HasSubst.of_constantCoeff_zero' ha) (HasSubst.of_constantCoeff_zero' hb) hel h

theorem log_FF (hL : FglLog.{u}) {a b : K⟦X⟧} (ha : constantCoeff a = 0)
    (hb : constantCoeff b = 0) :
    (logSer W).subst (FF[W](a, b)) = (logSer W).subst a + (logSer W).subst b := by
  have hab := hasSubst_pair ha hb
  have e := congrArg (MvPowerSeries.subst (![a, b] : Fin 2 → K⟦X⟧)) (hL K W).1
  rw [subst_pair_subst ha hb (Fgl1.fgl_cc W), MvPowerSeries.subst_add hab,
    subst_pair_subst ha hb (MvPowerSeries.constantCoeff_X 0),
    subst_pair_subst ha hb (MvPowerSeries.constantCoeff_X 1),
    MvPowerSeries.subst_X hab, MvPowerSeries.subst_X hab] at e
  exact e

theorem log_nSer (hL : FglLog.{u}) (n : ℕ) :
    (logSer W).subst (nSer W n) = C (n : K) * logSer W := by
  have hX : (logSer W).subst (X : K⟦X⟧) = logSer W := by
    rw [← PowerSeries.map_algebraMap_eq_subst_X]
    rfl
  induction n with
  | zero =>
    rw [nSer_zero, Nat.cast_zero, map_zero, zero_mul]
    exact PowerSeries.subst_zero_of_constantCoeff_zero (log_cc W)
  | succ n ih =>
    rw [nSer_succ, log_FF W hL constantCoeff_X (nSer_cc W n), ih, hX, Nat.cast_succ, map_add, map_one,
      add_mul, one_mul, add_comm]

theorem log_zSer (hL : FglLog.{u}) (n : ℤ) :
    (logSer W).subst (zSer W n) = C (n : K) * logSer W := by
  rcases n with n | n
  · show (logSer W).subst (nSer W n) = C (((n : ℕ) : ℤ) : K) * logSer W
    exact_mod_cast log_nSer W hL n
  · have hs := nSer_cc W (n + 1)
    have hS : (logSer W).subst (iSer W) = -logSer W :=
      ((logNeg_of integration_spec composition_inverse_spec invariant_differential_units iSerSpec') K W).1
    rw [zSer_negSucc, ← PowerSeries.subst_comp_subst_apply (HasSubst.of_constantCoeff_zero' (iSer_cc W))
      (HasSubst.of_constantCoeff_zero' hs), hS, subst_neg' (HasSubst.of_constantCoeff_zero' hs),
      log_nSer W hL (n + 1), Int.cast_negSucc, map_neg, neg_mul]

theorem field_add (hL : FglLog.{u}) (m n : ℤ) :
    FF[W](zSer W m, zSer W n) = zSer W (m + n) := by
  apply log_inj W (FF_cc W (zSer_cc W m) (zSer_cc W n)) (zSer_cc W (m + n))
  rw [log_FF W hL (zSer_cc W m) (zSer_cc W n), log_zSer W hL m, log_zSer W hL n, log_zSer W hL (m + n),
    Int.cast_add, map_add, add_mul]

theorem field_mul (hL : FglLog.{u}) (m n : ℤ) :
    (zSer W m).subst (zSer W n) = zSer W (m * n) := by
  have hm := HasSubst.of_constantCoeff_zero (zSer_cc W m)
  have hn := HasSubst.of_constantCoeff_zero (zSer_cc W n)
  have hcc : constantCoeff ((zSer W m).subst (zSer W n)) = 0 := by
    rw [cc_subst (zSer_cc W n)]
    exact zSer_cc W m
  apply log_inj W hcc (zSer_cc W (m * n))
  rw [← PowerSeries.subst_comp_subst_apply hm hn, log_zSer W hL m, subst_C_mul hn, log_zSer W hL n,
    log_zSer W hL (m * n), Int.cast_mul, map_mul, mul_assoc]

theorem field_one (hL : FglLog.{u}) : zSer W 1 = X := by
  have h1 := log_zSer W hL 1
  apply log_inj W (zSer_cc W 1) constantCoeff_X
  rw [h1, Int.cast_one, map_one, one_mul]
  have hx : (fun _ : Unit => (X : K⟦X⟧)) = MvPowerSeries.X := by
    funext u
    rfl
  simp only [PowerSeries.subst]
  rw [hx, MvPowerSeries.subst_self]
  rfl

theorem field_coeff (hL : FglLog.{u}) (n : ℤ) : coeff 1 (zSer W n) = (n : K) := by
  have h := congrArg (coeff 1) (log_zSer W hL n)
  rw [coeff_one_subst (zSer_cc W n), log_one, one_mul, coeff_C_mul, log_one, mul_one] at h
  exact h

end Field

section Transfer

open Univ

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

theorem zSer_univ (n : ℤ) : PowerSeries.map (φ_of W) (zSer W₀ n) = zSer W n := by
  rw [zSer_map]
  congr 1
  ext <;> simp [W₀, φ_of]

theorem ring_add (hL : FglLog.{0}) (m n : ℤ) :
    FF[W](zSer W m, zSer W n) = zSer W (m + n) := by
  have h : PowerSeries.map Univ.ι (FF[W₀](zSer W₀ m, zSer W₀ n))
      = PowerSeries.map Univ.ι (zSer W₀ (m + n)) := by
    rw [FF_map W₀ Univ.ι (zSer_cc W₀ m) (zSer_cc W₀ n), zSer_map, zSer_map, zSer_map]
    exact field_add Univ.WK hL m n
  have h2 := Univ.ps_transfer W h
  rw [FF_map W₀ (Univ.φ_of W) (zSer_cc W₀ m) (zSer_cc W₀ n), zSer_univ, zSer_univ, zSer_univ,
    Univ.map_eq] at h2
  exact h2

theorem ring_mul (hL : FglLog.{0}) (m n : ℤ) :
    (zSer W m).subst (zSer W n) = zSer W (m * n) := by
  have h : PowerSeries.map Univ.ι ((zSer W₀ m).subst (zSer W₀ n))
      = PowerSeries.map Univ.ι (zSer W₀ (m * n)) := by
    rw [zSer_comp_map, zSer_map]
    exact field_mul Univ.WK hL m n
  have h2 := Univ.ps_transfer W h
  rw [zSer_comp_map, zSer_univ, Univ.map_eq] at h2
  exact h2

theorem ring_one (hL : FglLog.{0}) : zSer W 1 = X := by
  have h : PowerSeries.map Univ.ι (zSer W₀ 1) = PowerSeries.map Univ.ι X := by
    rw [zSer_map, PowerSeries.map_X]
    exact field_one Univ.WK hL
  have h2 := Univ.ps_transfer W h
  rw [zSer_univ, PowerSeries.map_X] at h2
  exact h2

theorem ring_coeff (hL : FglLog.{0}) (n : ℤ) : coeff 1 (zSer W n) = (n : R) := by
  have h1 : Univ.ι (coeff 1 (zSer W₀ n)) = Univ.ι (n : Univ.Z) := by
    rw [← PowerSeries.coeff_map, zSer_map, map_intCast]
    exact field_coeff Univ.WK hL n
  have h2 : coeff 1 (zSer W₀ n) = (n : Univ.Z) := Univ.ι_injective h1
  rw [← zSer_univ W n, PowerSeries.coeff_map, h2, map_intCast]

theorem nSer_two_coeff (hL : FglLog.{0}) : coeff 1 (nSer W 2) = 2 := by
  have h : coeff 1 (zSer W ((2 : ℕ) : ℤ)) = (((2 : ℕ) : ℤ) : R) := ring_coeff W hL _
  rw [zSer_ofNat] at h
  rw [h]
  norm_num

theorem nSer_one (hL : FglLog.{0}) : nSer W 1 = X := by
  have h := ring_one W hL
  rwa [show (1 : ℤ) = ((1 : ℕ) : ℤ) from rfl, zSer_ofNat] at h

theorem nSer_two (hL : FglLog.{0}) : nSer W 2 = FF[W](X, X) := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, nSer_succ, nSer_one W hL]

end Transfer

end ZSer

theorem z_series_map : ZSerMap.{u, v} := by
  intro R S _ _ φ W n
  exact ZSer.zSer_map W φ n

theorem zSerLog_of (hL : FglLog.{u}) : ZSerLog.{u} := by
  intro K _ _ W n
  exact ZSer.log_zSer W hL n

theorem zSerSpec_of (hL : FglLog.{0}) : ZSerSpec.{u} := by
  intro R _ W
  refine ⟨fun n => ⟨ZSer.zSer_cc W n, ZSer.ring_coeff W hL n⟩, rfl, ZSer.ring_one W hL, ?_,
    fun n => ZSer.zSer_ofNat W n, fun m n => ZSer.ring_add W hL m n, fun m n => ZSer.ring_mul W hL m n⟩
  show (iSer W).subst (nSer W 1) = iSer W
  rw [ZSer.nSer_one W hL]
  have hx : (fun _ : Unit => (X : R⟦X⟧)) = MvPowerSeries.X := by
    funext u
    rfl
  simp only [PowerSeries.subst]
  rw [hx, MvPowerSeries.subst_self]
  rfl

theorem halfSpec_of (hL : FglLog.{0}) : HalfSpec.{u} := by
  intro R _ W h2
  have hc : coeff 1 (nSer W 2) = 2 := ZSer.nSer_two_coeff W hL
  have hu : IsUnit (coeff 1 (nSer W 2)) := by
    rw [hc]
    exact h2
  obtain ⟨hh0, hsh, hhs, hm, -, -⟩ := composition_inverse_spec R (nSer W 2) (ZSer.nSer_cc W 2) hu
  have hh0' : constantCoeff (halfSer W) = 0 := hh0
  have hh : HasSubst (halfSer W) := HasSubst.of_constantCoeff_zero' hh0'
  refine ⟨hh0', ?_, hsh, hhs, ?_⟩
  · rw [mul_comm, ← hc]
    exact hm
  · have key : PowerSeries.subst (halfSer W) (MvPowerSeries.subst (![X, X] : Fin 2 → R⟦X⟧) (fgl W) : R⟦X⟧)
        = MvPowerSeries.subst (![(X : R⟦X⟧).subst (halfSer W), (X : R⟦X⟧).subst (halfSer W)] : Fin 2 → R⟦X⟧)
            (fgl W) :=
      ZSer.subst_subst_pair constantCoeff_X constantCoeff_X hh0' (fgl W)
    rw [PowerSeries.subst_X hh] at key
    rw [← key, ← ZSer.nSer_two W hL]
    exact hsh

theorem halfLog_of (hL : FglLog.{u}) (hL0 : FglLog.{0}) : HalfLog.{u, v} := by
  refine ⟨fun K _ _ W => ?_, fun R S _ _ φ W h2 => ?_⟩
  · obtain ⟨hh0, -, hsh, -, -⟩ := halfSpec_of hL0 K W (isUnit_iff_ne_zero.mpr two_ne_zero)
    have hh := HasSubst.of_constantCoeff_zero' hh0
    have hX : (logSer W).subst (X : K⟦X⟧) = logSer W := by
      rw [← PowerSeries.map_algebraMap_eq_subst_X]
      rfl
    have e2 : PowerSeries.subst (halfSer W) ((logSer W).subst (nSer W 2)) = logSer W := by
      rw [PowerSeries.subst_comp_subst_apply (HasSubst.of_constantCoeff_zero' (ZSer.nSer_cc W 2)) hh, hsh, hX]
    rw [ZSer.log_nSer W hL 2, ZSer.subst_C_mul hh, Nat.cast_ofNat, map_ofNat] at e2
    exact e2
  · have hc : coeff 1 (nSer W 2) = 2 := ZSer.nSer_two_coeff W hL0
    have hu : IsUnit (coeff 1 (nSer W 2)) := by
      rw [hc]
      exact h2
    show PowerSeries.map φ (compInv (nSer W 2)) = compInv (nSer (W.map φ) 2)
    rw [composition_inverse_map R S φ (nSer W 2) (ZSer.nSer_cc W 2) hu, ZSer.nSer_map]

end Formalism.L2.Th1.A
