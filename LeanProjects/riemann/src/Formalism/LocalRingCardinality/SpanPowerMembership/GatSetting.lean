import Formalism.SharpRestriction.GrowthBounds.UnramifiedQuadraticSetting
import Formalism.LocalRingCardinality.SpanPowerMembership.GatRing

noncomputable section

namespace Formalism.BasicNotions.Examples₂.LevelValuationRings

open Formalism.MainNotions.G QuadraticAlgebra

variable (p : ℕ) [hp : Fact p.Prime] (n : ℕ)

abbrev Wn : Type := WittVector p (GaloisField p n)

abbrev Qn : Type := FractionRing (Wn p n)

abbrev On : Type := QuadraticAlgebra (Wn p n) (p : Wn p n) 0

instance instDomOn : IsDomain (On p n) := GatR.isDomain (WittVector.irreducible p)
instance instDvrOn : IsDiscreteValuationRing (On p n) := GatR.isDVR (WittVector.irreducible p)

abbrev Kn : Type := FractionRing (On p n)

def sigN : Qn p n ≃+* Qn p n :=
  IsFractionRing.ringEquivOfRingEquiv (WittVector.frobeniusEquiv p (GaloisField p n))

theorem sigN_alg (x : Wn p n) :
    sigN p n (algebraMap (Wn p n) (Qn p n) x) = algebraMap (Wn p n) (Qn p n) (WittVector.frobenius x) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap _ x

theorem inj_WK : Function.Injective ((algebraMap (On p n) (Kn p n)).comp (algebraMap (Wn p n) (On p n))) :=
  (IsFractionRing.injective (On p n) (Kn p n)).comp algebraMap_injective

def iotaN : Qn p n →+* Kn p n := IsFractionRing.lift (inj_WK p n)

theorem frob_iter (hn : n ≠ 0) (x : Wn p n) : (WittVector.frobenius^[n]) x = x := by
  ext i
  rw [WittVector.iterate_frobenius_coeff]
  have : Fintype (GaloisField p n) := Fintype.ofFinite _
  have h := FiniteField.pow_card (x.coeff i)
  rwa [← Nat.card_eq_fintype_card, GaloisField.card p n hn] at h

theorem sigN_pow_alg (k : ℕ) (x : Wn p n) :
    (sigN p n ^ k) (algebraMap (Wn p n) (Qn p n) x) =
      algebraMap (Wn p n) (Qn p n) ((WittVector.frobenius^[k]) x) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', Function.iterate_succ_apply']
    show sigN p n ((sigN p n ^ k) _) = _
    rw [ih, sigN_alg]

theorem sigN_period (hn : n ≠ 0) : sigN p n ^ n = 1 := by
  apply RingEquiv.toRingHom_injective
  apply IsLocalization.ringHom_ext (nonZeroDivisors (Wn p n))
  ext1 x
  show (sigN p n ^ n) (algebraMap (Wn p n) (Qn p n) x) = algebraMap (Wn p n) (Qn p n) x
  rw [sigN_pow_alg, frob_iter p n hn]

theorem hidaSettingOfEven (h5 : 5 ≤ p) (h2 : 2 ≤ n) (he : Even n) :
    HidaSetting p n (Wn p n) (Qn p n) (On p n) (Kn p n) (iotaN p n) (sigN p n)
      (algebraMap (Wn p n) (On p n)) ω where
  prime := hp.out
  five_le := h5
  two_le := h2
  even := he
  frac_alt := inferInstance
  frac_O := inferInstance
  p_unif := WittVector.irreducible p
  res_card := by
    rw [Nat.card_congr (WittVector.quotientPEquiv (p := p) (k := GaloisField p n)).toEquiv,
      GaloisField.card p n (by omega)]
  eq_sum_herm_smul_frame_of_inW := inferInstance
  frob := fun x => by
    have h : WittVector.frobenius x - x ^ p ∈ Ideal.span {(p : Wn p n)} := by
      rw [WittVector.mem_span_p_iff_coeff_zero_eq_zero]
      show WittVector.constantCoeff (WittVector.frobenius x - x ^ p) = 0
      rw [map_sub, map_pow]
      show (WittVector.frobenius x).coeff 0 - x.coeff 0 ^ p = 0
      rw [WittVector.coeff_frobenius_charP, sub_self]
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp h
    exact ⟨y, by rw [sigN_alg, ← hy]; congr 1; ring⟩
  period := sigN_period p n (by omega)
  ι_comp := fun x => IsFractionRing.lift_algebraMap (inj_WK p n) x
  finite := RingHom.finite_algebraMap.mpr inferInstance
  complete_O := GatR.isAdicComplete (WittVector.irreducible p) inferInstance
  w_sq := by rw [GatR.om_sq, map_natCast]

end Formalism.BasicNotions.Examples₂.LevelValuationRings
