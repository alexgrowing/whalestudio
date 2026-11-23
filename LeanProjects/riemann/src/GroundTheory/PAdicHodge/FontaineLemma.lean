import Mathlib
import GroundTheory.PAdicHodge.FontaineLemmaPhi
import GroundTheory.PAdicHodge.FontaineLemmaPeriod
set_option maxSynthPendingDepth 1

namespace GroundTheory.PAdicHodge

open _root_.WittVector

namespace ACris

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p] [CharZero K]

local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "θ" => fontaineTheta (normInteger K) p
local notation "φ" => WittVector.frobeniusEquiv p (PreTilt (normInteger K) p)
local notation "θdR" => IsPerfectoidField.thetaBDeRhamPlusField (K := K) p

theorem iterate_phiPlus_algebraMap (n : ℕ) (x : ACris K p) :
    (phiPlus K p)^[n] (algebraMap (ACris K p) (BCrisPlus K p) x) =
      algebraMap (ACris K p) (BCrisPlus K p) ((phi K p)^[n] x) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, phiPlus_algebraMap, Function.iterate_succ_apply']

theorem thetaField_iotaPlus_algebraMap (x : ACris K p) :
    θdR (iotaPlus K p (algebraMap (ACris K p) (BCrisPlus K p) x)) = (theta K p x : K) := by
  rw [iotaPlus_algebraMap, thetaField_iota]

theorem theta_phi_iterate_eq_zero_of_mul_eq {y : BCrisPlus K p} {a : ACris K p} {k : ℕ}
    (hya : y * algebraMap (ACris K p) (BCrisPlus K p) ((p : ACris K p) ^ k) =
      algebraMap (ACris K p) (BCrisPlus K p) a)
    (hy : ∀ n : ℕ, θdR (iotaPlus K p ((phiPlus K p)^[n] y)) = 0) (n : ℕ) :
    theta K p ((phi K p)^[n] a) = 0 := by
  apply Subtype.ext
  rw [ZeroMemClass.coe_zero, ← thetaField_iotaPlus_algebraMap, ← iterate_phiPlus_algebraMap, ← hya,
    ← RingHom.coe_pow, map_mul, map_mul, map_mul, RingHom.coe_pow, hy n, zero_mul]

set_option maxHeartbeats 1600000 in

theorem phiPlus_mem_span_periodT {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1)
    (hζ : PreTilt.untilt ((_root_.frobeniusEquiv 𝒪♭ p).symm ε) ≠ 1) {y : BCrisPlus K p}
    (hy : ∀ n : ℕ, θdR (iotaPlus K p ((phiPlus K p)^[n] y)) = 0) :
    phiPlus K p y ∈ Ideal.span {algebraMap (ACris K p) (BCrisPlus K p) (periodT hε)} := by
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers (p : ACris K p)) y
  obtain ⟨k, hk⟩ := s.2
  simp only at hs
  rw [← hk] at hs
  have ha := theta_phi_iterate_eq_zero_of_mul_eq hs hy

  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 (p_mul_phi_mem_span_mu hε hζ ha)
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (mu_mem_span_periodT (K := K) hε hζ)
  have hpa : (p : ACris K p) * phi K p a = periodT hε * (c * w) := by
    rw [← hw, ← hc]; ring

  have h1 := congrArg (phiPlus K p) hs
  rw [map_mul, phiPlus_algebraMap, phiPlus_algebraMap, map_pow, map_natCast] at h1
  have hu : IsUnit (algebraMap (ACris K p) (BCrisPlus K p) ((p : ACris K p) ^ (k + 1))) :=
    IsLocalization.map_units (BCrisPlus K p)
      (⟨(p : ACris K p) ^ (k + 1), k + 1, rfl⟩ : Submonoid.powers (p : ACris K p))
  rw [Ideal.mem_span_singleton']
  refine ⟨algebraMap (ACris K p) (BCrisPlus K p) (c * w) * ↑hu.unit⁻¹, ?_⟩
  have h2 : phiPlus K p y * algebraMap (ACris K p) (BCrisPlus K p) ((p : ACris K p) ^ (k + 1)) =
      algebraMap (ACris K p) (BCrisPlus K p) (periodT hε) *
        algebraMap (ACris K p) (BCrisPlus K p) (c * w) := by
    rw [pow_succ, map_mul, ← mul_assoc, h1, ← map_mul, mul_comm (phi K p a), hpa, map_mul]
  calc algebraMap (ACris K p) (BCrisPlus K p) (c * w) * ↑hu.unit⁻¹ *
        algebraMap (ACris K p) (BCrisPlus K p) (periodT hε)
      = phiPlus K p y * algebraMap (ACris K p) (BCrisPlus K p) ((p : ACris K p) ^ (k + 1)) *
          ↑hu.unit⁻¹ := by rw [h2]; ring
    _ = phiPlus K p y := by rw [mul_assoc, IsUnit.mul_val_inv, mul_one]

set_option maxHeartbeats 1600000 in

theorem mem_span_xi_of_forall_imp {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1)
    (hζ : PreTilt.untilt ((_root_.frobeniusEquiv 𝒪♭ p).symm ε) ≠ 1)
    (H : ∀ y : BCrisPlus K p, (∀ n : ℕ, θdR (iotaPlus K p ((phiPlus K p)^[n] y)) = 0) →
      y ∈ Ideal.span {algebraMap (ACris K p) (BCrisPlus K p) (periodT hε)})
    {z : BCrisPlus K p} (hz : θdR (iotaPlus K p z) = 0) :
    z ∈ Ideal.span {algebraMap (AInf K p) (BCrisPlus K p) (AInf.xi ε)} := by
  set v : AInf K p := (φ).symm (AInf.mu ε) with hv
  set V : BCrisPlus K p := algebraMap (AInf K p) (BCrisPlus K p) v with hV
  have hVa : ∀ w : AInf K p, algebraMap (AInf K p) (BCrisPlus K p) w =
      algebraMap (ACris K p) (BCrisPlus K p) (algebraMap (AInf K p) (ACris K p) w) :=
    fun w => IsScalarTower.algebraMap_apply _ _ _ w
  have hθV : ∀ n : ℕ, θdR (iotaPlus K p ((phiPlus K p)^[n] V)) = θ ((φ ^ n) v) := by
    intro n
    rw [hV, hVa, iterate_phiPlus_algebraMap, thetaField_iotaPlus_algebraMap,
      theta_phi_iterate_algebraMap]

  have hyz : ∀ n : ℕ, θdR (iotaPlus K p ((phiPlus K p)^[n] (V * z))) = 0 := by
    intro n
    rw [← RingHom.coe_pow, map_mul, map_mul, map_mul, RingHom.coe_pow, hθV]
    rcases n with _ | n
    · rw [Function.iterate_zero_apply, hz, mul_zero]
    · rw [pow_succ, RingAut.mul_apply, hv, RingEquiv.apply_symm_apply,
        AInf.fontaineTheta_frobenius_pow_mu hε, ZeroMemClass.coe_zero, zero_mul]
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 (H _ hyz)
  obtain ⟨u, -, hu⟩ := exists_periodT_eq_mu_mul_unit hε hζ

  have e : V * z = V * (algebraMap (AInf K p) (BCrisPlus K p) (AInf.xi ε) *
      (algebraMap (ACris K p) (BCrisPlus K p) u * a)) := by
    rw [← ha, hu, map_mul, ← hVa, AInf.mu_eq_xi_mul ε, map_mul, ← hv, ← hV]
    ring
  have hV0 : iotaPlus K p V ≠ 0 := by
    intro h0
    have h1 := hθV 0
    rw [Function.iterate_zero_apply, h0, map_zero, pow_zero, RingAut.one_apply, hv,
      AInf.frobeniusEquiv_symm_mu, map_sub, map_one, fontaineTheta_teichmuller] at h1
    apply hζ
    have h2 : ((PreTilt.untilt ((_root_.frobeniusEquiv 𝒪♭ p).symm ε) - 1 :
        normInteger K) : K) = 0 := h1.symm
    rw [AddSubgroupClass.coe_sub, OneMemClass.coe_one, sub_eq_zero] at h2
    exact Subtype.ext (by rw [h2, OneMemClass.coe_one])
  have e2 := congrArg (iotaPlus K p) e
  rw [map_mul, map_mul (iotaPlus K p) V] at e2
  have e3 := iotaPlus_injective (K := K) (p := p) (mul_left_cancel₀ hV0 e2)
  rw [Ideal.mem_span_singleton']
  exact ⟨algebraMap (ACris K p) (BCrisPlus K p) u * a, by rw [e3]; ring⟩

end ACris

end GroundTheory.PAdicHodge
