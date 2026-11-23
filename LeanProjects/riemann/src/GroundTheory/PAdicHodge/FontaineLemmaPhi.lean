import Mathlib
import GroundTheory.PAdicHodge.FontaineLemmaAInf
import GroundTheory.PAdicHodge.ACrisFrobFixed
import GroundTheory.PowerSubgroups.CountableNeighbourhoods.FontainePhiPowerSubgroups
set_option maxSynthPendingDepth 1

namespace GroundTheory.PAdicHodge

open _root_.WittVector

section Iteration

variable {A R ι : Type*} [CommRing A] [CommRing R]

theorem exists_eq_add_mul_of_forall {a : A} {r : R} [IsAdicComplete (Ideal.span {a}) A]
    [IsAdicComplete (Ideal.span {r}) R] (f : A →+* R) (hf : f a = r) (X : R) (ψ : ι → R)
    (h : ∀ y, ∃ b : A, ∃ s : R, ∃ y' : ι, ψ y = f b + X * s + r * ψ y') (y : ι) :
    ∃ b : A, ∃ s : R, ψ y = f b + X * s :=
  _root_.GroundTheory.Variant₂.N1.exists_eq_add_mul_of_forall' f hf X ψ h y

end Iteration

namespace ACris

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]

local notation "𝒪" => normInteger K
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "θ" => fontaineTheta (normInteger K) p
local notation "𝔸" => Localization.Away (p : AInf K p)
local notation "φ" => WittVector.frobeniusEquiv p (PreTilt (normInteger K) p)

theorem exists_p_mul_eq_frobenius_sub {ξ : AInf K p} (hξ : ξ ∈ RingHom.ker θ) :
    ∃ X : ACrisZero K p, (p : 𝔸) * (X : 𝔸) = algebraMap (AInf K p) 𝔸 (φ ξ) - p := by
  obtain ⟨c, hc⟩ := exists_frobenius_eq ξ
  refine ⟨⟨algebraMap (AInf K p) 𝔸 c + ((p - 1).factorial : 𝔸) * dpow p ξ - 1,
    sub_mem (add_mem (Subalgebra.algebraMap_mem _ c)
      (Subalgebra.mul_mem _ (Subalgebra.natCast_mem _ _) (dpow_mem hξ p))) (one_mem _)⟩, ?_⟩
  have h1 := factorial_mul_dpow (K := K) p ξ
  have h2 : algebraMap (AInf K p) 𝔸 (φ ξ) =
      algebraMap (AInf K p) 𝔸 ξ ^ p + (p : 𝔸) * algebraMap (AInf K p) 𝔸 c := by
    rw [hc, map_add, map_pow, map_mul, map_natCast]
  have h3 : (p : 𝔸) * ((p - 1).factorial : 𝔸) = (p.factorial : 𝔸) := by
    rw [← Nat.cast_mul, Nat.mul_factorial_pred hp.out.ne_zero]
  show (p : 𝔸) * (algebraMap (AInf K p) 𝔸 c + ((p - 1).factorial : 𝔸) * dpow p ξ - 1) = _
  linear_combination dpow p ξ * h3 + h1 - h2

theorem exists_phiAway_eq_add_mul {ξ : AInf K p} (hξ : RingHom.ker θ = Ideal.span {ξ})
    {X : ACrisZero K p} (hX : (p : 𝔸) * (X : 𝔸) = algebraMap (AInf K p) 𝔸 (φ ξ) - p) {y : 𝔸}
    (hy : y ∈ ACrisZero K p) :
    ∃ b : AInf K p, ∃ s ∈ ACrisZero K p,
      phiAway K p y = algebraMap (AInf K p) 𝔸 b + (X : 𝔸) * s := by
  induction hy using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨n, x, hx, rfl⟩ := hy
    rw [hξ] at hx
    obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    obtain ⟨w, hw⟩ := exists_natCast_mul_eq_pow (K := K) (p := p) (Nat.factorial_ne_zero n)
      (factorization_factorial_le (p := p) n)

    have hd : dpow n (φ ξ) = algebraMap (AInf K p) 𝔸 w * (1 + (X : 𝔸)) ^ n := by
      rw [dpow_eq_iff, ← mul_assoc, ← map_natCast (algebraMap (AInf K p) 𝔸), ← map_mul, hw,
        map_pow, map_natCast, ← mul_pow, mul_add, mul_one, hX, add_sub_cancel]
    set g := ∑ i ∈ Finset.range n, (1 + (X : 𝔸)) ^ i
    have hg : g ∈ ACrisZero K p :=
      Subalgebra.sum_mem _ fun i _ => Subalgebra.pow_mem _ (add_mem (one_mem _) X.2) i
    have hgeom : (1 + (X : 𝔸)) ^ n = 1 + (X : 𝔸) * g := by
      have := geom_sum_mul (1 + (X : 𝔸)) n
      rw [add_sub_cancel_left] at this
      rw [mul_comm, this]; ring
    refine ⟨w * φ d ^ n, algebraMap (AInf K p) 𝔸 w * g * algebraMap (AInf K p) 𝔸 (φ d) ^ n,
      Subalgebra.mul_mem _ (Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ w) hg)
        (Subalgebra.pow_mem _ (Subalgebra.algebraMap_mem _ _) n), ?_⟩
    rw [phiAway_dpow, map_mul, mul_comm (φ d) (φ ξ), dpow_mul, hd, hgeom, map_mul, map_pow]
    ring
  | algebraMap r =>
    exact ⟨φ r, 0, zero_mem _, by rw [phiAway_algebraMap, mul_zero, add_zero]⟩
  | add y₁ y₂ _ _ h₁ h₂ =>
    obtain ⟨w₁, z₁, hz₁, e₁⟩ := h₁
    obtain ⟨w₂, z₂, hz₂, e₂⟩ := h₂
    exact ⟨w₁ + w₂, z₁ + z₂, add_mem hz₁ hz₂, by rw [map_add, e₁, e₂, map_add]; ring⟩
  | mul y₁ y₂ _ _ h₁ h₂ =>
    obtain ⟨w₁, z₁, hz₁, e₁⟩ := h₁
    obtain ⟨w₂, z₂, hz₂, e₂⟩ := h₂
    refine ⟨w₁ * w₂, algebraMap (AInf K p) 𝔸 w₁ * z₂ + z₁ * algebraMap (AInf K p) 𝔸 w₂ +
      (X : 𝔸) * z₁ * z₂, ?_, by rw [map_mul, e₁, e₂, map_mul]; ring⟩
    exact add_mem (add_mem (Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) hz₂)
      (Subalgebra.mul_mem _ hz₁ (Subalgebra.algebraMap_mem _ _)))
      (Subalgebra.mul_mem _ (Subalgebra.mul_mem _ X.2 hz₁) hz₂)

set_option maxHeartbeats 1600000 in

theorem exists_phi_eq_add_mul [CharZero K] {ξ : AInf K p} (hξ : RingHom.ker θ = Ideal.span {ξ})
    {X : ACrisZero K p} (hX : (p : 𝔸) * (X : 𝔸) = algebraMap (AInf K p) 𝔸 (φ ξ) - p)
    (y : ACris K p) :
    ∃ b : AInf K p, ∃ s : ACris K p, phi K p y =
      algebraMap (AInf K p) (ACris K p) b + algebraMap (ACrisZero K p) (ACris K p) X * s := by
  refine exists_eq_add_mul_of_forall (a := (p : AInf K p)) (r := (p : ACris K p))
    (algebraMap (AInf K p) (ACris K p)) (map_natCast _ p) _ (phi K p) (fun y => ?_) y
  obtain ⟨y₀, z₁, rfl⟩ := exists_eq_add_p_pow_mul 1 y
  obtain ⟨b, s, hs, e⟩ := exists_phiAway_eq_add_mul hξ hX y₀.2
  refine ⟨b, algebraMap (ACrisZero K p) (ACris K p) ⟨s, hs⟩, z₁, ?_⟩
  have e' : phiZero K p y₀ = algebraMap (AInf K p) (ACrisZero K p) b + X * ⟨s, hs⟩ :=
    Subtype.ext (by rw [coe_phiZero, e]; rfl)
  have hof : phi K p (algebraMap (ACrisZero K p) (ACris K p) y₀) =
      algebraMap (ACrisZero K p) (ACris K p) (phiZero K p y₀) := phi_of y₀
  have hb : algebraMap (AInf K p) (ACris K p) b =
      algebraMap (ACrisZero K p) (ACris K p) (algebraMap (AInf K p) (ACrisZero K p) b) :=
    AdicCompletion.algebraMap_apply _ b
  rw [map_add, map_mul, pow_one, map_natCast, hof, e', map_add, map_mul, hb]

theorem frobenius_xi_sub_mem_span_mu {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1)
    (hζ : PreTilt.untilt ((_root_.frobeniusEquiv 𝒪♭ p).symm ε) ≠ 1) :
    φ (AInf.xi ε) - p ∈ Ideal.span {AInf.mu (K := K) ε} := by
  refine AInf.mem_span_mu_of_forall hε hζ fun n => ?_
  rw [map_sub, map_natCast, map_sub, map_natCast, ← RingAut.mul_apply, ← pow_succ,
    AInf.fontaineTheta_frobenius_pow_succ_xi hε n, sub_self]

section Theta

variable [CharZero K]

theorem theta_phi_iterate_algebraMap (n : ℕ) (w : AInf K p) :
    theta K p ((phi K p)^[n] (algebraMap (AInf K p) (ACris K p) w)) = θ ((φ ^ n) w) := by
  rw [phi_iterate_algebraMap, theta_algebraMap]

set_option maxHeartbeats 1600000 in

theorem p_mul_phi_mem_span_mu {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1)
    (hζ : PreTilt.untilt ((_root_.frobeniusEquiv 𝒪♭ p).symm ε) ≠ 1) {y : ACris K p}
    (hy : ∀ n : ℕ, theta K p ((phi K p)^[n] y) = 0) :
    (p : ACris K p) * phi K p y ∈
      Ideal.span {algebraMap (AInf K p) (ACris K p) (AInf.mu ε)} := by
  have hξ := AInf.ker_fontaineTheta_eq_span_xi hε hζ
  have hξk : AInf.xi ε ∈ RingHom.ker θ := by rw [hξ]; exact Ideal.mem_span_singleton_self _
  obtain ⟨X, hX⟩ := exists_p_mul_eq_frobenius_sub hξk
  obtain ⟨b, s, e⟩ := exists_phi_eq_add_mul hξ hX y
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.1 (frobenius_xi_sub_mem_span_mu hε hζ)

  have hXc : (p : ACris K p) * algebraMap (ACrisZero K p) (ACris K p) X =
      algebraMap (AInf K p) (ACris K p) (AInf.mu ε) * algebraMap (AInf K p) (ACris K p) d := by
    have h1 : (p : ACrisZero K p) * X =
        algebraMap (AInf K p) (ACrisZero K p) (AInf.mu ε * d) := by
      apply Subtype.ext
      rw [Subalgebra.coe_mul, SubringClass.coe_natCast, hX, Subalgebra.coe_algebraMap, mul_comm,
        hd, map_sub, map_natCast]
    have hof : algebraMap (ACrisZero K p) (ACris K p) ((p : ACrisZero K p) * X) =
        algebraMap (AInf K p) (ACris K p) (AInf.mu ε * d) := by
      rw [h1]
      exact (AdicCompletion.algebraMap_apply _ _).symm
    rw [map_mul, map_natCast] at hof
    rw [hof, map_mul]
  have hp0 := AInf.natCast_ne_zero hε hζ

  have e2 : (p : ACris K p) * phi K p y =
      algebraMap (AInf K p) (ACris K p) ((p : AInf K p) * b) +
        algebraMap (AInf K p) (ACris K p) (AInf.mu ε * d) * s := by
    rw [e, mul_add, ← mul_assoc, hXc, map_mul, map_mul, map_natCast]
  have hb : ∀ n : ℕ, θ ((φ ^ n) b) = 0 := by
    intro n
    set Φ := phi K p ^ n with hΦ
    have hΦa : ∀ w, theta K p (Φ (algebraMap (AInf K p) (ACris K p) w)) = θ ((φ ^ n) w) :=
      fun w => by rw [hΦ, RingHom.coe_pow, theta_phi_iterate_algebraMap]
    have h : theta K p (Φ (phi K p y)) = 0 := by
      rw [hΦ, RingHom.coe_pow, ← Function.iterate_succ_apply]
      exact hy (n + 1)
    have hl : theta K p (Φ ((p : ACris K p) * phi K p y)) = 0 := by
      rw [map_mul, map_natCast, map_mul, map_natCast, h, mul_zero]
    have hr : theta K p (Φ (algebraMap (AInf K p) (ACris K p) ((p : AInf K p) * b) +
        algebraMap (AInf K p) (ACris K p) (AInf.mu ε * d) * s)) = (p : 𝒪) * θ ((φ ^ n) b) := by
      rw [map_add, map_mul Φ, map_add, map_mul (theta K p), hΦa, hΦa,
        AInf.fontaineTheta_frobenius_pow_mul_mu hε, zero_mul, add_zero, map_mul, map_natCast,
        map_mul, map_natCast]
    rw [e2, hr] at hl
    exact (mul_eq_zero.1 hl).resolve_left hp0
  obtain ⟨β, hβ⟩ := Ideal.mem_span_singleton'.1 (AInf.mem_span_mu_of_forall hε hζ hb)
  rw [Ideal.mem_span_singleton']
  refine ⟨(p : ACris K p) * algebraMap (AInf K p) (ACris K p) β +
    algebraMap (AInf K p) (ACris K p) d * s, ?_⟩
  rw [e2, ← hβ]
  simp only [map_mul, map_natCast]
  ring

end Theta

end ACris

end GroundTheory.PAdicHodge
