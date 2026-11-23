import Mathlib
import GroundTheory.PAdicHodge.ACrisBdRGalois
import GroundTheory.PAdicHodge.UnramifiedClosure
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open _root_.WittVector

namespace ACris

section General

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]

local notation "𝒪" => normInteger K
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "θ" => fontaineTheta (normInteger K) p
local notation "𝔸" => Localization.Away (p : AInf K p)
local notation "φ" => WittVector.frobeniusEquiv p (PreTilt (normInteger K) p)

theorem exists_dpow_frobenius_eq_p_mul {x : AInf K p} (hx : x ∈ RingHom.ker θ) {n : ℕ}
    (hn : n ≠ 0) : ∃ z ∈ ACrisZero K p, dpow n (φ x) = (p : 𝔸) * z := by
  obtain ⟨y, hy⟩ := exists_frobenius_eq x
  set b : 𝔸 := ((p - 1).factorial : 𝔸) * dpow p x + algebraMap (AInf K p) 𝔸 y
  have hb : b ∈ ACrisZero K p :=
    add_mem (Subalgebra.mul_mem _ (Subalgebra.natCast_mem _ _) (dpow_mem hx p))
      (Subalgebra.algebraMap_mem _ y)
  have hpb : (p : 𝔸) * b = algebraMap (AInf K p) 𝔸 (φ x) := by
    have h1 : ((p : ℕ) : 𝔸) * ((p - 1).factorial : 𝔸) = (p.factorial : 𝔸) := by
      rw [← Nat.cast_mul, Nat.mul_factorial_pred hp.out.ne_zero]
    rw [hy, map_add, map_mul, map_pow, map_natCast, mul_add, ← mul_assoc, h1, factorial_mul_dpow]
  have hv : (n.factorial).factorization p ≤ n - 1 := by
    rw [Nat.factorization_def _ hp.out]
    have := padicValNat_factorial_lt_of_ne_zero p hn
    omega
  obtain ⟨c, hc⟩ := exists_natCast_mul_eq_pow (K := K) (p := p) (Nat.factorial_ne_zero n) hv
  refine ⟨algebraMap (AInf K p) 𝔸 c * b ^ n, Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ c)
    (Subalgebra.pow_mem _ hb n), ?_⟩
  rw [dpow_eq_iff, ← hpb, mul_pow]
  have h2 : (n.factorial : 𝔸) * algebraMap (AInf K p) 𝔸 c = (p : 𝔸) ^ (n - 1) := by
    rw [← map_natCast (algebraMap (AInf K p) 𝔸), ← map_mul, hc, map_pow, map_natCast]
  calc (n.factorial : 𝔸) * ((p : 𝔸) * (algebraMap (AInf K p) 𝔸 c * b ^ n))
      = (p : 𝔸) * ((n.factorial : 𝔸) * algebraMap (AInf K p) 𝔸 c) * b ^ n := by ring
    _ = (p : 𝔸) ^ n * b ^ n := by
        rw [h2, ← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hn)]

theorem exists_phiAway_eq {y : 𝔸} (hy : y ∈ ACrisZero K p) :
    ∃ w : AInf K p, ∃ z ∈ ACrisZero K p,
      phiAway K p y = algebraMap (AInf K p) 𝔸 w + (p : 𝔸) * z := by
  induction hy using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨n, x, hx, rfl⟩ := hy
    rw [phiAway_dpow]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ⟨1, 0, zero_mem _, by rw [dpow_zero, map_one, mul_zero, add_zero]⟩
    · obtain ⟨z, hz, hzeq⟩ := exists_dpow_frobenius_eq_p_mul hx hn.ne'
      exact ⟨0, z, hz, by rw [hzeq, map_zero, zero_add]⟩
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
      (p : 𝔸) * z₁ * z₂, ?_, by rw [map_mul, e₁, e₂, map_mul]; ring⟩
    exact add_mem (add_mem (Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) hz₂)
      (Subalgebra.mul_mem _ hz₁ (Subalgebra.algebraMap_mem _ _)))
      (Subalgebra.mul_mem _ (Subalgebra.mul_mem _ (Subalgebra.natCast_mem _ _) hz₁) hz₂)

variable [CharZero K]

omit [CharZero K] in
theorem of_eq_algebraMap (t : ACrisZero K p) :
    _root_.AdicCompletion.of (Ideal.span {(p : ACrisZero K p)}) (ACrisZero K p) t =
      algebraMap (ACrisZero K p) (ACris K p) t :=
  rfl

set_option maxHeartbeats 1600000 in

theorem exists_eq_add_p_pow_mul (k : ℕ) (y : ACris K p) :
    ∃ yk : ACrisZero K p, ∃ z : ACris K p,
      y = algebraMap (ACrisZero K p) (ACris K p) yk + (p : ACris K p) ^ k * z := by
  obtain ⟨yk, hyk⟩ := Ideal.Quotient.mk_surjective
    (_root_.AdicCompletion.evalₐ (Ideal.span {(p : ACrisZero K p)}) k y)
  have hker : y - _root_.AdicCompletion.of _ _ yk ∈ Ideal.span {(p : ACris K p)} ^ k := by
    rw [← span_p_pow_map, ← ker_adicCompletion_evalₐ (Submodule.fg_span_singleton _),
      RingHom.mem_ker]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_sub]
    rw [← hyk]
    exact sub_eq_zero.2 (_root_.AdicCompletion.evalₐ_of _ k yk).symm
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hker
  obtain ⟨z, hz⟩ := hker
  refine ⟨yk, z, ?_⟩
  rw [← of_eq_algebraMap, mul_comm (_ ^ k) z, hz]
  exact (add_sub_cancel _ _).symm

set_option maxHeartbeats 1600000 in

theorem exists_phi_eq (y : ACris K p) :
    ∃ w : AInf K p, ∃ z : ACris K p,
      phi K p y = algebraMap (AInf K p) (ACris K p) w + (p : ACris K p) * z := by
  obtain ⟨y₀, z₁, rfl⟩ := exists_eq_add_p_pow_mul 1 y
  obtain ⟨w, z, hz, e⟩ := exists_phiAway_eq y₀.2
  refine ⟨w, algebraMap (ACrisZero K p) (ACris K p) ⟨z, hz⟩ + phi K p z₁, ?_⟩
  have e' : phiZero K p y₀ = algebraMap (AInf K p) (ACrisZero K p) w +
      (p : ACrisZero K p) * ⟨z, hz⟩ :=
    Subtype.ext (by rw [coe_phiZero, e]; rfl)
  have hof : phi K p (algebraMap (ACrisZero K p) (ACris K p) y₀) =
      algebraMap (ACrisZero K p) (ACris K p) (phiZero K p y₀) := phi_of y₀
  have hw : algebraMap (AInf K p) (ACris K p) w =
      algebraMap (ACrisZero K p) (ACris K p) (algebraMap (AInf K p) (ACrisZero K p) w) :=
    AdicCompletion.algebraMap_apply _ w
  rw [map_add, map_mul, pow_one, map_natCast, hof, e', map_add, map_mul, map_natCast, hw, mul_add,
    add_assoc]

omit [CharZero K] in

theorem phi_iterate_algebraMap (n : ℕ) (w : AInf K p) :
    (phi K p)^[n] (algebraMap (AInf K p) (ACris K p) w) =
      algebraMap (AInf K p) (ACris K p) ((φ ^ n) w) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, phi_algebraMap, pow_succ', RingAut.mul_apply]

set_option maxHeartbeats 1600000 in

theorem exists_phi_iterate_eq (n : ℕ) (y : ACris K p) :
    ∃ w : AInf K p, ∃ z : ACris K p,
      (phi K p)^[n] y = algebraMap (AInf K p) (ACris K p) w + (p : ACris K p) ^ n * z := by
  induction n with
  | zero => exact ⟨0, y, by rw [Function.iterate_zero_apply, map_zero, pow_zero, one_mul, zero_add]⟩
  | succ n ih =>
    obtain ⟨w, z, e⟩ := ih
    obtain ⟨w', z', e'⟩ := exists_phi_eq (K := K) z
    refine ⟨φ w + (p : AInf K p) ^ n * w', z', ?_⟩
    rw [Function.iterate_succ_apply', e, map_add, map_mul, map_pow, map_natCast, phi_algebraMap, e',
      map_add, map_mul, map_pow, map_natCast, mul_add, ← add_assoc, ← mul_assoc, ← pow_succ]

theorem thetaField_toBDeRhamPlus (a : 𝔸) :
    IsPerfectoidField.thetaBDeRhamPlusField p (toBDeRhamPlus (normInteger K) p a) =
      thetaAway K p a :=
  rfl

theorem exists_thetaField_iota_eq (y : ACris K p) :
    ∃ a : ACrisZero K p,
      IsPerfectoidField.thetaBDeRhamPlusField p (iota K p y) = thetaAway K p (a : 𝔸) := by
  obtain ⟨a, ha, hae⟩ := Subring.mem_map.1 (embedding₂ K p 1 y).2
  refine ⟨⟨a, ha⟩, ?_⟩
  let B := _root_.AdicCompletion (kerAway K p) 𝔸
  let G : B →+* K := IsPerfectoidField.thetaBDeRhamPlusField (K := K) p
  let ι' : ACris K p →+* B := iota K p
  have hι : ∀ y, _root_.AdicCompletion.evalₐ (kerAway K p) 1 (ι' y) = iotaQ K p 1 y :=
    fun y => evalₐ_iota 1 y
  let b : B := ι' y - ι' (_root_.AdicCompletion.of _ _ ⟨a, ha⟩)
  have h1 : _root_.AdicCompletion.evalₐ (kerAway K p) 1 b = 0 := by
    change _root_.AdicCompletion.evalₐ (kerAway K p) 1
      (ι' y - ι' (_root_.AdicCompletion.of _ _ ⟨a, ha⟩)) = 0
    rw [map_sub, hι, hι, iotaQ_of, sub_eq_zero]
    exact hae.symm
  have h2 : b ∈ (kerAway K p ^ 1).map (algebraMap 𝔸 B) := by
    rw [← ker_adicCompletion_evalₐ (fg_ker_fontaineThetaInvertP ker_eq_span_xiGen) 1,
      RingHom.mem_ker]
    exact h1
  have hle : (kerAway K p ^ 1).map (algebraMap 𝔸 B) ≤ RingHom.ker G := by
    rw [pow_one, Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, RingHom.mem_ker]
    change thetaAway K p x = 0
    rw [thetaAway, RingHom.comp_apply, RingHom.mem_ker.1 hx, map_zero]
  have h0 : G b = 0 := RingHom.mem_ker.1 (hle h2)
  have h3 : G b = IsPerfectoidField.thetaBDeRhamPlusField p (iota K p y) -
      thetaAway K p a := by
    change IsPerfectoidField.thetaBDeRhamPlusField p
      (iota K p y - iota K p (_root_.AdicCompletion.of _ _ ⟨a, ha⟩)) = _
    rw [map_sub, iota_of, thetaField_toBDeRhamPlus]
  rw [h3, sub_eq_zero] at h0
  exact h0

theorem thetaField_iota (y : ACris K p) :
    IsPerfectoidField.thetaBDeRhamPlusField p (iota K p y) = (theta K p y : K) := by
  let F : ACris K p →+* normInteger K :=
    ((IsPerfectoidField.thetaBDeRhamPlusField p).comp (iota K p)).codRestrict (normInteger K)
      fun y => by
        obtain ⟨a, ha⟩ := exists_thetaField_iota_eq (K := K) (p := p) y
        rw [RingHom.comp_apply, ha]
        exact acrisZero_le_thetaIntegral a.2
  have hF : F = theta K p := ringHom_ext fun a => Subtype.ext (by
    change IsPerfectoidField.thetaBDeRhamPlusField p (iota K p (_root_.AdicCompletion.of _ _ a)) = _
    rw [iota_of, thetaField_toBDeRhamPlus, theta_of, coe_thetaZero])
  exact congrArg Subtype.val (RingHom.congr_fun hF y)

set_option maxHeartbeats 1600000 in

theorem exists_theta_eq_sum_of_phi_iterate {y : ACris K p} {N : ℕ} (hN : 1 ≤ N)
    (hy : (phi K p)^[N] y = y) {m : ℕ} (hm : 1 ≤ m) :
    ∃ c : ℕ → normInteger K, ∀ j : ℕ, ∃ e : normInteger K,
      (theta K p y : K) = ∑ i ∈ Finset.range m, (p : K) ^ i * ((c i : K)) ^ p ^ (N * j) +
        (p : K) ^ m * (e : K) := by
  have hfix : ∀ j, (phi K p)^[N * j] y = y := fun j => by
    rw [Function.iterate_mul]; exact Function.iterate_fixed hy j
  obtain ⟨w, z, e⟩ := exists_phi_iterate_eq (N * m) y
  rw [hfix m] at e
  set z' := (p : ACris K p) ^ (N * m - m) * z
  have e' : y = algebraMap (AInf K p) (ACris K p) w + (p : ACris K p) ^ m * z' := by
    rw [e, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' (Nat.le_mul_of_pos_left m hN)]
  set a : ℕ → 𝒪♭ := fun n => ((_root_.frobeniusEquiv 𝒪♭ p).symm ^ n) (w.coeff n)
  have hw : WittVector.teichmullerSeries a = w := WittVector.teichmullerSeries_coeff_eq w
  obtain ⟨w'', hw''⟩ := WittVector.dvd_sub_sum_teichmullerSeries a (m - 1)
  rw [hw, Nat.sub_add_cancel hm] at hw''
  have hIic : Finset.Iic (m - 1) = Finset.range m := by
    ext i; simp only [Finset.mem_Iic, Finset.mem_range]; omega
  rw [hIic] at hw''
  refine ⟨fun i => PreTilt.untilt (a i), fun j => ?_⟩
  set n := N * j

  have hyn : y = algebraMap (AInf K p) (ACris K p) ((φ ^ n) w) +
      (p : ACris K p) ^ m * ((phi K p ^ n) z') := by
    conv_lhs => rw [← hfix j, ← RingHom.coe_pow, e']
    rw [map_add, map_mul, map_pow, map_natCast, RingHom.coe_pow, phi_iterate_algebraMap]
  have hwn : (φ ^ n) w = ∑ i ∈ Finset.range m, teichmuller p (a i ^ p ^ n) * (p : AInf K p) ^ i +
      (p : AInf K p) ^ m * (φ ^ n) w'' := by
    have hw2 : w = ∑ i ∈ Finset.range m, teichmuller p (a i) * (p : AInf K p) ^ i +
        (p : AInf K p) ^ m * w'' := by rw [← hw'']; ring
    conv_lhs => rw [hw2]
    rw [map_add, map_sum, map_mul, map_pow, map_natCast]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_pow, map_natCast, WittVector.frobeniusEquiv_pow_teichmuller]
  refine ⟨θ ((φ ^ n) w'') + theta K p ((phi K p ^ n) z'), ?_⟩
  conv_lhs => rw [hyn]
  rw [map_add, map_mul, map_pow, map_natCast, theta_algebraMap, hwn, map_add, map_sum, map_mul,
    map_pow, map_natCast]
  simp only [map_mul, map_pow, map_natCast, fontaineTheta_teichmuller]
  push_cast
  ring_nf
  congr 1
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

end General

section Cp

variable {p : ℕ} [hp : Fact p.Prime]

theorem exists_theta_approx_of_phi_iterate {y : ACris ℂ_[p] p} {N : ℕ} (hN : 1 ≤ N)
    (hy : (phi ℂ_[p] p)^[N] y = y) (m : ℕ) :
    ∃ u ∈ unramifiedClosure p,
      ‖((theta ℂ_[p] p y : normInteger ℂ_[p]) : ℂ_[p]) - (u : ℂ_[p])‖ ≤ ‖(p : ℂ_[p])‖ ^ m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · refine ⟨0, zero_mem _, ?_⟩
    simpa using mem_normInteger.1 (theta ℂ_[p] p y).2
  obtain ⟨c, hc⟩ := exists_theta_eq_sum_of_phi_iterate hN hy hm
  have hc1 : ∀ i, ‖(c i : ℂ_[p])‖ ≤ 1 := fun i => mem_normInteger.1 (c i).2
  choose Kf hK using fun i => eventually_approx_pow (hc1 i) m
  set J := ∑ i ∈ Finset.range m, Kf i
  have hJ : ∀ i ∈ Finset.range m, Kf i ≤ N * J := fun i hi =>
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hi).trans (Nat.le_mul_of_pos_left J hN)
  choose! u hu hclose using fun i (hi : i ∈ Finset.range m) => hK i (N * J) (hJ i hi)
  obtain ⟨e, he⟩ := hc J
  refine ⟨∑ i ∈ Finset.range m, (p : PadicAlgCl p) ^ i * u i,
    sum_mem fun i hi => mul_mem (pow_mem (natCast_mem _ p) i) (hu i hi), ?_⟩
  have hp1 : ‖(p : ℂ_[p])‖ ≤ 1 := norm_natCast_p_lt_one.le
  have hcoe : ((∑ i ∈ Finset.range m, (p : PadicAlgCl p) ^ i * u i : PadicAlgCl p) : ℂ_[p]) =
      ∑ i ∈ Finset.range m, (p : ℂ_[p]) ^ i * (u i : ℂ_[p]) := by
    simp only [PadicComplex.coe_eq, map_sum, map_mul, map_pow, map_natCast]
  rw [he, hcoe]
  have hdiff : ∑ i ∈ Finset.range m, (p : ℂ_[p]) ^ i * (c i : ℂ_[p]) ^ p ^ (N * J) +
      (p : ℂ_[p]) ^ m * (e : ℂ_[p]) - ∑ i ∈ Finset.range m, (p : ℂ_[p]) ^ i * (u i : ℂ_[p]) =
      ∑ i ∈ Finset.range m, (p : ℂ_[p]) ^ i * ((c i : ℂ_[p]) ^ p ^ (N * J) - (u i : ℂ_[p])) +
        (p : ℂ_[p]) ^ m * (e : ℂ_[p]) := by
    rw [add_sub_right_comm, ← Finset.sum_sub_distrib]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hdiff]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun i hi => ?_
    rw [norm_mul, norm_pow]
    exact (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hp1)).trans
      (hclose i hi)
  · rw [norm_mul, norm_pow]
    exact mul_le_of_le_one_right (by positivity) (mem_normInteger.1 e.2)

end Cp

end ACris

end GroundTheory.PAdicHodge
