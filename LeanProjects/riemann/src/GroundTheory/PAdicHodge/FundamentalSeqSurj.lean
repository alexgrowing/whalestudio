import Mathlib
import GroundTheory.PAdicHodge.FundamentalSeqLog
import GroundTheory.PAdicHodge.GalSmulAlgebraMapPadicPlus
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open _root_.WittVector

namespace ACris

variable {p : ℕ} [hp : Fact p.Prime]

local notation "𝒪" => normInteger ℂ_[p]
local notation "𝒪♭" => PreTilt (normInteger ℂ_[p]) p
local notation "𝔹" => BDeRhamPlus (normInteger ℂ_[p]) p
local notation "𝔭" => Ideal.span {(p : ACris ℂ_[p] p)}
local notation "θdR" => IsPerfectoidField.thetaBDeRhamPlusField (K := ℂ_[p]) p

theorem exists_untilt_eq_of_cp (π : 𝒪) : ∃ x : 𝒪♭, PreTilt.untilt x = π := by
  have hp0 : 0 < p := hp.out.pos
  let root : 𝒪 → 𝒪 := fun z =>
    ⟨Classical.choose (IsAlgClosed.exists_pow_nat_eq (z : ℂ_[p]) hp0), mem_normInteger.2 (by
      have h := Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq (z : ℂ_[p]) hp0)
      have h2 : ‖Classical.choose (IsAlgClosed.exists_pow_nat_eq (z : ℂ_[p]) hp0)‖ ^ p ≤ 1 := by
        rw [← norm_pow, h]; exact mem_normInteger.1 z.2
      exact (pow_le_one_iff_of_nonneg (norm_nonneg _) hp0.ne').1 h2)⟩
  have hroot : ∀ z, root z ^ p = z := fun z => Subtype.ext (by
    simp only [root, SubmonoidClass.coe_pow]
    exact Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq (z : ℂ_[p]) hp0))
  let y : ℕ → 𝒪 := fun n => root^[n] π
  have hy : ∀ n, y (n + 1) ^ p = y n := fun n => by
    simp only [y, Function.iterate_succ_apply', hroot]
  exact ⟨IsPerfectoidField.ofCompatible p y hy, by rw [IsPerfectoidField.untilt_ofCompatible]; rfl⟩

theorem exists_phi_eq_p_mul_theta_sub_mem (c : 𝒪) :
    ∃ u : ACris ℂ_[p] p, phi ℂ_[p] p u = (p : ACris ℂ_[p] p) * u ∧
      theta ℂ_[p] p u - (p : 𝒪) ^ 2 * c ∈ Ideal.span {(p : 𝒪) ^ 3} := by
  obtain ⟨x, hx⟩ := exists_untilt_eq_of_cp (1 + (p : 𝒪) ^ 2 * c)
  have h1 : PreTilt.untilt x - 1 = (p : 𝒪) ^ 2 * c := by rw [hx]; ring
  have hmem : PreTilt.untilt x - 1 ∈ Ideal.span {(p : 𝒪)} := by
    rw [h1, Ideal.mem_span_singleton']
    exact ⟨p * c, by ring⟩
  exact ⟨logTeich hmem, phi_logTeich hmem, theta_logTeich_sub_mem hmem h1⟩

theorem exists_phi_eq_p_mul_theta_eq (c : 𝒪) :
    ∃ u : ACris ℂ_[p] p, phi ℂ_[p] p u = (p : ACris ℂ_[p] p) * u ∧
      theta ℂ_[p] p u = (p : 𝒪) ^ 2 * c := by
  choose g hgφ hgθ using exists_phi_eq_p_mul_theta_sub_mem (p := p)
  have he : ∀ c, ∃ e : 𝒪, theta ℂ_[p] p (g c) = (p : 𝒪) ^ 2 * c - (p : 𝒪) ^ 3 * e := fun c => by
    obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.1 (hgθ c)
    exact ⟨-e, by linear_combination -he⟩
  choose e he using he
  set cs : ℕ → 𝒪 := fun j => e^[j] c with hcs
  have hcs1 : ∀ j, e (cs j) = cs (j + 1) := fun j => by
    simp only [hcs, Function.iterate_succ_apply']
  set a : ℕ → ACris ℂ_[p] p := fun j => (p : ACris ℂ_[p] p) ^ j * g (cs j) with ha_def
  have ha : ∀ k, ∃ N, ∀ n, N ≤ n → a n ∈ 𝔭 ^ k := fun k => ⟨k, fun n hn => by
    rw [Ideal.span_singleton_pow]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton.2 (pow_dvd_pow _ hn))⟩
  obtain ⟨s, hs⟩ := exists_isAdicSum ha
  refine ⟨s, ?_, ?_⟩
  · have h1 := (hs.map (phi ℂ_[p] p) span_p_le_comap_phi).congr
      (b := fun n => (p : ACris ℂ_[p] p) * a n) (fun n => by
        simp only [ha_def]
        rw [map_mul, map_pow, map_natCast, hgφ]
        ring)
    exact h1.unique (hs.mul_left _)
  · have hle : 𝔭 ≤ (Ideal.span {(p : 𝒪)}).comap (theta ℂ_[p] p) := by
      rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_natCast]
      exact Ideal.mem_span_singleton_self _
    have h1 := hs.map (theta ℂ_[p] p) hle
    have htel : ∀ M, ∑ j ∈ Finset.range M, theta ℂ_[p] p (a j) =
        (p : 𝒪) ^ 2 * c - (p : 𝒪) ^ (M + 2) * cs M := by
      intro M
      induction M with
      | zero => simp [hcs]
      | succ M ih =>
        rw [Finset.sum_range_succ, ih]
        simp only [ha_def]
        rw [map_mul, map_pow, map_natCast, he, hcs1]
        ring
    have h2 : IsAdicSum (Ideal.span {(p : 𝒪)}) (fun n => theta ℂ_[p] p (a n))
        ((p : 𝒪) ^ 2 * c) := fun k => ⟨k, fun M hM => by
      rw [htel, sub_sub_cancel, Ideal.span_singleton_pow]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton.2 (pow_dvd_pow _ (by omega)))⟩
    exact h1.unique h2

section Plus

set_option maxHeartbeats 1600000 in

theorem phiPlus_eq_of_mul_eq {y : (BCrisPlus ℂ_[p] p)} {a : ACris ℂ_[p] p} {k m : ℕ}
    (hy : y * (p : (BCrisPlus ℂ_[p] p)) ^ k = algebraMap (ACris ℂ_[p] p) (BCrisPlus ℂ_[p] p) a)
    (ha : phi ℂ_[p] p a = (p : ACris ℂ_[p] p) ^ m * a) :
    phiPlus ℂ_[p] p y = (p : (BCrisPlus ℂ_[p] p)) ^ m * y := by
  have h := congrArg (phiPlus ℂ_[p] p) hy
  rw [map_mul, map_pow, map_natCast, phiPlus_algebraMap, ha, map_mul, map_pow, map_natCast,
    ← hy] at h
  exact (isUnit_p_bCrisPlus.pow k).mul_right_cancel (by rw [h]; ring)

set_option maxHeartbeats 1600000 in

theorem exists_phiPlus_eq_theta_eq (c : ℂ_[p]) :
    ∃ y : (BCrisPlus ℂ_[p] p), phiPlus ℂ_[p] p y = (p : (BCrisPlus ℂ_[p] p)) * y ∧ θdR (iotaPlus ℂ_[p] p y) = c := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ‖(p : ℂ_[p]) ^ N * c‖ ≤ 1 := by
    rcases eq_or_ne c 0 with rfl | hc
    · exact ⟨0, by simp⟩
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (inv_pos.2 (norm_pos_iff.2 hc))
      (norm_natCast_p_lt_one (p := p))
    refine ⟨N, ?_⟩
    rw [norm_mul, norm_pow]
    calc ‖(p : ℂ_[p])‖ ^ N * ‖c‖ ≤ ‖c‖⁻¹ * ‖c‖ := by gcongr
      _ = 1 := inv_mul_cancel₀ (norm_ne_zero_iff.2 hc)
  set c' : 𝒪 := ⟨(p : ℂ_[p]) ^ N * c, mem_normInteger.2 hN⟩ with hc'
  have hc'' : (c' : ℂ_[p]) = (p : ℂ_[p]) ^ N * c := rfl
  obtain ⟨u, hφ, hθ⟩ := exists_phi_eq_p_mul_theta_eq c'
  obtain ⟨y, hy⟩ : ∃ y : (BCrisPlus ℂ_[p] p), y * (p : (BCrisPlus ℂ_[p] p)) ^ (N + 2) = algebraMap (ACris ℂ_[p] p) (BCrisPlus ℂ_[p] p) u :=
    ⟨algebraMap (ACris ℂ_[p] p) (BCrisPlus ℂ_[p] p) u * Ring.inverse (p : (BCrisPlus ℂ_[p] p)) ^ (N + 2), by
      rw [mul_assoc, ← mul_pow, Ring.inverse_mul_cancel _ isUnit_p_bCrisPlus, one_pow, mul_one]⟩
  refine ⟨y, by simpa using phiPlus_eq_of_mul_eq hy (m := 1) (by rw [hφ, pow_one]), ?_⟩
  have h := congrArg (fun z => θdR (iotaPlus ℂ_[p] p z)) hy
  simp only [map_mul, map_pow, map_natCast, thetaField_iotaPlus_algebraMap, hθ] at h
  have hp0 : (p : ℂ_[p]) ^ (N + 2) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hp.out.ne_zero)
  apply mul_right_cancel₀ hp0
  rw [h]
  push_cast
  rw [hc'']
  ring

set_option maxHeartbeats 1600000 in

theorem exists_phiPlus_eq_pow_theta_eq {m : ℕ} (hm : 1 ≤ m) (c : ℂ_[p]) :
    ∃ y : (BCrisPlus ℂ_[p] p), phiPlus ℂ_[p] p y = (p : (BCrisPlus ℂ_[p] p)) ^ m * y ∧ θdR (iotaPlus ℂ_[p] p y) = c := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  obtain ⟨y1, h1, h1'⟩ := exists_phiPlus_eq_theta_eq c
  obtain ⟨y0, h0, h0'⟩ := exists_phiPlus_eq_theta_eq (p := p) 1
  refine ⟨y1 * y0 ^ k, ?_, ?_⟩
  · rw [map_mul, map_pow, h1, h0]
    ring
  · rw [map_mul, map_mul, map_pow, map_pow, h1', h0', one_pow, mul_one]

variable {ε : PreTilt (normInteger ℂ_[p]) p} (hε : PreTilt.untilt ε = 1)
  (hζ : PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt (normInteger ℂ_[p]) p) p).symm ε) ≠ 1)

abbrev periodTPlus : (BCrisPlus ℂ_[p] p) := algebraMap (ACris ℂ_[p] p) (BCrisPlus ℂ_[p] p) (periodT hε)

set_option maxHeartbeats 1600000 in
theorem phiPlus_periodTPlus : phiPlus ℂ_[p] p (periodTPlus hε) = (p : (BCrisPlus ℂ_[p] p)) * periodTPlus hε := by
  rw [periodTPlus, phiPlus_algebraMap, phi_periodT_eq_mul, map_mul, map_natCast]

set_option maxHeartbeats 1600000 in
theorem iotaPlus_periodTPlus : iotaPlus ℂ_[p] p (periodTPlus hε) = fontaineT ε hε := by
  rw [periodTPlus, iotaPlus_algebraMap, iota_periodT]

include hζ in

theorem mem_span_fontaineT_of_theta_eq_zero {r : 𝔹} (hr : θdR r = 0) :
    r ∈ Ideal.span {fontaineT ε hε} := by
  rw [← maximalIdeal_eq_span_fontaineT hε hζ, IsPerfectoidField.maximalIdeal_bDeRhamPlus]
  exact hr

set_option maxHeartbeats 1600000 in
include hζ in

theorem exists_phiPlus_eq_pow_iotaPlus_sub_mem {m n : ℕ} (hnm : n ≤ m) (w : 𝔹) :
    ∃ y : (BCrisPlus ℂ_[p] p), phiPlus ℂ_[p] p y = (p : (BCrisPlus ℂ_[p] p)) ^ m * y ∧
      iotaPlus ℂ_[p] p y - w ∈ Ideal.span {fontaineT ε hε ^ n} := by
  induction n with
  | zero =>
    refine ⟨0, by simp, ?_⟩
    rw [pow_zero, Ideal.span_singleton_one]
    exact Submodule.mem_top
  | succ n ih =>
    obtain ⟨y, hy, hyw⟩ := ih (by omega)
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.1 hyw
    obtain ⟨z, hz, hz'⟩ := exists_phiPlus_eq_pow_theta_eq (p := p) (m := m - n) (by omega) (-θdR d)
    refine ⟨y + periodTPlus hε ^ n * z, ?_, ?_⟩
    · have hpm : (p : (BCrisPlus ℂ_[p] p)) ^ m = (p : (BCrisPlus ℂ_[p] p)) ^ n * (p : (BCrisPlus ℂ_[p] p)) ^ (m - n) := by
        rw [← pow_add, Nat.add_sub_cancel' (by omega)]
      rw [map_add, map_mul, map_pow, hy, hz, phiPlus_periodTPlus, mul_pow, hpm]
      ring
    · have h0 : θdR (d + iotaPlus ℂ_[p] p z) = 0 := by rw [map_add, hz', add_neg_cancel]
      obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.1 (mem_span_fontaineT_of_theta_eq_zero hε hζ h0)
      rw [Ideal.mem_span_singleton']
      refine ⟨e, ?_⟩
      rw [map_add, map_mul, map_pow, iotaPlus_periodTPlus, add_sub_right_comm, ← hd, pow_succ]
      linear_combination (fontaineT ε hε ^ n) * he

end Plus

end ACris

end GroundTheory.PAdicHodge
