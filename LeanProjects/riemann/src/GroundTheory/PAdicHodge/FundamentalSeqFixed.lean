import Mathlib
import GroundTheory.PAdicHodge.FundamentalSeqSurj
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open _root_.WittVector Polynomial

namespace ACris

variable {p : ℕ} [hp : Fact p.Prime]

local notation "𝒪" => normInteger ℂ_[p]
local notation "𝔹" => BDeRhamPlus (normInteger ℂ_[p]) p
local notation "𝔭" => Ideal.span {(p : ACris ℂ_[p] p)}
local notation "θdR" => IsPerfectoidField.thetaBDeRhamPlusField (K := ℂ_[p]) p

section Residue

theorem prod_range_X_sub_C_zmod :
    ∏ a ∈ Finset.range p, (X - C ((a : ℕ) : ZMod p)) = X ^ p - X := by
  have hmon : (X ^ p - X : (ZMod p)[X]).Monic :=
    (monic_X_pow p).sub_of_left (by rw [degree_X, degree_X_pow]; exact_mod_cast hp.out.one_lt)
  have hr : (X ^ p - X : (ZMod p)[X]).roots = Finset.univ.val := by
    simpa [ZMod.card] using FiniteField.roots_X_pow_card_sub_X (ZMod p)
  have hdeg : (X ^ p - X : (ZMod p)[X]).natDegree = p :=
    FiniteField.X_pow_card_sub_X_natDegree_eq (ZMod p) hp.out.one_lt
  have h := prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmon (by
    rw [hr, hdeg, Finset.card_val, Finset.card_univ, ZMod.card])
  rw [hr, ← Finset.prod_eq_multiset_prod] at h
  rw [← h]
  refine Finset.prod_nbij' (fun a => (a : ZMod p)) (fun a => a.val) (fun a _ => Finset.mem_univ _)
    (fun a _ => Finset.mem_range.2 (ZMod.val_lt a)) (fun a ha => ?_) (fun a _ => ZMod.natCast_zmod_val a)
    (fun a _ => rfl)
  exact ZMod.val_cast_of_lt (Finset.mem_range.1 ha)

theorem C_dvd_of_map_eq_zero {F : ℤ[X]} (h : F.map (Int.castRingHom (ZMod p)) = 0) :
    C (p : ℤ) ∣ F := by
  rw [C_dvd_iff_dvd_coeff]
  intro i
  have h1 : (F.coeff i : ZMod p) = 0 := by
    have := congrArg (fun f => Polynomial.coeff f i) h
    simpa only [coeff_map, eq_intCast, coeff_zero] using this
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1 h1

theorem exists_prod_range_X_sub_C_eq :
    ∃ G : ℤ[X], ∏ a ∈ Finset.range p, (X - C ((a : ℕ) : ℤ)) = X ^ p - X + C (p : ℤ) * G := by
  have hmap : (∏ a ∈ Finset.range p, (X - C ((a : ℕ) : ℤ)) - (X ^ p - X)).map
      (Int.castRingHom (ZMod p)) = 0 := by
    rw [Polynomial.map_sub, Polynomial.map_prod, sub_eq_zero]
    have e1 : Polynomial.map (Int.castRingHom (ZMod p)) (X ^ p - X) = X ^ p - X := by simp
    rw [e1, ← prod_range_X_sub_C_zmod]
    exact Finset.prod_congr rfl fun i _ => by simp
  obtain ⟨G, hG⟩ := C_dvd_of_map_eq_zero hmap
  exact ⟨G, by rw [← hG]; ring⟩

theorem exists_prod_range_sub_eq (v : 𝒪) :
    ∃ g : 𝒪, ∏ a ∈ Finset.range p, (v - (a : 𝒪)) = v ^ p - v + (p : 𝒪) * g := by
  obtain ⟨G, hG⟩ := exists_prod_range_X_sub_C_eq (p := p)
  refine ⟨aeval v G, ?_⟩
  have h := congrArg (aeval v) hG
  simpa [map_prod] using h

theorem norm_intCast_eq_one {n : ℤ} (hn0 : n ≠ 0) (hn : n.natAbs < p) : ‖(n : ℂ_[p])‖ = 1 := by
  have h1 : ‖(n : ℚ_[p])‖ = 1 := by
    refine le_antisymm (Padic.norm_int_le_one n) (not_lt.1 fun hlt => ?_)
    have hd := Padic.norm_intCast_lt_one_iff.1 hlt
    have := Int.natAbs_dvd_natAbs.2 hd
    simp only [Int.natAbs_natCast] at this
    exact absurd (Nat.le_of_dvd (Int.natAbs_pos.2 hn0) this) (by omega)
  have h2 := PadicComplex.norm_extends' (p := p) (n : ℚ_[p])
  rw [h1, PadicComplex.coe_eq, map_intCast, map_intCast] at h2
  exact h2

theorem dvd_iff_norm_le {a b : 𝒪} (hb : b ≠ 0) : b ∣ a ↔ ‖(a : ℂ_[p])‖ ≤ ‖(b : ℂ_[p])‖ := by
  have hb' : (b : ℂ_[p]) ≠ 0 := fun h => hb (Subtype.ext h)
  constructor
  · rintro ⟨c, rfl⟩
    rw [MulMemClass.coe_mul, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (mem_normInteger.1 c.2)
  · intro h
    refine ⟨⟨(a : ℂ_[p]) / b, mem_normInteger.2 ?_⟩, Subtype.ext ?_⟩
    · rw [norm_div]
      exact div_le_one_of_le₀ h (norm_nonneg _)
    · rw [MulMemClass.coe_mul]
      field_simp

theorem natCast_p_ne_zero' : (p : 𝒪) ≠ 0 := fun h => by
  have := congrArg (fun x : 𝒪 => (x : ℂ_[p])) h
  simp only [SubringClass.coe_natCast, ZeroMemClass.coe_zero, Nat.cast_eq_zero] at this
  exact hp.out.ne_zero this

set_option maxHeartbeats 1600000 in

theorem exists_natCast_dvd_sub_of_dvd_pow_sub {v : 𝒪} (hv : (p : 𝒪) ∣ v ^ p - v) :
    ∃ a : ℕ, a < p ∧ (p : 𝒪) ∣ v - a := by
  obtain ⟨g, hg⟩ := exists_prod_range_sub_eq v
  have hprod : (p : 𝒪) ∣ ∏ a ∈ Finset.range p, (v - (a : 𝒪)) := by
    rw [hg]
    exact dvd_add hv (dvd_mul_right _ _)
  rw [dvd_iff_norm_le natCast_p_ne_zero'] at hprod
  have hnp : ‖((p : 𝒪) : ℂ_[p])‖ < 1 := by
    simpa using norm_natCast_p_lt_one (p := p)
  simp only [SubmonoidClass.coe_finsetProd, norm_prod] at hprod
  have hle : ∀ a : ℕ, ‖((v - (a : 𝒪) : 𝒪) : ℂ_[p])‖ ≤ 1 := fun a => mem_normInteger.1 (v - a).2
  by_cases hex : ∃ a ∈ Finset.range p, ‖((v - (a : 𝒪) : 𝒪) : ℂ_[p])‖ < 1
  · obtain ⟨a, ha, hlt⟩ := hex
    refine ⟨a, Finset.mem_range.1 ha, ?_⟩
    rw [dvd_iff_norm_le natCast_p_ne_zero']
    rw [Finset.prod_eq_single_of_mem a ha] at hprod
    · exact hprod
    · intro b hb hba
      have hab : ‖(((a : ℤ) - b : ℤ) : ℂ_[p])‖ = 1 := norm_intCast_eq_one (by omega)
        (by have := Finset.mem_range.1 ha; have := Finset.mem_range.1 hb; omega)
      have e : ((v - (b : 𝒪) : 𝒪) : ℂ_[p]) = ((v - (a : 𝒪) : 𝒪) : ℂ_[p]) +
          (((a : ℤ) - b : ℤ) : ℂ_[p]) := by push_cast; ring
      rw [e, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [hab]; exact hlt.ne),
        hab, max_eq_right hlt.le]
  · push Not at hex
    have h1 : ∏ a ∈ Finset.range p, ‖((v - (a : 𝒪) : 𝒪) : ℂ_[p])‖ = 1 :=
      Finset.prod_eq_one fun a ha => le_antisymm (hle a) (hex a ha)
    rw [h1] at hprod
    exact absurd hprod (not_le.2 hnp)

end Residue

section Approx

set_option maxHeartbeats 1600000 in

theorem exists_int_dvd_sub (m : ℕ) : ∀ v : 𝒪, (∃ c : ℕ → 𝒪, ∀ k : ℕ,
    (p : 𝒪) ^ m ∣ v - ∑ i ∈ Finset.range m, (p : 𝒪) ^ i * c i ^ p ^ k) →
    ∃ z : ℤ, (p : 𝒪) ^ m ∣ v - z := by
  induction m with
  | zero => intro v _; exact ⟨0, by simp⟩
  | succ m ih =>
    rintro v ⟨c, hc⟩
    have h0 : ∀ k, (p : 𝒪) ∣ v - c 0 ^ p ^ k := fun k => by
      have h := (dvd_pow_self (p : 𝒪) m.succ_ne_zero).trans (hc k)
      rw [Finset.sum_range_succ', pow_zero, one_mul] at h
      have hs : (p : 𝒪) ∣ ∑ i ∈ Finset.range m, (p : 𝒪) ^ (i + 1) * c (i + 1) ^ p ^ k :=
        Finset.dvd_sum fun i _ => Dvd.dvd.mul_right (dvd_pow_self _ i.succ_ne_zero) _
      convert dvd_add h hs using 1
      ring
    have hv1 : (p : 𝒪) ∣ v ^ p - v := by
      have e1 : (p : 𝒪) ∣ v ^ p - c 0 ^ p := by
        have h := dvd_sub_pow_of_dvd_sub (by simpa using h0 0) 1
        rw [pow_one] at h
        exact (dvd_pow_self (p : 𝒪) two_ne_zero).trans h
      have e2 := h0 1
      rw [pow_one] at e2
      convert dvd_sub e1 e2 using 1
      ring
    obtain ⟨a, hap, ha⟩ := exists_natCast_dvd_sub_of_dvd_pow_sub hv1
    have hca : (p : 𝒪) ∣ c 0 - a := by
      have h := h0 0
      rw [pow_zero, pow_one] at h
      convert dvd_sub ha h using 1
      ring
    have hfa : (p : 𝒪) ∣ (a : 𝒪) ^ p - a := by
      have hz : (p : ℤ) ∣ (a : ℤ) ^ p - a := by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        push_cast
        rw [ZMod.pow_card, sub_self]
      have := map_dvd (Int.castRingHom 𝒪) hz
      simpa using this
    have hak : ∀ j, (p : 𝒪) ^ (m + 1) ∣ (a : 𝒪) ^ p ^ (m + j) - (a : 𝒪) ^ p ^ m := by
      intro j
      induction j with
      | zero => simp
      | succ j ihj =>
        have h1 := dvd_sub_pow_of_dvd_sub hfa (m + j)
        have e : ((a : 𝒪) ^ p) ^ p ^ (m + j) = (a : 𝒪) ^ p ^ (m + (j + 1)) := by
          rw [← pow_mul, ← pow_succ']
          rfl
        rw [e] at h1
        have h2 := (pow_dvd_pow (p : 𝒪) (by omega : m + 1 ≤ m + j + 1)).trans h1
        convert dvd_add h2 ihj using 1
        ring
    have hk : ∀ j, (p : 𝒪) ^ (m + 1) ∣ (v - (a : 𝒪) ^ p ^ m) -
        (p : 𝒪) * ∑ i ∈ Finset.range m, (p : 𝒪) ^ i * c (i + 1) ^ p ^ (m + j) := by
      intro j
      have h1 := hc (m + j)
      rw [Finset.sum_range_succ', pow_zero, one_mul] at h1
      have h2 : (p : 𝒪) ^ (m + 1) ∣ c 0 ^ p ^ (m + j) - (a : 𝒪) ^ p ^ (m + j) :=
        (pow_dvd_pow _ (by omega)).trans (dvd_sub_pow_of_dvd_sub hca (m + j))
      convert dvd_add (dvd_add h1 h2) (hak j) using 1
      simp only [Finset.mul_sum, ← mul_assoc, ← pow_succ']
      ring
    have hpz : (p : 𝒪) ∣ v - (a : 𝒪) ^ p ^ m := by
      have h := dvd_add ((dvd_pow_self (p : 𝒪) m.succ_ne_zero).trans (hk 0))
        (dvd_mul_right (p : 𝒪) (∑ i ∈ Finset.range m, (p : 𝒪) ^ i * c (i + 1) ^ p ^ (m + 0)))
      rwa [sub_add_cancel] at h
    obtain ⟨v', hv'⟩ := hpz
    have hv'c : ∀ k, (p : 𝒪) ^ m ∣
        v' - ∑ i ∈ Finset.range m, (p : 𝒪) ^ i * (c (i + 1) ^ p ^ m) ^ p ^ k := by
      intro k
      have h := hk k
      rw [hv', ← mul_sub, pow_succ'] at h
      have h' := (mul_dvd_mul_iff_left natCast_p_ne_zero').1 h
      have e : ∀ i, c (i + 1) ^ p ^ (m + k) = (c (i + 1) ^ p ^ m) ^ p ^ k := fun i => by
        rw [pow_add, pow_mul]
      simp only [e] at h'
      exact h'
    obtain ⟨z', hz'⟩ := ih v' ⟨fun i => c (i + 1) ^ p ^ m, hv'c⟩
    refine ⟨(a : ℤ) ^ p ^ m + p * z', ?_⟩
    have e : v - (((a : ℤ) ^ p ^ m + p * z' : ℤ) : 𝒪) = (p : 𝒪) * (v' - z') := by
      push_cast
      linear_combination hv'
    rw [e, pow_succ']
    exact mul_dvd_mul_left _ hz'

theorem norm_algebraMap_padic (q : ℚ_[p]) : ‖algebraMap ℚ_[p] ℂ_[p] q‖ = ‖q‖ := by
  rw [IsScalarTower.algebraMap_apply ℚ_[p] (PadicAlgCl p) ℂ_[p], ← PadicComplex.coe_eq]
  exact PadicComplex.norm_extends' p q

theorem isClosed_range_algebraMap_padic : IsClosed (Set.range (algebraMap ℚ_[p] ℂ_[p])) :=
  (AddMonoidHomClass.isometry_of_norm _ norm_algebraMap_padic).isUniformInducing.isComplete_range.isClosed

set_option maxHeartbeats 1600000 in

theorem theta_mem_range_of_phi_eq {y : ACris ℂ_[p] p} (hy : phi ℂ_[p] p y = y) :
    ∃ q : ℚ_[p], ((theta ℂ_[p] p y : 𝒪) : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] q := by
  have happrox : ∀ m : ℕ, ∃ z : ℤ,
      ‖((theta ℂ_[p] p y : 𝒪) : ℂ_[p]) - (z : ℂ_[p])‖ ≤ ‖(p : ℂ_[p])‖ ^ m := by
    intro m
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · exact ⟨0, by simpa using mem_normInteger.1 (theta ℂ_[p] p y).2⟩
    obtain ⟨c, hc⟩ := exists_theta_eq_sum_of_phi_iterate (N := 1) le_rfl
      (by rw [Function.iterate_one]; exact hy) hm
    obtain ⟨z, hz⟩ := exists_int_dvd_sub m (theta ℂ_[p] p y) ⟨c, fun k => by
      obtain ⟨e, he⟩ := hc k
      refine ⟨e, Subtype.ext ?_⟩
      simp only [one_mul] at he
      push_cast
      rw [he]
      ring⟩
    refine ⟨z, ?_⟩
    have h := (dvd_iff_norm_le (pow_ne_zero m natCast_p_ne_zero')).1 hz
    simpa using h
  have hmem : ((theta ℂ_[p] p y : 𝒪) : ℂ_[p]) ∈ closure (Set.range (algebraMap ℚ_[p] ℂ_[p])) := by
    rw [Metric.mem_closure_iff]
    intro δ hδ
    obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hδ (norm_natCast_p_lt_one (p := p))
    obtain ⟨z, hz⟩ := happrox m
    refine ⟨algebraMap ℚ_[p] ℂ_[p] z, ⟨z, rfl⟩, ?_⟩
    rw [dist_eq_norm, map_intCast]
    exact hz.trans_lt hm
  rw [isClosed_range_algebraMap_padic.closure_eq] at hmem
  obtain ⟨q, hq⟩ := hmem
  exact ⟨q, hq.symm⟩

end Approx

section Plus

theorem mem_pow_of_p_pow_mul_phi_eq {a : ACris ℂ_[p] p} {m : ℕ} (hm : 1 ≤ m)
    (ha : (p : ACris ℂ_[p] p) ^ m * phi ℂ_[p] p a = a) (j : ℕ) : a ∈ 𝔭 ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at ih ⊢
    obtain ⟨b, hb⟩ := ih
    refine ⟨(p : ACris ℂ_[p] p) ^ (m - 1) * phi ℂ_[p] p b, ?_⟩
    conv_rhs => rw [← ha, ← hb]
    rw [map_mul, map_pow, map_natCast]
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring

set_option maxHeartbeats 1600000 in

theorem eq_zero_of_p_pow_mul_phiPlus_eq {y : BCrisPlus ℂ_[p] p} {m : ℕ} (hm : 1 ≤ m)
    (hy : (p : BCrisPlus ℂ_[p] p) ^ m * phiPlus ℂ_[p] p y = y) : y = 0 := by
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers (p : ACris ℂ_[p] p)) y
  obtain ⟨k, hk⟩ := s.2
  simp only at hs
  rw [← hk, map_pow, map_natCast] at hs
  have h1 := congrArg (phiPlus ℂ_[p] p) hs
  rw [map_mul, map_pow, map_natCast, phiPlus_algebraMap] at h1
  have ha : (p : ACris ℂ_[p] p) ^ m * phi ℂ_[p] p a = a := by
    apply algebraMap_aCris_injective
    rw [map_mul, map_pow, map_natCast, ← h1, ← hs]
    conv_rhs => rw [← hy]
    ring
  have ha0 : a = 0 := IsHausdorff.haus' (I := 𝔭) a fun j => by
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
    exact mem_pow_of_p_pow_mul_phi_eq hm ha j
  rw [ha0, map_zero] at hs
  exact (isUnit_p_bCrisPlus.pow k).mul_left_eq_zero.1 hs

variable {ε : PreTilt (normInteger ℂ_[p]) p} (hε : PreTilt.untilt ε = 1)
  (hζ : PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt (normInteger ℂ_[p]) p) p).symm ε) ≠ 1)

include hζ in
theorem iotaPlus_periodTPlus_ne_zero : iotaPlus ℂ_[p] p (periodTPlus hε) ≠ 0 := by
  rw [iotaPlus_periodTPlus]
  exact fontaineT_ne_zero hε hζ

include hζ in

theorem periodTPlus_mul_left_cancel {a b : BCrisPlus ℂ_[p] p}
    (h : periodTPlus hε * a = periodTPlus hε * b) : a = b :=
  iotaPlus_injective (K := ℂ_[p]) (p := p) (mul_left_cancel₀ (iotaPlus_periodTPlus_ne_zero hε hζ)
    (by rw [← map_mul, ← map_mul, h]))

set_option maxHeartbeats 1600000 in
theorem iterate_phiPlus_eq_pow_mul {y : BCrisPlus ℂ_[p] p} {n : ℕ}
    (hy : phiPlus ℂ_[p] p y = (p : BCrisPlus ℂ_[p] p) ^ n * y) (k : ℕ) :
    (phiPlus ℂ_[p] p)^[k] y = ((p : BCrisPlus ℂ_[p] p) ^ n) ^ k * y := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, map_mul, map_pow, map_pow, map_natCast, hy]
    ring

include hε hζ in
set_option maxHeartbeats 1600000 in

theorem exists_eq_algebraMap_of_phiPlus_eq {y : BCrisPlus ℂ_[p] p}
    (hy : phiPlus ℂ_[p] p y = y) : ∃ q : ℚ_[p], y = algebraMap ℚ_[p] (BCrisPlus ℂ_[p] p) q := by
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers (p : ACris ℂ_[p] p)) y
  obtain ⟨k, hk⟩ := s.2
  simp only at hs
  rw [← hk, map_pow, map_natCast] at hs
  have hφa : phi ℂ_[p] p a = a := by
    apply algebraMap_aCris_injective
    have h1 := congrArg (phiPlus ℂ_[p] p) hs
    rw [map_mul, map_pow, map_natCast, phiPlus_algebraMap, hy, hs] at h1
    exact h1.symm
  obtain ⟨q0, hq0⟩ := theta_mem_range_of_phi_eq hφa
  refine ⟨q0 / (p : ℚ_[p]) ^ k, ?_⟩
  set y' := y - algebraMap ℚ_[p] (BCrisPlus ℂ_[p] p) (q0 / (p : ℚ_[p]) ^ k) with hy'_def
  have hy' : phiPlus ℂ_[p] p y' = y' := by rw [hy'_def, map_sub, hy, phiPlus_algebraMap_padic]
  have hθ : θdR (iotaPlus ℂ_[p] p y') = 0 := by
    have h1 := congrArg (fun z => θdR (iotaPlus ℂ_[p] p z)) hs
    simp only [map_mul, map_pow, map_natCast, thetaField_iotaPlus_algebraMap, hq0] at h1
    rw [hy'_def, map_sub, map_sub, iotaPlus_algebraMap_padic, thetaBDeRhamPlusField_algebraMap,
      sub_eq_zero]
    have hp0 : (p : ℂ_[p]) ^ k ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hp.out.ne_zero)
    apply mul_right_cancel₀ hp0
    rw [h1, map_div₀, map_pow, map_natCast, div_mul_cancel₀ _ hp0]
  have hall : ∀ n, θdR (iotaPlus ℂ_[p] p ((phiPlus ℂ_[p] p)^[n] y')) = 0 := fun n => by
    rw [Function.iterate_fixed hy' n, hθ]
  have hmem := phiPlus_mem_span_periodT hε hζ hall
  rw [hy'] at hmem
  obtain ⟨y'', hy''⟩ := Ideal.mem_span_singleton'.1 hmem
  have h2 : (p : BCrisPlus ℂ_[p] p) ^ 1 * phiPlus ℂ_[p] p y'' = y'' := by
    apply periodTPlus_mul_left_cancel hε hζ
    have h3 := congrArg (phiPlus ℂ_[p] p) hy''
    rw [map_mul, phiPlus_periodTPlus, hy', ← hy''] at h3
    rw [pow_one]
    linear_combination h3
  have h4 := eq_zero_of_p_pow_mul_phiPlus_eq le_rfl h2
  rw [h4, zero_mul] at hy''
  rw [← sub_eq_zero, ← hy'_def, ← hy'']

include hζ in
set_option maxHeartbeats 1600000 in

theorem exists_eq_algebraMap_mul_pow_of_phiPlus_eq (n : ℕ) : ∀ {y : BCrisPlus ℂ_[p] p},
    phiPlus ℂ_[p] p y = (p : BCrisPlus ℂ_[p] p) ^ n * y →
    iotaPlus ℂ_[p] p y ∈ Ideal.span {fontaineT ε hε ^ n} →
    ∃ q : ℚ_[p], y = algebraMap ℚ_[p] (BCrisPlus ℂ_[p] p) q * periodTPlus hε ^ n := by
  induction n with
  | zero =>
    intro y hy _
    obtain ⟨q, hq⟩ := exists_eq_algebraMap_of_phiPlus_eq hε hζ (by rw [hy, pow_zero, one_mul])
    exact ⟨q, by rw [hq, pow_zero, mul_one]⟩
  | succ n ih =>
    intro y hy hι
    have hθ0 : θdR (iotaPlus ℂ_[p] p y) = 0 := by
      have hT : fontaineT ε hε ^ (n + 1) ∈ RingHom.ker θdR := by
        rw [← IsPerfectoidField.maximalIdeal_bDeRhamPlus, maximalIdeal_eq_span_fontaineT hε hζ]
        exact Ideal.pow_mem_of_mem _ (Ideal.mem_span_singleton_self _) _ n.succ_pos
      obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.1 hι
      rw [← hd, map_mul, RingHom.mem_ker.1 hT, mul_zero]
    have hall : ∀ k, θdR (iotaPlus ℂ_[p] p ((phiPlus ℂ_[p] p)^[k] y)) = 0 := fun k => by
      rw [iterate_phiPlus_eq_pow_mul hy k, map_mul, map_mul, hθ0, mul_zero]
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 (phiPlus_mem_span_periodT hε hζ hall)
    set y1 := Ring.inverse (p : BCrisPlus ℂ_[p] p) ^ (n + 1) * w with hy1_def
    have hinv : Ring.inverse (p : BCrisPlus ℂ_[p] p) ^ (n + 1) * (p : BCrisPlus ℂ_[p] p) ^ (n + 1) =
        1 := by
      rw [← mul_pow, Ring.inverse_mul_cancel _ isUnit_p_bCrisPlus, one_pow]
    have hyt : y = periodTPlus hε * y1 := by
      calc y = Ring.inverse (p : BCrisPlus ℂ_[p] p) ^ (n + 1) * ((p : BCrisPlus ℂ_[p] p) ^ (n + 1) * y) := by
            rw [← mul_assoc, hinv, one_mul]
        _ = Ring.inverse (p : BCrisPlus ℂ_[p] p) ^ (n + 1) * (w * periodTPlus hε) := by rw [← hy, hw]
        _ = periodTPlus hε * y1 := by rw [hy1_def]; ring
    have hy1 : phiPlus ℂ_[p] p y1 = (p : BCrisPlus ℂ_[p] p) ^ n * y1 := by
      apply isUnit_p_bCrisPlus.mul_left_cancel
      apply periodTPlus_mul_left_cancel hε hζ
      have h3 := congrArg (phiPlus ℂ_[p] p) hyt
      rw [map_mul, phiPlus_periodTPlus, hy] at h3
      rw [hyt] at h3
      linear_combination -h3
    have hι1 : iotaPlus ℂ_[p] p y1 ∈ Ideal.span {fontaineT ε hε ^ n} := by
      obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.1 hι
      rw [hyt, map_mul, iotaPlus_periodTPlus] at hd
      rw [Ideal.mem_span_singleton']
      refine ⟨d, mul_left_cancel₀ (fontaineT_ne_zero hε hζ) ?_⟩
      rw [← hd]
      ring
    obtain ⟨q, hq⟩ := ih hy1 hι1
    exact ⟨q, by rw [hyt, hq]; ring⟩

end Plus

end ACris

end GroundTheory.PAdicHodge
