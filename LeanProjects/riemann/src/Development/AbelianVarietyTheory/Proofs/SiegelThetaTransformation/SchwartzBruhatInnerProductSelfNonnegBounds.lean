import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IMemSiegel
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FinsumQuotientOfLe
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real

namespace GlobalTheory.SW.IpPos

open NumberField

variable {K κ ι : Type} [Field K] [NumberField K] [Fintype κ] [Fintype ι]

open Matrix Complex in
open scoped ComplexConjugate Real in
open NumberField in
variable {K κ ι : Type} [Field K] [NumberField K] [Fintype κ] [Fintype ι] in
omit [NumberField K] [Fintype κ] [Fintype ι] in
theorem _root_.GlobalTheory.SW.IpPos.exists_of_mem_perSub {R : ℕ} {x : Matrix κ ι K}
    (hx : x ∈ _root_.GlobalTheory.SW.perSub K κ ι R) :
    ∃ y : Matrix κ ι K, _root_.GlobalTheory.SW.IntM y ∧ x = (R : K) • y := by
  obtain ⟨y, rfl⟩ := (_root_.GlobalTheory.SW.HaarLevel.mem_perSub R x).mp hx
  exact ⟨_root_.GlobalTheory.SW.HaarLevel.incl K κ ι y,
    (_root_.GlobalTheory.SW.HaarLevel.intM_iff _).mpr ⟨y, rfl⟩,
    (Nat.cast_smul_eq_nsmul K R _).symm⟩

open Matrix Complex in
open scoped ComplexConjugate Real in
open NumberField in
variable {K κ ι : Type} [Field K] [NumberField K] [Fintype κ] [Fintype ι] in
omit [NumberField K] [Fintype κ] [Fintype ι] in
theorem _root_.GlobalTheory.SW.IpPos.apply_out_mk {R : ℕ} {φ : Matrix κ ι K → ℂ}
    (h : _root_.GlobalTheory.SW.HasLevel R φ) (x : Matrix κ ι K) :
    φ (QuotientAddGroup.mk (s := _root_.GlobalTheory.SW.perSub K κ ι R) x).out = φ x := by
  have hmem := QuotientAddGroup.eq.mp
    (QuotientAddGroup.out_eq' (QuotientAddGroup.mk (s := _root_.GlobalTheory.SW.perSub K κ ι R) x)).symm
  rw [← _root_.GlobalTheory.SW.HaarLevel.periodic h x _ hmem, add_neg_cancel_left]

open Matrix Complex in
open scoped ComplexConjugate Real in
open NumberField in
variable {K κ ι : Type} [Field K] [NumberField K] [Fintype κ] [Fintype ι] in
omit [NumberField K] [Fintype κ] [Fintype ι] in
theorem _root_.GlobalTheory.SW.IpPos.intM_natCast_smul (n : ℕ) {x : Matrix κ ι K}
    (hx : _root_.GlobalTheory.SW.IntM x) : _root_.GlobalTheory.SW.IntM ((n : K) • x) := by
  intro k i
  rw [Matrix.smul_apply, smul_eq_mul]
  exact (isIntegral_natCast n).mul (hx k i)

open Matrix Complex in
open scoped ComplexConjugate Real in
open NumberField in
variable {K κ ι : Type} [Field K] [NumberField K] [Fintype κ] [Fintype ι] in
omit [NumberField K] [Fintype κ] [Fintype ι] in
theorem _root_.GlobalTheory.SW.IpPos.hasLevel_mul {R : ℕ} {φ : Matrix κ ι K → ℂ} (h : _root_.GlobalTheory.SW.HasLevel R φ)
    (S : ℕ) : _root_.GlobalTheory.SW.HasLevel (R * S) φ := by
  refine ⟨fun x hx => ?_, fun x y hy => ?_⟩
  · rw [Nat.cast_mul, mul_comm, mul_smul]
    exact _root_.GlobalTheory.SW.IpPos.intM_natCast_smul S (h.1 x hx)
  · rw [Nat.cast_mul, mul_smul]
    exact h.2 x _ (_root_.GlobalTheory.SW.IpPos.intM_natCast_smul S hy)

def classes (K κ ι : Type) [Field K] (R : ℕ) : Set (Matrix κ ι K ⧸ perSub K κ ι R) :=
  {q | IntM ((R : K) • q.out)}

open Matrix Complex in
open scoped ComplexConjugate Real in
open NumberField in
variable {K κ ι : Type} [Field K] [NumberField K] [Fintype κ] [Fintype ι] in
theorem _root_.GlobalTheory.SW.IpPos.classes_finite_card {R : ℕ} (hR : 0 < R) :
    (_root_.GlobalTheory.SW.IpPos.classes K κ ι R).Finite ∧
      (_root_.GlobalTheory.SW.IpPos.classes K κ ι R).ncard ≤
      (R ^ (Module.finrank ℚ K * (Fintype.card κ * Fintype.card ι))) ^ 2 := by
  set L := _root_.GlobalTheory.SW.perSub K κ ι 1
  set H := (_root_.GlobalTheory.SW.perSub K κ ι (1 * (R * R))).addSubgroupOf L
  have hRK : (R : K) ≠ 0 := Nat.cast_ne_zero.mpr hR.ne'
  have hidx : H.index = (R ^ (Module.finrank ℚ K * (Fintype.card κ * Fintype.card ι))) ^ 2 := by
    show (_root_.GlobalTheory.SW.perSub K κ ι (1 * (R * R))).relIndex L = _
    rw [_root_.GlobalTheory.SW.HaarLevel.relIndex_perSub 1 (R * R) one_pos, mul_pow, ← sq]
  let g : L →+ Matrix κ ι K ⧸ _root_.GlobalTheory.SW.perSub K κ ι R :=
    (QuotientAddGroup.mk' _).comp
      ((DistribMulAction.toAddMonoidHom (Matrix κ ι K) ((R : K)⁻¹)).comp L.subtype)
  have hker : H ≤ g.ker := by
    intro z hz
    rw [AddMonoidHom.mem_ker]
    obtain ⟨y, hy, hzy⟩ :=
      _root_.GlobalTheory.SW.IpPos.exists_of_mem_perSub (AddSubgroup.mem_addSubgroupOf.mp hz)
    simp only [g, AddMonoidHom.comp_apply, AddSubgroup.coe_subtype,
      DistribMulAction.toAddMonoidHom_apply, QuotientAddGroup.mk'_apply,
      QuotientAddGroup.eq_zero_iff, hzy, smul_smul]
    rw [show ((R : K))⁻¹ * ((1 * (R * R) : ℕ) : K) = R by push_cast; field_simp]
    exact AddSubgroup.subset_closure ⟨y, hy, rfl⟩
  let F := QuotientAddGroup.lift H g hker
  have hsub : _root_.GlobalTheory.SW.IpPos.classes K κ ι R ⊆ Set.range F := by
    intro q hq
    have hL : (R : K) • q.out ∈ L :=
      AddSubgroup.subset_closure ⟨_, hq, by rw [Nat.cast_one, one_smul]⟩
    refine ⟨QuotientAddGroup.mk ⟨_, hL⟩, ?_⟩
    simp only [F, QuotientAddGroup.lift_mk, g, AddMonoidHom.comp_apply, AddSubgroup.coe_subtype,
      DistribMulAction.toAddMonoidHom_apply, QuotientAddGroup.mk'_apply, smul_smul,
      inv_mul_cancel₀ hRK, one_smul]
    exact QuotientAddGroup.out_eq' q
  have hfin : Finite (L ⧸ H) := Nat.finite_of_card_ne_zero (by
    rw [← AddSubgroup.index, hidx]; positivity)
  refine ⟨(Set.finite_range F).subset hsub, ?_⟩
  calc (_root_.GlobalTheory.SW.IpPos.classes K κ ι R).ncard ≤ (Set.range F).ncard :=
        Set.ncard_le_ncard hsub (Set.finite_range F)
    _ = Nat.card (Set.range F) := (Nat.card_coe_set_eq _).symm
    _ ≤ Nat.card (L ⧸ H) := Nat.card_le_card_of_surjective _ Set.rangeFactorization_surjective
    _ = _ := hidx

open Matrix Complex in
open scoped ComplexConjugate Real in
open NumberField in
variable {K κ ι : Type} [Field K] [NumberField K] [Fintype κ] [Fintype ι] in
theorem _root_.GlobalTheory.SW.IpPos.ip_eq_sum {R : ℕ} (hR : 0 < R) {φ ψ : Matrix κ ι K → ℂ}
    (hφ : _root_.GlobalTheory.SW.HasLevel R φ) (hψ : _root_.GlobalTheory.SW.HasLevel R ψ) :
    _root_.GlobalTheory.SW.ip φ ψ =
      ((R : ℂ) ^ (Module.finrank ℚ K * (Fintype.card κ * Fintype.card ι)))⁻¹ *
      ∑ q ∈ (_root_.GlobalTheory.SW.IpPos.classes_finite_card (K := K) (κ := κ) (ι := ι) hR).1.toFinset,
        φ q.out * conj (ψ q.out) := by
  have hlev : _root_.GlobalTheory.SW.HasLevel R (fun x => φ x * conj (ψ x)) := by
    refine ⟨fun x hx => hφ.1 x (left_ne_zero_of_mul hx), fun x y hy => ?_⟩
    simp only [hφ.2 x y hy, hψ.2 x y hy]
  unfold _root_.GlobalTheory.SW.ip
  rw [(_root_.GlobalTheory.SW.haar_eq_haarAt K κ ι R _ hR hlev).1]
  unfold _root_.GlobalTheory.SW.haarAt
  congr 1
  refine finsum_eq_sum_of_support_subset _ ?_
  intro q hq
  rw [Set.Finite.coe_toFinset]
  exact hφ.1 _ (left_ne_zero_of_mul hq)

end GlobalTheory.SW.IpPos

open Matrix Complex in
open scoped ComplexConjugate Real in
open NumberField in
variable {K κ ι : Type} [Field K] [NumberField K] [Fintype κ] [Fintype ι] in
private lemma schwartzBruhatInnerProduct_self_eq_lemma {R : ℕ} (hR : 0 < R) {φ : Matrix κ ι K → ℂ}
    (hφ : _root_.GlobalTheory.SW.HasLevel R φ) :
    _root_.GlobalTheory.SW.ip φ φ =
      (((R : ℝ) ^ (Module.finrank ℚ K * (Fintype.card κ * Fintype.card ι)))⁻¹ *
      ∑ q ∈ (_root_.GlobalTheory.SW.IpPos.classes_finite_card (K := K) (κ := κ) (ι := ι) hR).1.toFinset,
        ‖φ q.out‖ ^ 2 : ℝ) := by
  rw [_root_.GlobalTheory.SW.IpPos.ip_eq_sum hR hφ hφ]
  simp_rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  rfl

open Matrix Complex in
open scoped ComplexConjugate Real in

theorem _root_.GlobalTheory.SW.ip_self_nonneg_and_bounds : ∀ (K κ ι : Type) [Field K] [NumberField K]
    [Fintype κ] [Fintype ι] (R : ℕ) (φ : Matrix κ ι K → ℂ), 0 < R → _root_.GlobalTheory.SW.HasLevel R φ →
    (_root_.GlobalTheory.SW.ip φ φ).im = 0 ∧ 0 ≤ (_root_.GlobalTheory.SW.ip φ φ).re ∧
    (∀ x, ‖φ x‖ ^ 2 ≤ (R : ℝ) ^ (Module.finrank ℚ K * (Fintype.card κ * Fintype.card ι)) *
      (_root_.GlobalTheory.SW.ip φ φ).re) ∧
    (∀ B : ℝ, (∀ x, ‖φ x‖ ≤ B) → (_root_.GlobalTheory.SW.ip φ φ).re ≤
      (R : ℝ) ^ (Module.finrank ℚ K * (Fintype.card κ * Fintype.card ι)) * B ^ 2) ∧
    (∃ B : ℝ, ∀ x, ‖φ x‖ ≤ B) ∧ ∀ ψ, _root_.GlobalTheory.SW.IsSB ψ →
      ‖_root_.GlobalTheory.SW.ip φ ψ‖ ^ 2 ≤
        (_root_.GlobalTheory.SW.ip φ φ).re * (_root_.GlobalTheory.SW.ip ψ ψ).re := by
  intro K κ ι _ _ _ _ R φ hR hφ
  set N := Module.finrank ℚ K * (Fintype.card κ * Fintype.card ι)
  have hfc := _root_.GlobalTheory.SW.IpPos.classes_finite_card (K := K) (κ := κ) (ι := ι) hR
  set s := hfc.1.toFinset with hs
  set Sφ := ∑ q ∈ s, ‖φ q.out‖ ^ 2 with hSφ
  have hc : (0 : ℝ) < (R : ℝ) ^ N := by positivity
  have hip : _root_.GlobalTheory.SW.ip φ φ = (((R : ℝ) ^ N)⁻¹ * Sφ : ℝ) :=
    schwartzBruhatInnerProduct_self_eq_lemma hR hφ
  have hre : (_root_.GlobalTheory.SW.ip φ φ).re = ((R : ℝ) ^ N)⁻¹ * Sφ := by
    rw [hip, Complex.ofReal_re]
  have hS0 : 0 ≤ Sφ := Finset.sum_nonneg fun _ _ => by positivity
  have hpt : ∀ x, ‖φ x‖ ^ 2 ≤ (R : ℝ) ^ N * (_root_.GlobalTheory.SW.ip φ φ).re := by
    intro x
    rw [hre, ← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]
    by_cases hx : φ x = 0
    · simpa [hx] using hS0
    · have hq : (QuotientAddGroup.mk x : Matrix κ ι K ⧸ _root_.GlobalTheory.SW.perSub K κ ι R) ∈ s := by
        rw [hs, Set.Finite.mem_toFinset]
        show _root_.GlobalTheory.SW.IntM _
        exact hφ.1 _ (by rwa [_root_.GlobalTheory.SW.IpPos.apply_out_mk hφ])
      have h := Finset.single_le_sum (f := fun q => ‖φ q.out‖ ^ 2) (fun _ _ => by positivity) hq
      simpa only [_root_.GlobalTheory.SW.IpPos.apply_out_mk hφ] using h
  refine ⟨by rw [hip, Complex.ofReal_im], by rw [hre]; positivity, hpt, fun B hB => ?_,
    ⟨√((R : ℝ) ^ N * (_root_.GlobalTheory.SW.ip φ φ).re), fun x => by
      simpa using Real.abs_le_sqrt (hpt x)⟩, fun ψ hψ => ?_⟩
  · have h1 : Sφ ≤ s.card • B ^ 2 :=
      Finset.sum_le_card_nsmul _ _ _ (fun q _ => pow_le_pow_left₀ (norm_nonneg _) (hB _) 2)
    have hcard : (s.card : ℝ) ≤ ((R : ℝ) ^ N) ^ 2 := by
      rw [hs, ← Set.ncard_eq_toFinset_card _ hfc.1]
      exact_mod_cast hfc.2
    rw [nsmul_eq_mul] at h1
    rw [hre]
    calc ((R : ℝ) ^ N)⁻¹ * Sφ ≤ ((R : ℝ) ^ N)⁻¹ * (((R : ℝ) ^ N) ^ 2 * B ^ 2) := by
          gcongr
          exact h1.trans (mul_le_mul_of_nonneg_right hcard (sq_nonneg B))
      _ = (R : ℝ) ^ N * B ^ 2 := by field_simp
  · obtain ⟨S, hS, hψS⟩ := hψ
    have hRS : 0 < R * S := Nat.mul_pos hR hS
    have hφ' := _root_.GlobalTheory.SW.IpPos.hasLevel_mul hφ S
    have hψ' : _root_.GlobalTheory.SW.HasLevel (R * S) ψ := by
      rw [mul_comm]; exact _root_.GlobalTheory.SW.IpPos.hasLevel_mul hψS R
    rw [_root_.GlobalTheory.SW.IpPos.ip_eq_sum hRS hφ' hψ',
      schwartzBruhatInnerProduct_self_eq_lemma hRS hφ', schwartzBruhatInnerProduct_self_eq_lemma hRS hψ',
      Complex.ofReal_re, Complex.ofReal_re, norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
    set t := (_root_.GlobalTheory.SW.IpPos.classes_finite_card (K := K) (κ := κ) (ι := ι) hRS).1.toFinset
    set d : ℝ := ((R * S : ℕ) : ℝ) ^ N
    have hcs : ‖∑ q ∈ t, φ q.out * conj (ψ q.out)‖ ^ 2 ≤
        (∑ q ∈ t, ‖φ q.out‖ ^ 2) * ∑ q ∈ t, ‖ψ q.out‖ ^ 2 := by
      calc _ ≤ (∑ q ∈ t, ‖φ q.out‖ * ‖ψ q.out‖) ^ 2 := by
            gcongr
            refine (norm_sum_le _ _).trans (le_of_eq ?_)
            simp [Complex.norm_conj]
        _ ≤ _ := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    calc (d⁻¹ * ‖∑ q ∈ t, φ q.out * conj (ψ q.out)‖) ^ 2
        = d⁻¹ * d⁻¹ * ‖∑ q ∈ t, φ q.out * conj (ψ q.out)‖ ^ 2 := by ring
      _ ≤ d⁻¹ * d⁻¹ * ((∑ q ∈ t, ‖φ q.out‖ ^ 2) * ∑ q ∈ t, ‖ψ q.out‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hcs (by positivity)
      _ = _ := by ring
