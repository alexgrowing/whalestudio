import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyRayDataOfNeZero
import Development.AbelianVarietyTheory.Definitions.Foundations.RayPrimes
import Development.AbelianVarietyTheory.Definitions.Foundations.NormOneSevenOneTwo

noncomputable section

open NumberField IsDedekindDomain
open scoped nonZeroDivisors

namespace GlobalTheory.Mem.RayData

section aux

variable {K : Type} [Field K] [NumberField K]

def idealUnit (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) : (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  Units.mk0 (I : FractionalIdeal (𝓞 K)⁰ K) (FractionalIdeal.coeIdeal_ne_zero.2 hI)

theorem coe_idealUnit (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    (idealUnit I hI : FractionalIdeal (𝓞 K)⁰ K) = (I : FractionalIdeal (𝓞 K)⁰ K) := rfl

open NumberField IsDedekindDomain in
open scoped nonZeroDivisors in
variable {K : Type} [Field K] [NumberField K] in
private lemma coe_idealUnit_eq (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    ((_root_.GlobalTheory.Mem.RayData.idealUnit I hI : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) = I := rfl

open NumberField IsDedekindDomain in
open scoped nonZeroDivisors in
variable {K : Type} [Field K] [NumberField K] in
theorem _root_.GlobalTheory.Mem.RayData.idealUnit_mul (I J : Ideal (𝓞 K)) (hI : I ≠ ⊥) (hJ : J ≠ ⊥) (h : I * J ≠ ⊥) :
    _root_.GlobalTheory.Mem.RayData.idealUnit (I * J) h = _root_.GlobalTheory.Mem.RayData.idealUnit I hI * _root_.GlobalTheory.Mem.RayData.idealUnit J hJ := by
  ext
  simp [coe_idealUnit_eq, FractionalIdeal.coeIdeal_mul]

open NumberField IsDedekindDomain in
open scoped nonZeroDivisors in
variable {K : Type} [Field K] [NumberField K] in
theorem _root_.GlobalTheory.Mem.RayData.idealUnit_congr {I J : Ideal (𝓞 K)} (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
    _root_.GlobalTheory.Mem.RayData.idealUnit I hI = _root_.GlobalTheory.Mem.RayData.idealUnit J hJ ↔ I = J := by
  rw [Units.ext_iff, coe_idealUnit_eq, coe_idealUnit_eq, FractionalIdeal.coeIdeal_inj]

open NumberField IsDedekindDomain in
open scoped nonZeroDivisors in
variable {K : Type} [Field K] [NumberField K] in
theorem _root_.GlobalTheory.Mem.RayData.span_ne_bot {a : 𝓞 K} (ha : a ≠ 0) : Ideal.span {a} ≠ ⊥ := by
  rwa [Ne, Ideal.span_singleton_eq_bot]

open NumberField IsDedekindDomain in
open scoped nonZeroDivisors in
variable {K : Type} [Field K] [NumberField K] in
private lemma idealUnit_span_mem_rayP_of_sub_one_mem {𝔮 : Ideal (𝓞 K)} {a : 𝓞 K} (ha : a ≠ 0)
    (h : a - 1 ∈ 𝔮) : _root_.GlobalTheory.Mem.RayData.idealUnit _ (_root_.GlobalTheory.Mem.RayData.span_ne_bot ha) ∈ _root_.GlobalTheory.Mem.An.rayP 𝔮 := by
  unfold _root_.GlobalTheory.Mem.An.rayP
  exact Subgroup.subset_closure ⟨a, h, rfl⟩

open NumberField IsDedekindDomain in
open scoped nonZeroDivisors in
variable {K : Type} [Field K] [NumberField K] in

theorem _root_.GlobalTheory.Mem.RayData.mem_principalRay_iff (𝔮 : Ideal (𝓞 K)) (x : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    x ∈ _root_.GlobalTheory.Mem.An.rayP 𝔮 ↔ ∃ (a b : 𝓞 K) (ha : a ≠ 0) (hb : b ≠ 0), a - 1 ∈ 𝔮 ∧ b - 1 ∈ 𝔮 ∧
      x * _root_.GlobalTheory.Mem.RayData.idealUnit _ (_root_.GlobalTheory.Mem.RayData.span_ne_bot hb) = _root_.GlobalTheory.Mem.RayData.idealUnit _ (_root_.GlobalTheory.Mem.RayData.span_ne_bot ha) := by
  constructor
  · intro hx
    unfold _root_.GlobalTheory.Mem.An.rayP at hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha1, hya⟩ := hy
      have ha : a ≠ 0 := by
        rintro rfl
        exact y.ne_zero (by rw [hya]; simp)
      refine ⟨a, 1, ha, one_ne_zero, ha1, by simp, ?_⟩
      ext
      simp [coe_idealUnit_eq, hya]
    | one =>
      exact ⟨1, 1, one_ne_zero, one_ne_zero, by simp, by simp, one_mul _⟩
    | mul y z _ _ hy hz =>
      obtain ⟨a, b, ha, hb, ha1, hb1, hyab⟩ := hy
      obtain ⟨c, d, hc, hd, hc1, hd1, hzcd⟩ := hz
      refine ⟨a * c, b * d, mul_ne_zero ha hc, mul_ne_zero hb hd, ?_, ?_, ?_⟩
      · have e : a * c - 1 = a * (c - 1) + (a - 1) := by ring
        rw [e]
        exact 𝔮.add_mem (𝔮.mul_mem_left _ hc1) ha1
      · have e : b * d - 1 = b * (d - 1) + (b - 1) := by ring
        rw [e]
        exact 𝔮.add_mem (𝔮.mul_mem_left _ hd1) hb1
      · rw [Units.ext_iff] at hyab hzcd ⊢
        simp only [Units.val_mul, coe_idealUnit_eq] at hyab hzcd ⊢
        rw [← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_mul_span_singleton,
          FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_mul, ← hyab, ← hzcd]
        ring
    | inv y _ hy =>
      obtain ⟨a, b, ha, hb, ha1, hb1, hyab⟩ := hy
      refine ⟨b, a, hb, ha, hb1, ha1, ?_⟩
      rw [← hyab, inv_mul_cancel_left]
  · rintro ⟨a, b, ha, hb, ha1, hb1, h⟩
    have hx : x = _root_.GlobalTheory.Mem.RayData.idealUnit _ (_root_.GlobalTheory.Mem.RayData.span_ne_bot ha) * (_root_.GlobalTheory.Mem.RayData.idealUnit _ (_root_.GlobalTheory.Mem.RayData.span_ne_bot hb))⁻¹ := by
      rw [← h, mul_inv_cancel_right]
    rw [hx]
    exact mul_mem (idealUnit_span_mem_rayP_of_sub_one_mem ha ha1)
      (inv_mem (idealUnit_span_mem_rayP_of_sub_one_mem hb hb1))

variable {M : ℕ} (D : RayData K M)

end aux

open NumberField IsDedekindDomain in
open scoped nonZeroDivisors in
variable {K : Type} [Field K] [NumberField K] in
private lemma ideal_mul_ne_bot {I J : Ideal (𝓞 K)} (hI : I ≠ ⊥) (hJ : J ≠ ⊥) : I * J ≠ ⊥ :=
  fun h => (Ideal.mul_eq_bot.mp h).elim hI hJ

open NumberField IsDedekindDomain in
open scoped nonZeroDivisors in
variable {K : Type} [Field K] [NumberField K] in
private lemma exists_coprime_idealUnit_mul_mem_rayP {𝔮 I : Ideal (𝓞 K)}
    (hIq : IsCoprime I 𝔮) (hI : I ≠ ⊥) :
    ∃ (J : Ideal (𝓞 K)) (hJ : J ≠ ⊥), IsCoprime J 𝔮 ∧
      _root_.GlobalTheory.Mem.RayData.idealUnit I hI * _root_.GlobalTheory.Mem.RayData.idealUnit J hJ ∈ _root_.GlobalTheory.Mem.An.rayP 𝔮 := by
  have hsup : I ⊔ 𝔮 = ⊤ := Ideal.isCoprime_iff_sup_eq.mp hIq
  obtain ⟨c, hcI, hc0, hc1⟩ : ∃ c ∈ I, c ≠ 0 ∧ c - 1 ∈ 𝔮 := by
    have h1 : (1 : 𝓞 K) ∈ I ⊔ 𝔮 := by rw [hsup]; exact Submodule.mem_top
    obtain ⟨i, hi, r, hr, hir⟩ := Submodule.mem_sup.mp h1
    by_cases hi0 : i = 0
    · have h1q : (1 : 𝓞 K) ∈ 𝔮 := by rw [← hir, hi0, zero_add]; exact hr
      obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
      refine ⟨c, hc, hc0, ?_⟩
      rw [(Ideal.eq_top_iff_one _).mpr h1q]
      exact Submodule.mem_top
    · refine ⟨i, hi, hi0, ?_⟩
      have e : i - 1 = -r := by rw [← hir]; ring
      rw [e]
      exact 𝔮.neg_mem hr
  obtain ⟨J, hJ⟩ := Ideal.dvd_span_singleton.mpr hcI
  have hJ0 : J ≠ ⊥ := by
    rintro rfl
    exact _root_.GlobalTheory.Mem.RayData.span_ne_bot hc0 (by rw [hJ, Ideal.mul_bot])
  have hcq : Ideal.span {c} ⊔ 𝔮 = ⊤ := by
    rw [Ideal.eq_top_iff_one]
    have e : (1 : 𝓞 K) = c - (c - 1) := by ring
    rw [e]
    exact Submodule.sub_mem _ (Ideal.mem_sup_left (Ideal.mem_span_singleton_self c))
      (Ideal.mem_sup_right hc1)
  refine ⟨J, hJ0, Ideal.isCoprime_iff_sup_eq.mpr (eq_top_mono (sup_le_sup_right ?_ _) hcq), ?_⟩
  · rw [hJ]
    exact Ideal.mul_le_inf.trans inf_le_right
  · rw [← _root_.GlobalTheory.Mem.RayData.idealUnit_mul I J hI hJ0 (ideal_mul_ne_bot hI hJ0)]
    have e : _root_.GlobalTheory.Mem.RayData.idealUnit (I * J) (ideal_mul_ne_bot hI hJ0) = _root_.GlobalTheory.Mem.RayData.idealUnit _ (_root_.GlobalTheory.Mem.RayData.span_ne_bot hc0) :=
      (_root_.GlobalTheory.Mem.RayData.idealUnit_congr _ _).2 hJ.symm
    rw [e]
    exact idealUnit_span_mem_rayP_of_sub_one_mem hc0 hc1

open NumberField IsDedekindDomain in
open scoped nonZeroDivisors in

theorem _root_.GlobalTheory.Mem.RayData.card_eq_rayNo : ∀ (K : Type) [Field K] [NumberField K] (M : ℕ), M ≠ 0 →
    ∀ D : _root_.GlobalTheory.Mem.RayData K M,
    Fintype.card D.G =
      _root_.GlobalTheory.Mem.An.rayNo (Ideal.span {(M : NumberField.RingOfIntegers K)}) := by
  intro K _ _ M _ D
  set 𝔮 : Ideal (𝓞 K) := Ideal.span {(M : 𝓞 K)} with h𝔮
  have memF : ∀ (I : Ideal (𝓞 K)) (hI : I ≠ ⊥), IsCoprime I 𝔮 →
      _root_.GlobalTheory.Mem.RayData.idealUnit I hI ∈ _root_.GlobalTheory.Mem.An.rayI 𝔮 := fun I hI hIq =>
    _root_.GlobalTheory.Mem.An.Model.mem_rayI_of_coprime 𝔮 I hI (Ideal.isCoprime_iff_sup_eq.mp hIq) _ rfl
  have S : ∀ x ∈ _root_.GlobalTheory.Mem.An.rayI 𝔮, ∃ (J : Ideal (𝓞 K)) (hJ : J ≠ ⊥),
      IsCoprime J 𝔮 ∧ x⁻¹ * _root_.GlobalTheory.Mem.RayData.idealUnit J hJ ∈ _root_.GlobalTheory.Mem.An.rayP 𝔮 := by
    intro x hx
    unfold _root_.GlobalTheory.Mem.An.rayI at hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨v, hv, hyv⟩ := hy
      have hv0 : v.asIdeal ≠ ⊥ := v.ne_bot
      refine ⟨v.asIdeal, hv0, ?_, ?_⟩
      · rw [Ideal.isCoprime_iff_sup_eq]
        by_contra h
        have e := v.isMaximal.eq_of_le h le_sup_left
        exact hv (Ideal.dvd_iff_le.mpr (le_sup_right.trans e.ge))
      · have e : y = _root_.GlobalTheory.Mem.RayData.idealUnit v.asIdeal hv0 := Units.ext hyv
        rw [e, inv_mul_cancel]
        exact one_mem _
    | one =>
      refine ⟨⊤, top_ne_bot, Ideal.isCoprime_iff_sup_eq.mpr (top_sup_eq _), ?_⟩
      have e : _root_.GlobalTheory.Mem.RayData.idealUnit (⊤ : Ideal (𝓞 K)) top_ne_bot = 1 := by
        ext
        simp [coe_idealUnit_eq]
      rw [e, mul_one, inv_one]
      exact one_mem _
    | mul y z _ _ hy hz =>
      obtain ⟨J, hJ, hJq, hyJ⟩ := hy
      obtain ⟨L, hL, hLq, hzL⟩ := hz
      refine ⟨J * L, ideal_mul_ne_bot hJ hL, hJq.mul_left hLq, ?_⟩
      rw [_root_.GlobalTheory.Mem.RayData.idealUnit_mul J L hJ hL, mul_inv, mul_mul_mul_comm]
      exact mul_mem hyJ hzL
    | inv y _ hy =>
      obtain ⟨J, hJ, hJq, hyJ⟩ := hy
      obtain ⟨L, hL, hLq, hJL⟩ := exists_coprime_idealUnit_mul_mem_rayP hJq hJ
      refine ⟨L, hL, hLq, ?_⟩
      have e : y⁻¹⁻¹ * _root_.GlobalTheory.Mem.RayData.idealUnit L hL = (y⁻¹ * _root_.GlobalTheory.Mem.RayData.idealUnit J hJ)⁻¹ * (_root_.GlobalTheory.Mem.RayData.idealUnit J hJ * _root_.GlobalTheory.Mem.RayData.idealUnit L hL) := by
        rw [mul_inv_rev, inv_inv, mul_comm (_root_.GlobalTheory.Mem.RayData.idealUnit J hJ)⁻¹ y, mul_assoc,
          inv_mul_cancel_left]
      rw [e]
      exact mul_mem (inv_mem hyJ) hJL
  choose I hIq hI0 hIcls using D.cls_surj
  let f : D.G → _root_.GlobalTheory.Mem.An.rayI 𝔮 ⧸
      (_root_.GlobalTheory.Mem.An.rayP 𝔮).subgroupOf (_root_.GlobalTheory.Mem.An.rayI 𝔮) :=
    fun c => QuotientGroup.mk ⟨_root_.GlobalTheory.Mem.RayData.idealUnit (I c) (hI0 c), memF _ _ (hIq c)⟩
  have hf : Function.Bijective f := by
    constructor
    · intro c d hcd
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at hcd
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hcd
      obtain ⟨a, b, ha, hb, ha1, hb1, h⟩ := (_root_.GlobalTheory.Mem.RayData.mem_principalRay_iff 𝔮 _).mp hcd
      rw [← hIcls c, ← hIcls d, D.cls_eq _ _ (hIq c) (hIq d) (hI0 c) (hI0 d)]
      refine ⟨a, b, ha, hb, ha1, hb1, ?_⟩
      have h' : _root_.GlobalTheory.Mem.RayData.idealUnit (I d) (hI0 d) * _root_.GlobalTheory.Mem.RayData.idealUnit _ (_root_.GlobalTheory.Mem.RayData.span_ne_bot hb) =
          _root_.GlobalTheory.Mem.RayData.idealUnit (I c) (hI0 c) * _root_.GlobalTheory.Mem.RayData.idealUnit _ (_root_.GlobalTheory.Mem.RayData.span_ne_bot ha) := by
        rw [← h]
        group
      rw [← _root_.GlobalTheory.Mem.RayData.idealUnit_mul _ _ _ _ (ideal_mul_ne_bot (hI0 d) (_root_.GlobalTheory.Mem.RayData.span_ne_bot hb)),
        ← _root_.GlobalTheory.Mem.RayData.idealUnit_mul _ _ _ _ (ideal_mul_ne_bot (hI0 c) (_root_.GlobalTheory.Mem.RayData.span_ne_bot ha)), _root_.GlobalTheory.Mem.RayData.idealUnit_congr] at h'
      rw [mul_comm (Ideal.span {a}), mul_comm (Ideal.span {b})]
      exact h'.symm
    · intro y
      obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientGroup.mk_surjective y
      obtain ⟨J, hJ0, hJq, hxJ⟩ := S x hx
      refine ⟨D.cls J, ?_⟩
      have hc := hIcls (D.cls J)
      rw [D.cls_eq _ _ (hIq _) hJq (hI0 _) hJ0] at hc
      obtain ⟨a, b, ha, hb, ha1, hb1, hab⟩ := hc
      set u := _root_.GlobalTheory.Mem.RayData.idealUnit (I (D.cls J)) (hI0 _) with hu
      have e : _root_.GlobalTheory.Mem.RayData.idealUnit _ (_root_.GlobalTheory.Mem.RayData.span_ne_bot ha) * u = _root_.GlobalTheory.Mem.RayData.idealUnit _ (_root_.GlobalTheory.Mem.RayData.span_ne_bot hb) * _root_.GlobalTheory.Mem.RayData.idealUnit J hJ0 := by
        rw [hu, ← _root_.GlobalTheory.Mem.RayData.idealUnit_mul _ _ _ _ (ideal_mul_ne_bot (_root_.GlobalTheory.Mem.RayData.span_ne_bot ha) (hI0 _)),
          ← _root_.GlobalTheory.Mem.RayData.idealUnit_mul _ _ _ _ (ideal_mul_ne_bot (_root_.GlobalTheory.Mem.RayData.span_ne_bot hb) hJ0), _root_.GlobalTheory.Mem.RayData.idealUnit_congr]
        exact hab
      have hP : u⁻¹ * _root_.GlobalTheory.Mem.RayData.idealUnit J hJ0 ∈ _root_.GlobalTheory.Mem.An.rayP 𝔮 := by
        rw [_root_.GlobalTheory.Mem.RayData.mem_principalRay_iff]
        refine ⟨a, b, ha, hb, ha1, hb1, ?_⟩
        rw [mul_assoc, mul_comm (_root_.GlobalTheory.Mem.RayData.idealUnit J hJ0), ← e, mul_comm (_root_.GlobalTheory.Mem.RayData.idealUnit _ (_root_.GlobalTheory.Mem.RayData.span_ne_bot ha)),
          inv_mul_cancel_left]
      show QuotientGroup.mk _ = QuotientGroup.mk _
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      have e' : u⁻¹ * x = (u⁻¹ * _root_.GlobalTheory.Mem.RayData.idealUnit J hJ0) * (x⁻¹ * _root_.GlobalTheory.Mem.RayData.idealUnit J hJ0)⁻¹ := by group
      rw [e']
      exact mul_mem hP (inv_mem hxJ)
  rw [Fintype.card_eq_nat_card, Nat.card_eq_of_bijective f hf]
  rfl

end GlobalTheory.Mem.RayData

end
