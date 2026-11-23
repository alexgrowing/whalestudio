import Mathlib
import Formalism.GL3MeanSquares.PrimeCountAsymptoticInProgressions
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Formalism.CyclotomicNorms.StatementI
import Development.AbelianVarietyTheory.Definitions.Foundations.RayPrimes
import Development.AbelianVarietyTheory.Definitions.Foundations.NormOneSevenOneTwo
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntegralOfMemRayI

noncomputable section

open NumberField IsDedekindDomain
open scoped nonZeroDivisors

namespace GlobalTheory.Mem.RayNo

open GlobalTheory.Mem.An GlobalTheory.Mem.RayData

section General

variable {R : Type} [CommRing R] [IsDedekindDomain R] (m : Ideal R)

def Rel (I J : Ideal R) : Prop :=
  ∃ a b : R, a - 1 ∈ m ∧ b - 1 ∈ m ∧ Ideal.span {a} * I = Ideal.span {b} * J

variable {m}

theorem mul_sub_one_mem {a b : R} (ha : a - 1 ∈ m) (hb : b - 1 ∈ m) : a * b - 1 ∈ m := by
  have e : a * b - 1 = (a - 1) * b + (b - 1) := by ring
  rw [e]
  exact m.add_mem (m.mul_mem_right b ha) hb

theorem ne_zero_of_sub_one_mem (hm : m ≠ ⊤) {a : R} (ha : a - 1 ∈ m) : a ≠ 0 := by
  rintro rfl
  apply hm
  rw [Ideal.eq_top_iff_one]
  have h1 : -(0 - 1 : R) ∈ m := m.neg_mem ha
  simpa using h1

theorem exists_mem_sub_one {I : Ideal R} (h : IsCoprime I m) : ∃ a ∈ I, a - 1 ∈ m := by
  obtain ⟨i, hi, j, hj, hij⟩ := Ideal.isCoprime_iff_exists.1 h
  refine ⟨i, hi, ?_⟩
  have e : i - 1 = -j := by rw [← hij]; ring
  rw [e]
  exact m.neg_mem hj

theorem isCoprime_span {a : R} (ha : a - 1 ∈ m) : IsCoprime (Ideal.span {a}) m := by
  refine Ideal.isCoprime_iff_exists.2 ⟨a, Ideal.mem_span_singleton_self a, -(a - 1), m.neg_mem ha, ?_⟩
  ring

theorem Rel.refl (I : Ideal R) : Rel m I I :=
  ⟨1, 1, by simp, by simp, rfl⟩

theorem Rel.symm {I J : Ideal R} (h : Rel m I J) : Rel m J I := by
  obtain ⟨a, b, ha, hb, e⟩ := h
  exact ⟨b, a, hb, ha, e.symm⟩

theorem Rel.mul {I J I' J' : Ideal R} (h : Rel m I J) (h' : Rel m I' J') : Rel m (I * I') (J * J') := by
  obtain ⟨a, b, ha, hb, e⟩ := h
  obtain ⟨a', b', ha', hb', e'⟩ := h'
  refine ⟨a * a', b * b', mul_sub_one_mem ha ha', mul_sub_one_mem hb hb', ?_⟩
  calc Ideal.span {a * a'} * (I * I') = (Ideal.span {a} * I) * (Ideal.span {a'} * I') := by
        rw [← Ideal.span_singleton_mul_span_singleton]; ring
    _ = (Ideal.span {b} * J) * (Ideal.span {b'} * J') := by rw [e, e']
    _ = Ideal.span {b * b'} * (J * J') := by
        rw [← Ideal.span_singleton_mul_span_singleton]; ring

theorem Rel.trans {I J L : Ideal R} (h : Rel m I J) (h' : Rel m J L) : Rel m I L := by
  obtain ⟨a, b, ha, hb, e⟩ := h
  obtain ⟨c, d, hc, hd, e'⟩ := h'
  refine ⟨a * c, b * d, mul_sub_one_mem ha hc, mul_sub_one_mem hb hd, ?_⟩
  calc Ideal.span {a * c} * I = Ideal.span {c} * (Ideal.span {a} * I) := by
        rw [← Ideal.span_singleton_mul_span_singleton]; ring
    _ = Ideal.span {c} * (Ideal.span {b} * J) := by rw [e]
    _ = Ideal.span {b} * (Ideal.span {c} * J) := by ring
    _ = Ideal.span {b} * (Ideal.span {d} * L) := by rw [e']
    _ = Ideal.span {b * d} * L := by
        rw [← Ideal.span_singleton_mul_span_singleton]; ring

theorem exists_good {I J : Ideal R} (hI : IsCoprime I m) (hJ : IsCoprime J m) {x y : R} (hy : y ≠ 0)
    (h : Ideal.span {x} * I = Ideal.span {y} * J) :
    ∃ b : R, IsCoprime (Ideal.span {b}) m ∧ Rel m I (Ideal.span {b} * J) := by
  obtain ⟨j, hj, hj1⟩ := exists_mem_sub_one hJ
  have hyj : y * j ∈ Ideal.span {x} := by
    have hm : y * j ∈ Ideal.span {y} * J := Ideal.mul_mem_mul (Ideal.mem_span_singleton_self y) hj
    rw [← h] at hm
    exact (Ideal.mul_le_left : Ideal.span {x} * I ≤ Ideal.span {x}) hm
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 hyj
  by_cases hx : x = 0
  · have hj0 : j = 0 := by
      rw [hx, mul_zero] at hb
      exact (mul_eq_zero.1 hb.symm).resolve_left hy
    have htop : m = ⊤ := by
      rw [Ideal.eq_top_iff_one]
      rw [hj0] at hj1
      have h1 : -(0 - 1 : R) ∈ m := m.neg_mem hj1
      simpa using h1
    subst htop
    refine ⟨0, Ideal.isCoprime_iff_sup_eq.2 (sup_top_eq _), 0, 0, Submodule.mem_top, Submodule.mem_top, ?_⟩
    rw [Ideal.span_singleton_eq_bot.2 rfl, Ideal.bot_mul, Ideal.bot_mul]
  · have key : Ideal.span {j} * I = Ideal.span {b} * J := by
      have hx' : Ideal.span {x} ≠ 0 := by
        rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
        exact hx
      apply mul_left_cancel₀ hx'
      calc Ideal.span {x} * (Ideal.span {j} * I) = Ideal.span {j} * (Ideal.span {x} * I) := by ring
        _ = Ideal.span {j} * (Ideal.span {y} * J) := by rw [h]
        _ = Ideal.span {y * j} * J := by rw [← Ideal.span_singleton_mul_span_singleton]; ring
        _ = Ideal.span {x} * (Ideal.span {b} * J) := by
          rw [← hb, ← Ideal.span_singleton_mul_span_singleton]; ring
    refine ⟨b, ?_, j, 1, hj1, by simp, ?_⟩
    · have hc : IsCoprime (Ideal.span {j} * I) m := (isCoprime_span hj1).mul_left hI
      rw [key] at hc
      exact hc.of_mul_left_left
    · rw [Ideal.span_singleton_one, Ideal.top_mul]
      exact key

theorem rel_span {b c : R} (hb : IsCoprime (Ideal.span {b}) m) (h : b - c ∈ m) :
    Rel m (Ideal.span {b}) (Ideal.span {c}) := by
  obtain ⟨i, hi, j, hj, hij⟩ := Ideal.isCoprime_iff_exists.1 hb
  obtain ⟨u, rfl⟩ := Ideal.mem_span_singleton'.1 hi
  have hu : u * b - 1 ∈ m := by
    have e : u * b - 1 = -j := by rw [← hij]; ring
    rw [e]
    exact m.neg_mem hj
  refine ⟨u * c, u * b, ?_, hu, ?_⟩
  · have e : u * c - 1 = (u * b - 1) - u * (b - c) := by ring
    rw [e]
    exact m.sub_mem hu (m.mul_mem_left u h)
  · rw [Ideal.span_singleton_mul_span_singleton, Ideal.span_singleton_mul_span_singleton,
      mul_right_comm]

end General

variable {K : Type} [Field K] [NumberField K] {𝔮 : Ideal (𝓞 K)}

theorem mem_principalRay_of_eq {I J : Ideal (𝓞 K)} (hI0 : I ≠ ⊥) (hJ0 : J ≠ ⊥) {a b : 𝓞 K} (ha : a ≠ 0) (hb : b ≠ 0)
    (ha1 : a - 1 ∈ 𝔮) (hb1 : b - 1 ∈ 𝔮) (h : Ideal.span {a} * I = Ideal.span {b} * J) :
    (idealUnit I hI0)⁻¹ * idealUnit J hJ0 ∈ rayP 𝔮 := by
  refine (mem_principalRay_iff 𝔮 _).2 ⟨a, b, ha, hb, ha1, hb1, ?_⟩
  rw [mul_assoc, inv_mul_eq_iff_eq_mul]
  apply Units.ext
  simp only [Units.val_mul, coe_idealUnit]
  rw [← FractionalIdeal.coeIdeal_mul, ← FractionalIdeal.coeIdeal_mul, mul_comm J, mul_comm I, h]

theorem exists_integral (h𝔮 : 𝔮 ≠ ⊥) (x : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (hx : x ∈ rayI 𝔮) :
    ∃ (I : Ideal (𝓞 K)) (hI0 : I ≠ ⊥), IsCoprime I 𝔮 ∧ (idealUnit I hI0)⁻¹ * x ∈ rayP 𝔮 := by
  unfold rayI at hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨v, hv, hxv⟩ := hx
    refine ⟨v.asIdeal, v.ne_bot, ?_, ?_⟩
    · rw [Ideal.isCoprime_iff_sup_eq]
      by_contra hne
      apply hv
      rw [Ideal.dvd_iff_le]
      have e := v.isMaximal.eq_of_le hne le_sup_left
      rw [e]
      exact le_sup_right
    · have e : idealUnit v.asIdeal v.ne_bot = x := Units.ext (by rw [coe_idealUnit, hxv])
      rw [e, inv_mul_cancel]
      exact one_mem _
  | one =>
    refine ⟨⊤, top_ne_bot, Ideal.isCoprime_iff_sup_eq.2 (top_sup_eq _), ?_⟩
    have e : idealUnit (⊤ : Ideal (𝓞 K)) top_ne_bot = 1 :=
      Units.ext (by rw [coe_idealUnit, FractionalIdeal.coeIdeal_top]; rfl)
    rw [e, inv_one, one_mul]
    exact one_mem _
  | mul x y _ _ ihx ihy =>
    obtain ⟨I, hI0, hIc, hIr⟩ := ihx
    obtain ⟨J, hJ0, hJc, hJr⟩ := ihy
    have hIJ : I * J ≠ ⊥ := by
      rw [Ne, Ideal.mul_eq_bot, not_or]
      exact ⟨hI0, hJ0⟩
    refine ⟨I * J, hIJ, hIc.mul_left hJc, ?_⟩
    rw [idealUnit_mul I J hI0 hJ0 hIJ, mul_inv, mul_mul_mul_comm]
    exact mul_mem hIr hJr
  | inv x _ ihx =>
    obtain ⟨I, hI0, hIc, hIr⟩ := ihx
    obtain ⟨i, hi, hi0, hi1⟩ : ∃ i ∈ I, i ≠ 0 ∧ i - 1 ∈ 𝔮 := by
      by_cases htop : 𝔮 = ⊤
      · obtain ⟨i, hi, hi0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI0
        exact ⟨i, hi, hi0, by rw [htop]; exact Submodule.mem_top⟩
      · obtain ⟨i, hi, hi1⟩ := exists_mem_sub_one hIc
        exact ⟨i, hi, ne_zero_of_sub_one_mem htop hi1, hi1⟩
    obtain ⟨J, hJ⟩ : I ∣ Ideal.span {i} :=
      Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hi)
    have hJ0 : J ≠ ⊥ := by
      rintro rfl
      rw [Ideal.mul_bot, Ideal.span_singleton_eq_bot] at hJ
      exact hi0 hJ
    have hJc : IsCoprime J 𝔮 := by
      have hc := isCoprime_span (m := 𝔮) hi1
      rw [hJ] at hc
      exact hc.of_mul_left_right
    refine ⟨J, hJ0, hJc, ?_⟩
    have hS : idealUnit (Ideal.span {i}) (span_ne_bot hi0) = idealUnit I hI0 * idealUnit J hJ0 := by
      apply Units.ext
      simp only [Units.val_mul, coe_idealUnit]
      rw [hJ, FractionalIdeal.coeIdeal_mul]
    have hSr : idealUnit (Ideal.span {i}) (span_ne_bot hi0) ∈ rayP 𝔮 :=
      Subgroup.subset_closure ⟨i, hi1, coe_idealUnit _ _⟩
    have key := mul_mem (inv_mem hSr) (inv_mem hIr)
    convert key using 1
    rw [hS, mul_inv, mul_inv, inv_inv, mul_mul_mul_comm, inv_mul_cancel, one_mul]

theorem exists_injective (h𝔮 : 𝔮 ≠ ⊥) :
    ∃ F : (rayI 𝔮 ⧸ (rayP 𝔮).subgroupOf (rayI 𝔮)) → ClassGroup (𝓞 K) × (𝓞 K ⧸ 𝔮), Function.Injective F := by
  have H1 : ∀ ξ : rayI 𝔮 ⧸ (rayP 𝔮).subgroupOf (rayI 𝔮), ∃ (I : Ideal (𝓞 K)) (hI0 : I ≠ ⊥),
      IsCoprime I 𝔮 ∧ (idealUnit I hI0)⁻¹ * (ξ.out : (FractionalIdeal (𝓞 K)⁰ K)ˣ) ∈ rayP 𝔮 :=
    fun ξ => exists_integral h𝔮 _ ξ.out.2
  choose I hI0 hIc hIr using H1
  obtain ⟨c, hc⟩ : ∃ c : rayI 𝔮 ⧸ (rayP 𝔮).subgroupOf (rayI 𝔮) → ClassGroup (𝓞 K),
      ∀ ξ, c ξ = ClassGroup.mk0 ⟨I ξ, mem_nonZeroDivisors_of_ne_zero (hI0 ξ)⟩ := ⟨_, fun _ => rfl⟩
  have H2 : ∀ ξ, ∃ b : 𝓞 K, IsCoprime (Ideal.span {b}) 𝔮 ∧
      Rel 𝔮 (I ξ) (Ideal.span {b} * I (Function.invFun c (c ξ))) := by
    intro ξ
    obtain ⟨ξ0, hξ0⟩ : ∃ ξ0, ξ0 = Function.invFun c (c ξ) := ⟨_, rfl⟩
    have e : c ξ0 = c ξ := hξ0 ▸ Function.invFun_eq (f := c) ⟨ξ, rfl⟩
    rw [hc, hc] at e
    obtain ⟨x, y, _, hy, hxy⟩ := ClassGroup.mk0_eq_mk0_iff.1 e.symm
    rw [← hξ0]
    exact exists_good (hIc _) (hIc _) hy hxy
  choose b hbc hbr using H2
  refine ⟨fun ξ => (c ξ, Ideal.Quotient.mk 𝔮 (b ξ)), ?_⟩
  intro ξ η hξη
  simp only [Prod.mk.injEq] at hξη
  obtain ⟨h1, h2⟩ := hξη
  have hq : (idealUnit (I ξ) (hI0 ξ))⁻¹ * idealUnit (I η) (hI0 η) ∈ rayP 𝔮 := by
    by_cases htop : 𝔮 = ⊤
    · rw [hc, hc] at h1
      obtain ⟨x, y, hx, hy, hxy⟩ := ClassGroup.mk0_eq_mk0_iff.1 h1
      exact mem_principalRay_of_eq (hI0 ξ) (hI0 η) hx hy (by rw [htop]; exact Submodule.mem_top)
        (by rw [htop]; exact Submodule.mem_top) hxy
    · have hsub : b ξ - b η ∈ 𝔮 := Ideal.Quotient.eq.1 h2
      have R2 := hbr η
      rw [← h1] at R2
      have R := (hbr ξ).trans (((rel_span (hbc ξ) hsub).mul (Rel.refl _)).trans R2.symm)
      obtain ⟨a, a', ha, ha', e⟩ := R
      exact mem_principalRay_of_eq (hI0 ξ) (hI0 η) (ne_zero_of_sub_one_mem htop ha)
        (ne_zero_of_sub_one_mem htop ha') ha ha' e
  rw [← QuotientGroup.out_eq' ξ, ← QuotientGroup.out_eq' η, QuotientGroup.eq, Subgroup.mem_subgroupOf]
  have key := mul_mem (mul_mem (inv_mem (hIr ξ)) hq) (hIr η)
  convert key using 1
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  group

theorem rayNo_bounds : ∀ (K : Type) [Field K] [NumberField K] (𝔮 : Ideal (𝓞 K)), 𝔮 ≠ ⊥ →
    1 ≤ rayNo 𝔮 ∧ rayNo 𝔮 ≤ classNumber K * Ideal.absNorm 𝔮 ∧ rayP 𝔮 ≤ rayI 𝔮 := by
  intro K _ _ 𝔮 h𝔮
  have : Finite (𝓞 K ⧸ 𝔮) := Ideal.finiteQuotientOfFreeOfNeBot 𝔮 h𝔮
  obtain ⟨F, hF⟩ := exists_injective h𝔮
  have : Finite (rayI 𝔮 ⧸ (rayP 𝔮).subgroupOf (rayI 𝔮)) := Finite.of_injective F hF
  have hno : rayNo 𝔮 = Nat.card (rayI 𝔮 ⧸ (rayP 𝔮).subgroupOf (rayI 𝔮)) := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hno]
    exact Nat.card_pos
  · rw [hno]
    calc Nat.card _ ≤ Nat.card (ClassGroup (𝓞 K) × (𝓞 K ⧸ 𝔮)) := Nat.card_le_card_of_injective F hF
      _ = classNumber K * Ideal.absNorm 𝔮 := by
        rw [Nat.card_prod, Ideal.absNorm_apply, Submodule.cardQuot_apply, classNumber,
          Nat.card_eq_fintype_card]
  · unfold rayP
    rw [Subgroup.closure_le]
    rintro x ⟨a, ha1, hxa⟩
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [Ideal.span_singleton_eq_bot.2 rfl, FractionalIdeal.coeIdeal_bot] at hxa
      exact x.ne_zero hxa
    exact Model.mem_rayI_of_coprime 𝔮 (Ideal.span {a})
      (by rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact ha0)
      (Ideal.isCoprime_iff_sup_eq.1 (isCoprime_span ha1)) x hxa

end GlobalTheory.Mem.RayNo

end
