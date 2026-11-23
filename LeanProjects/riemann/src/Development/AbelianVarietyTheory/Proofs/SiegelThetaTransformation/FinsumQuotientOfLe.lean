import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IMemSiegel
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real

namespace GlobalTheory.SW.HaarLevel

noncomputable section

open NumberField

theorem finsum_quotient_of_le {A : Type} [AddCommGroup A] {s t : AddSubgroup A} (h : s ≤ t)
    (hn : s.relIndex t ≠ 0) (φ : A → ℂ) (hφ : ∀ x, ∀ y ∈ t, φ (x + y) = φ x)
    (hf : (Function.support fun q : A ⧸ t => φ q.out).Finite) :
    ∑ᶠ q : A ⧸ s, φ q.out = (s.relIndex t : ℂ) * ∑ᶠ q : A ⧸ t, φ q.out := by
  classical
  set e := AddSubgroup.quotientEquivProdOfLE h
  haveI : Finite (t ⧸ s.addSubgroupOf t) := Nat.finite_of_card_ne_zero hn
  haveI : Fintype (t ⧸ s.addSubgroupOf t) := Fintype.ofFinite _
  have h1 : ∀ q : A ⧸ s, φ q.out = φ (e q).1.out := by
    intro q
    have h2 : (e q).1 = (q.out : A ⧸ t) := by
      conv_lhs => rw [← QuotientAddGroup.out_eq' q]
      rfl
    have h3 : ((e q).1.out : A ⧸ t) = (q.out : A ⧸ t) := by
      rw [QuotientAddGroup.out_eq', h2]
    have := hφ (e q).1.out _ (QuotientAddGroup.eq.1 h3)
    rw [← this]; congr 1; abel
  simp_rw [h1]
  rw [finsum_comp_equiv e (f := fun p => φ p.1.out),
    finsum_eq_sum_of_support_subset (s := hf.toFinset ×ˢ Finset.univ), finsum_eq_sum _ hf,
    Finset.sum_product, Finset.mul_sum]
  · refine Finset.sum_congr rfl fun q _ => ?_
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [AddSubgroup.relIndex, AddSubgroup.index, Nat.card_eq_fintype_card]
  · intro p hp
    simpa using hp

variable {K : Type} [Field K] [NumberField K] {κ ι : Type} [Fintype κ] [Fintype ι]

def incl (K κ ι : Type) [Field K] : Matrix κ ι (𝓞 K) →+ Matrix κ ι K :=
  (algebraMap (𝓞 K) K).toAddMonoidHom.mapMatrix

omit [NumberField K] [Fintype κ] [Fintype ι] in
theorem intM_iff (x : Matrix κ ι K) : IntM x ↔ ∃ y, incl K κ ι y = x := by
  constructor
  · intro h
    exact ⟨fun k i => ⟨x k i, h k i⟩, rfl⟩
  · rintro ⟨y, rfl⟩ k i
    exact (y k i).2

omit [NumberField K] [Fintype κ] [Fintype ι] in
theorem incl_inj : Function.Injective (incl K κ ι) := fun a b h => by
  ext k i
  exact congrFun (congrFun h k) i

omit [NumberField K] [Fintype κ] [Fintype ι] in
theorem perSub_eq_range (R : ℕ) :
    perSub K κ ι R = ((incl K κ ι).comp (nsmulAddMonoidHom R)).range := by
  have : {x | ∃ y : Matrix κ ι K, IntM y ∧ x = (R : K) • y} =
      (((incl K κ ι).comp (nsmulAddMonoidHom R)).range : Set (Matrix κ ι K)) := by
    ext z
    simp only [Set.mem_setOf_eq, SetLike.mem_coe, AddMonoidHom.mem_range, AddMonoidHom.comp_apply,
      nsmulAddMonoidHom_apply, map_nsmul, intM_iff, Nat.cast_smul_eq_nsmul]
    constructor
    · rintro ⟨_, ⟨y, rfl⟩, rfl⟩; exact ⟨y, rfl⟩
    · rintro ⟨y, rfl⟩; exact ⟨_, ⟨y, rfl⟩, rfl⟩
  rw [perSub, this, AddSubgroup.closure_eq]

omit [NumberField K] [Fintype κ] [Fintype ι] in
theorem mem_perSub (R : ℕ) (x : Matrix κ ι K) :
    x ∈ perSub K κ ι R ↔ ∃ y, R • incl K κ ι y = x := by
  rw [perSub_eq_range]
  simp only [AddMonoidHom.mem_range, AddMonoidHom.comp_apply, nsmulAddMonoidHom_apply, map_nsmul]

theorem index_nsmul (R : ℕ) : (nsmulAddMonoidHom R : Matrix κ ι (𝓞 K) →+ _).range.index =
    R ^ (Module.finrank ℚ K * (Fintype.card κ * Fintype.card ι)) := by
  rw [AddSubgroup.index_range_nsmul, Module.finrank_matrix, RingOfIntegers.rank]
  ring

omit [Fintype κ] [Fintype ι] in
theorem nsmul_cancel {R : ℕ} (hR : 0 < R) {x y : Matrix κ ι K} : R • x = R • y ↔ x = y := by
  rw [← Nat.cast_smul_eq_nsmul K, ← Nat.cast_smul_eq_nsmul K]
  exact (smul_right_injective _ (by exact_mod_cast hR.ne')).eq_iff

theorem relIndex_perSub (R S : ℕ) (hR : 0 < R) :
    (perSub K κ ι (R * S)).relIndex (perSub K κ ι R) =
      S ^ (Module.finrank ℚ K * (Fintype.card κ * Fintype.card ι)) := by
  rw [perSub_eq_range R, ← AddSubgroup.index_comap, ← index_nsmul]
  congr 1
  ext y
  simp only [AddSubgroup.mem_comap, mem_perSub, AddMonoidHom.mem_range, AddMonoidHom.comp_apply,
    nsmulAddMonoidHom_apply]
  refine exists_congr fun z => ?_
  rw [mul_smul, map_nsmul, nsmul_cancel hR, ← map_nsmul, incl_inj.eq_iff]

omit [NumberField K] [Fintype κ] [Fintype ι] in
theorem perSub_le (R S : ℕ) : perSub K κ ι (R * S) ≤ perSub K κ ι R := by
  intro x hx
  obtain ⟨y, rfl⟩ := (mem_perSub _ _).1 hx
  exact (mem_perSub _ _).2 ⟨S • y, by rw [map_nsmul, mul_smul]⟩

omit [NumberField K] [Fintype κ] [Fintype ι] in
theorem periodic {R : ℕ} {φ : Matrix κ ι K → ℂ} (h : HasLevel R φ) (x : Matrix κ ι K) :
    ∀ y ∈ perSub K κ ι R, φ (x + y) = φ x := by
  intro y hy
  obtain ⟨z, rfl⟩ := (mem_perSub _ _).1 hy
  rw [← Nat.cast_smul_eq_nsmul K]
  exact h.2 x _ ((intM_iff _).2 ⟨z, rfl⟩)

theorem finite_support {R : ℕ} {φ : Matrix κ ι K → ℂ} (hR : 0 < R) (h : HasLevel R φ) :
    (Function.support fun q : Matrix κ ι K ⧸ perSub K κ ι R => φ q.out).Finite := by
  have hK : (R : K) ≠ 0 := by exact_mod_cast hR.ne'
  set f : Matrix κ ι (𝓞 K) →+ Matrix κ ι K ⧸ perSub K κ ι R :=
    (QuotientAddGroup.mk' (perSub K κ ι R)).comp
      ((DistribSMul.toAddMonoidHom (Matrix κ ι K) (R : K)⁻¹).comp (incl K κ ι)) with hf
  have hfa : ∀ y, f y = (((R : K)⁻¹ • incl K κ ι y : Matrix κ ι K) :
    Matrix κ ι K ⧸ perSub K κ ι R) := fun _ => rfl
  have hker : (nsmulAddMonoidHom (R * R) : Matrix κ ι (𝓞 K) →+ _).range ≤ f.ker := by
    rintro _ ⟨y, rfl⟩
    rw [AddMonoidHom.mem_ker, hfa, QuotientAddGroup.eq_zero_iff, mem_perSub]
    refine ⟨y, ?_⟩
    rw [nsmulAddMonoidHom_apply, map_nsmul, mul_smul, ← Nat.cast_smul_eq_nsmul K R (R • _),
      smul_smul, inv_mul_cancel₀ hK, one_smul]
  have hcard : Nat.card f.range ≠ 0 := by
    rw [← AddSubgroup.index_ker]
    refine ne_zero_of_dvd_ne_zero ?_ (AddSubgroup.index_dvd_of_le hker)
    rw [index_nsmul]
    positivity
  have hfin : Finite f.range := Nat.finite_of_card_ne_zero hcard
  refine (Set.toFinite (f.range : Set (Matrix κ ι K ⧸ perSub K κ ι R))).subset fun q hq => ?_
  obtain ⟨y, hy⟩ := (intM_iff _).1 (h.1 _ hq)
  refine ⟨y, ?_⟩
  rw [hfa, hy, smul_smul, inv_mul_cancel₀ hK, one_smul, QuotientAddGroup.out_eq']

theorem haarAt_mul {R : ℕ} {φ : Matrix κ ι K → ℂ} (hR : 0 < R) (h : HasLevel R φ) {S : ℕ}
    (hS : 0 < S) : haarAt (R * S) φ = haarAt R φ := by
  have hS' : (S : ℂ) ≠ 0 := by exact_mod_cast hS.ne'
  have hR' : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  rw [haarAt, haarAt, finsum_quotient_of_le (perSub_le R S)
    (by rw [relIndex_perSub R S hR]; positivity) φ (periodic h) (finite_support hR h),
    relIndex_perSub R S hR]
  push_cast
  rw [mul_pow]
  field_simp

end

end GlobalTheory.SW.HaarLevel

namespace GlobalTheory.SW

theorem haar_eq_haarAt : ∀ (K κ ι : Type) [Field K] [NumberField K] [Fintype κ] [Fintype ι] (R : ℕ) (φ : Matrix κ ι K → ℂ), 0 < R → HasLevel R φ → haar φ = haarAt R φ ∧ (Function.support fun q : Matrix κ ι K ⧸ perSub K κ ι R => φ q.out).Finite := by
  intro K κ ι _ _ _ _ R φ hR h
  refine ⟨?_, HaarLevel.finite_support hR h⟩
  have hs : IsSB φ := ⟨R, hR, h⟩
  rw [haar, dif_pos hs, ← HaarLevel.haarAt_mul hR h hs.choose_spec.1,
    ← HaarLevel.haarAt_mul hs.choose_spec.1 hs.choose_spec.2 hR, mul_comm]

end GlobalTheory.SW
