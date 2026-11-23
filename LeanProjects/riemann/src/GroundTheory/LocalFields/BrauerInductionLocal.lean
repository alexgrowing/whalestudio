import Mathlib
import GroundTheory.LocalFields.BrauerInductionSpan

noncomputable section

namespace GroundTheory.LocalField

open Module Representation

open scoped Classical

universe u

variable {G : Type u} [Group G] [Fintype G]

section ClassCount

def classCount (s : G) (g : G) : ℂ := ∑ t : G, if t⁻¹ * g * t = s then 1 else 0

theorem indFun_zpowers_delta (s : G) :
    indFun (Subgroup.zpowers s).subtype
      (fun c ↦ if c = ⟨s, Subgroup.mem_zpowers s⟩ then (Nat.card (Subgroup.zpowers s) : ℂ) else 0) =
      classCount s := by
  funext g
  have hN : (Nat.card (Subgroup.zpowers s) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  rw [indFun_apply, classCount, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  have hin : ∀ c : Subgroup.zpowers s, (if (Subgroup.zpowers s).subtype c = t⁻¹ * g * t then
      (if c = ⟨s, Subgroup.mem_zpowers s⟩ then (Nat.card (Subgroup.zpowers s) : ℂ) else 0) else 0) =
      if c = ⟨s, Subgroup.mem_zpowers s⟩ then
        (if t⁻¹ * g * t = s then (Nat.card (Subgroup.zpowers s) : ℂ) else 0) else 0 := by
    intro c
    by_cases hc : c = ⟨s, Subgroup.mem_zpowers s⟩
    · subst hc
      simp only [Subgroup.coe_subtype, if_true]
      by_cases h : s = t⁻¹ * g * t
      · rw [if_pos h, if_pos h.symm]
      · rw [if_neg h, if_neg (Ne.symm h)]
    · simp [hc]
  rw [Finset.sum_congr rfl fun c _ ↦ hin c, Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
  split_ifs
  · field_simp
  · simp

variable {E : Subgroup G → Prop} (hE : ∀ K L : Subgroup G, E K → L ≤ K → E L)
  (hmono : ∀ K : Subgroup G, E K → ∀ χ : K → ℂ, IsIrrCharacter χ →
    ∃ (L : Subgroup K) (μ : L →* ℂˣ), χ = indLin L μ)
  (hcyc : ∀ s : G, E (Subgroup.zpowers s))
  {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (Nat.card G))

include hE hmono hcyc hζ in

theorem classCount_mem_spanA (s : G) : classCount s ∈ spanA E ζ := by
  set C := Subgroup.zpowers s
  set s' : C := ⟨s, Subgroup.mem_zpowers s⟩
  set δ : C → ℂ := fun c ↦ if c = s' then (Nat.card C : ℂ) else 0
  have hcomm : ∀ a b : C, a * b = b * a := fun a b ↦
    (Subgroup.zpowers_isMulCommutative s).is_comm.comm a b
  have hδ : IsClassFun δ := by
    intro g h
    simp only [δ]
    rw [hcomm h g, mul_inv_cancel_right]
  have hN : (Nat.card C : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hcoef : ∀ ψ : C → ℂ, charInner C δ ψ = ψ s'⁻¹ := by
    intro ψ
    rw [charInner_apply]
    simp only [δ, ite_mul, zero_mul]
    rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ _), ← mul_assoc, inv_mul_cancel₀ hN, one_mul]
  rw [← indFun_zpowers_delta]
  change indFun C.subtype δ ∈ spanA E ζ
  rw [eq_sum_irrChars_of_isClassFun hδ, map_sum]
  refine Submodule.sum_mem _ fun ψ hψ ↦ ?_
  rw [map_smul, hcoef]
  refine smul_mem_spanA ?_ (indFun_mem_spanZ hE hmono (hcyc s) (mem_irrChars.mp hψ).isCharacter)
  have : NeZero (Nat.card G) := ⟨Nat.card_pos.ne'⟩
  refine (mem_irrChars.mp hψ).isCharacter.apply_mem_adjoin _ hζ ?_
  rw [← Subgroup.orderOf_coe]
  exact orderOf_dvd_natCard _

end ClassCount

section Divisible

theorem card_smul_eq_sum_classCount {F : G → ℂ} (hF : IsClassFun F) :
    (Nat.card G : ℂ) • F = ∑ s : G, F s • classCount s := by
  funext g
  simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply, classCount, Finset.mul_sum]
  rw [Finset.sum_comm]
  have h : ∀ t : G, ∑ s : G, F s * (if t⁻¹ * g * t = s then 1 else 0) = F g := by
    intro t
    simp only [mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]
    simpa using hF g t⁻¹
  rw [Finset.sum_congr rfl fun t _ ↦ h t, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Nat.card_eq_fintype_card]

variable {E : Subgroup G → Prop} (hE : ∀ K L : Subgroup G, E K → L ≤ K → E L)
  (hmono : ∀ K : Subgroup G, E K → ∀ χ : K → ℂ, IsIrrCharacter χ →
    ∃ (L : Subgroup K) (μ : L →* ℂˣ), χ = indLin L μ)
  (hcyc : ∀ s : G, E (Subgroup.zpowers s))
  {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (Nat.card G))

include hE hmono hcyc hζ in

theorem mem_spanA_of_dvd {F : G → ℂ} (hF : IsClassFun F)
    (hdiv : ∀ g, ∃ k : ℤ, F g = (Nat.card G : ℂ) * k) : F ∈ spanA E ζ := by
  choose k hk using hdiv
  have hG : (Nat.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hF' : F = ∑ s : G, k s • classCount s := by
    have h := card_smul_eq_sum_classCount hF
    funext g
    have hg := congrFun h g
    simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply] at hg
    simp only [Finset.sum_apply]
    simp only [Pi.smul_apply, zsmul_eq_mul]
    apply mul_left_cancel₀ hG
    rw [hg, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    rw [hk s]
    ring
  rw [hF']
  exact Submodule.sum_mem _ fun s _ ↦ Submodule.smul_mem _ _ (classCount_mem_spanA hE hmono hcyc hζ s)

end Divisible

section Values

variable {E : Subgroup G → Prop} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (Nat.card G))
include hζ

theorem apply_mem_adjoin_of_mem_spanZ {f : G → ℂ} (hf : f ∈ spanZ E) (g : G) :
    f g ∈ Algebra.adjoin ℤ ({ζ} : Set ℂ) := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨K, -, l, rfl⟩ := hx
    exact (IsCharacter.indLin K l).apply_mem_adjoin_card g hζ
  | zero => exact Subalgebra.zero_mem _
  | add x y _ _ hx hy => exact Subalgebra.add_mem _ hx hy
  | smul n x _ hx =>
    rw [Pi.smul_apply, zsmul_eq_mul]
    exact Subalgebra.mul_mem _ (Subalgebra.intCast_mem _ n) hx

theorem apply_mem_adjoin_of_mem_spanA {f : G → ℂ} (hf : f ∈ spanA E ζ) (g : G) :
    f g ∈ Algebra.adjoin ℤ ({ζ} : Set ℂ) := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, g', hg', rfl⟩ := hx
    rw [Pi.smul_apply, smul_eq_mul]
    exact Subalgebra.mul_mem _ ha (apply_mem_adjoin_of_mem_spanZ hζ hg' g)
  | zero => exact Subalgebra.zero_mem _
  | add x y _ _ hx hy => exact Subalgebra.add_mem _ hx hy
  | smul n x _ hx =>
    rw [Pi.smul_apply, zsmul_eq_mul]
    exact Subalgebra.mul_mem _ (Subalgebra.intCast_mem _ n) hx

end Values

section Congruence

def CongrData (ζ : ℂ) (N : ℕ) (s : G) (a : ℤ) (f : G → ℂ) : Prop :=
  ∃ (ι : Type u) (_ : Fintype ι) (c β β' : ι → Algebra.adjoin ℤ ({ζ} : Set ℂ)),
    (∀ i, β i ^ N = β' i ^ N) ∧ f s = ∑ i, (c i : ℂ) * β i ∧ f (s ^ a) = ∑ i, (c i : ℂ) * β' i

variable {ζ : ℂ} {N : ℕ} {s : G} {a : ℤ}

omit [Fintype G] in
theorem congrData_zero : CongrData ζ N s a (0 : G → ℂ) :=
  ⟨PEmpty, inferInstance, PEmpty.elim, PEmpty.elim, PEmpty.elim, fun i ↦ i.elim, by simp, by simp⟩

omit [Fintype G] in
theorem CongrData.add {f g : G → ℂ} (hf : CongrData ζ N s a f) (hg : CongrData ζ N s a g) :
    CongrData ζ N s a (f + g) := by
  obtain ⟨ι, _, c, β, β', hβ, h1, h2⟩ := hf
  obtain ⟨ι', _, c', γ, γ', hγ, h1', h2'⟩ := hg
  refine ⟨ι ⊕ ι', inferInstance, Sum.elim c c', Sum.elim β γ, Sum.elim β' γ', ?_, ?_, ?_⟩
  · rintro (i | i)
    · exact hβ i
    · exact hγ i
  · simp [Fintype.sum_sum_type, h1, h1']
  · simp [Fintype.sum_sum_type, h2, h2']

omit [Fintype G] in
theorem CongrData.smul {f : G → ℂ} (hf : CongrData ζ N s a f) (x : Algebra.adjoin ℤ ({ζ} : Set ℂ)) :
    CongrData ζ N s a ((x : ℂ) • f) := by
  obtain ⟨ι, _, c, β, β', hβ, h1, h2⟩ := hf
  refine ⟨ι, inferInstance, fun i ↦ x * c i, β, β', hβ, ?_, ?_⟩
  · simp [h1, Finset.mul_sum, mul_assoc]
  · simp [h2, Finset.mul_sum, mul_assoc]

omit [Fintype G] in
theorem CongrData.zsmul {f : G → ℂ} (hf : CongrData ζ N s a f) (n : ℤ) : CongrData ζ N s a (n • f) := by
  have := hf.smul (n : Algebra.adjoin ℤ ({ζ} : Set ℂ))
  rwa [show ((n : Algebra.adjoin ℤ ({ζ} : Set ℂ)) : ℂ) = (n : ℂ) by simp, Int.cast_smul_eq_zsmul] at this

theorem IsCharacter.congrData {χ : G → ℂ} (hχ : IsCharacter χ) (hζ : IsPrimitiveRoot ζ (Nat.card G))
    {b : ℤ} (hab : s ^ a * s ^ b = s) (hb : (s ^ b) ^ N = 1) : CongrData ζ N s a χ := by
  set C := Subgroup.zpowers s
  set s' : C := ⟨s, Subgroup.mem_zpowers s⟩
  have : NeZero (Nat.card G) := ⟨Nat.card_pos.ne'⟩
  obtain ⟨m, hm⟩ := (hχ.comp C.subtype).exists_nat
  have hval : ∀ ψ ∈ irrChars C, ∀ x : C, ψ x ∈ Algebra.adjoin ℤ ({ζ} : Set ℂ) := fun ψ hψ x ↦
    (mem_irrChars.mp hψ).isCharacter.apply_mem_adjoin x hζ
      (by rw [← Subgroup.orderOf_coe]; exact orderOf_dvd_natCard _)
  have hsN : s' ^ N = (s' ^ a) ^ N := by
    apply Subtype.ext
    simp only [s', Subgroup.coe_pow, Subgroup.coe_zpow]
    have hc : Commute (s ^ a) (s ^ b) := (Commute.refl s).zpow_zpow a b
    rw [← hab, hc.mul_pow, hb, mul_one, hab]
  refine ⟨irrChars C, inferInstance, fun ψ ↦ (m ψ : Algebra.adjoin ℤ ({ζ} : Set ℂ)),
    fun ψ ↦ ⟨ψ.1 s', hval ψ.1 ψ.2 s'⟩, fun ψ ↦ ⟨ψ.1 (s' ^ a), hval ψ.1 ψ.2 _⟩, ?_, ?_, ?_⟩
  · intro ψ
    obtain ⟨l, hl⟩ := (mem_irrChars.mp ψ.2).exists_monoidHom
    apply Subtype.ext
    simp only [SubmonoidClass.coe_pow]
    rw [hl, hl, ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, ← map_pow, ← map_pow, hsN]
  · have h := congrFun hm s'
    simp only [Function.comp_apply, Subgroup.coe_subtype, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul] at h
    change χ (s' : G) = _
    rw [h, ← Finset.sum_coe_sort]
    simp
  · have h := congrFun hm (s' ^ a)
    simp only [Function.comp_apply, Subgroup.coe_subtype, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, Subgroup.coe_zpow] at h
    change χ ((s' : G) ^ a) = _
    rw [h, ← Finset.sum_coe_sort]
    simp

variable {E : Subgroup G → Prop}

theorem congrData_of_mem_spanZ (hζ : IsPrimitiveRoot ζ (Nat.card G)) {b : ℤ} (hab : s ^ a * s ^ b = s)
    (hb : (s ^ b) ^ N = 1) {f : G → ℂ} (hf : f ∈ spanZ E) : CongrData ζ N s a f := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨K, -, l, rfl⟩ := hx
    exact (IsCharacter.indLin K l).congrData hζ hab hb
  | zero => exact congrData_zero
  | add x y _ _ hx hy => exact hx.add hy
  | smul n x _ hx => exact hx.zsmul n

theorem congrData_of_mem_spanA (hζ : IsPrimitiveRoot ζ (Nat.card G)) {b : ℤ} (hab : s ^ a * s ^ b = s)
    (hb : (s ^ b) ^ N = 1) {f : G → ℂ} (hf : f ∈ spanA E ζ) : CongrData ζ N s a f := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨x', hx', g, hg, rfl⟩ := hx
    exact (congrData_of_mem_spanZ hζ hab hb hg).smul ⟨x', hx'⟩
  | zero => exact congrData_zero
  | add x y _ _ hx hy => exact hx.add hy
  | smul n x _ hx => exact hx.zsmul n

omit [Fintype G] in

theorem CongrData.exists_pow_eq {p k : ℕ} (hp : p.Prime) {f : G → ℂ} (hf : CongrData ζ (p ^ k) s a f) :
    ∃ r ∈ Algebra.adjoin ℤ ({ζ} : Set ℂ), f s ^ p ^ k = f (s ^ a) ^ p ^ k + p * r := by
  obtain ⟨ι, _, c, β, β', hβ, h1, h2⟩ := hf
  obtain ⟨r1, hr1⟩ := exists_sum_pow_prime_pow_eq hp Finset.univ (fun i ↦ c i * β i) k
  obtain ⟨r2, hr2⟩ := exists_sum_pow_prime_pow_eq hp Finset.univ (fun i ↦ c i * β' i) k
  have heq : ∑ i, (c i * β i) ^ p ^ k = ∑ i, (c i * β' i) ^ p ^ k :=
    Finset.sum_congr rfl fun i _ ↦ by rw [mul_pow, mul_pow, hβ i]
  refine ⟨(r1 - r2 : Algebra.adjoin ℤ ({ζ} : Set ℂ)), (r1 - r2).2, ?_⟩
  have hx : f s = ((∑ i, c i * β i : Algebra.adjoin ℤ ({ζ} : Set ℂ)) : ℂ) := by
    rw [h1]
    push_cast
    rfl
  have hy : f (s ^ a) = ((∑ i, c i * β' i : Algebra.adjoin ℤ ({ζ} : Set ℂ)) : ℂ) := by
    rw [h2]
    push_cast
    rfl
  rw [hx, hy]
  have key : (∑ i, c i * β i) ^ p ^ k = (∑ i, c i * β' i) ^ p ^ k + p * (r1 - r2) := by
    rw [hr1, hr2, heq]
    ring
  have := congrArg (fun z : Algebra.adjoin ℤ ({ζ} : Set ℂ) ↦ (z : ℂ)) key
  simpa using this

theorem int_modEq_of_mem_spanA (hζ : IsPrimitiveRoot ζ (Nat.card G)) {p k : ℕ} (hp : p.Prime) {b : ℤ}
    (hab : s ^ a * s ^ b = s) (hb : (s ^ b) ^ p ^ k = 1) {f : G → ℂ} (hf : f ∈ spanA E ζ) {u v : ℤ}
    (hu : f s = u) (hv : f (s ^ a) = v) : (u : ZMod p) = v := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨r, hr, hrr⟩ := (congrData_of_mem_spanA hζ hab hb hf).exists_pow_eq hp
  rw [hu, hv] at hrr
  have hint := hζ.isIntegral Nat.card_pos
  obtain ⟨z, -, hz⟩ := exists_int_of_mul_eq_int hint hr (d := p) (k := u ^ p ^ k - v ^ p ^ k)
    (Int.natCast_ne_zero.mpr hp.ne_zero) (by push_cast; rw [hrr]; ring)
  have hmod : ((u ^ p ^ k : ℤ) : ZMod p) = ((v ^ p ^ k : ℤ) : ZMod p) := by
    rw [← sub_eq_zero, ← Int.cast_sub, ← hz]
    push_cast
    simp
  push_cast at hmod
  rwa [ZMod.pow_card_pow, ZMod.pow_card_pow] at hmod

end Congruence

end GroundTheory.LocalField
