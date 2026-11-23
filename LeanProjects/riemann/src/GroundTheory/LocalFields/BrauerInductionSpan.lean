import Mathlib
import GroundTheory.LocalFields.BrauerInductionIntegral
import GroundTheory.LocalFields.BrauerInductionElementary

noncomputable section

namespace GroundTheory.LocalField

open Module Representation

open scoped Classical

section OneDim

variable {K : Type*} [Group K]

theorem isCharacter_monoidHom (l : K →* ℂˣ) : IsCharacter (fun k ↦ (l k : ℂ)) := by
  let ρ : Representation ℂ K ℂ :=
    { toFun := fun k ↦ (l k : ℂ) • LinearMap.id
      map_one' := by simp; rfl
      map_mul' := fun k k' ↦ by
        ext
        simp [mul_comm] }
  refine ⟨ℂ, inferInstance, inferInstance, inferInstance, ρ, ?_⟩
  funext k
  simp [Representation.character, ρ, LinearMap.trace_id]

end OneDim

variable {G : Type*} [Group G] [Fintype G]

def indLin (K : Subgroup G) (l : K →* ℂˣ) : G → ℂ := indFun K.subtype (fun k ↦ (l k : ℂ))

theorem IsCharacter.indLin (K : Subgroup G) (l : K →* ℂˣ) : IsCharacter (indLin K l) :=
  (isCharacter_monoidHom l).indFun K.subtype

section Transport

variable {H H' : Type*} [Group H] [Fintype H] [Group H'] [Fintype H']

theorem indFun_comp_toMonoidHom (φ : H →* G) (e : H' ≃* H) (ψ : H → ℂ) :
    indFun (φ.comp e.toMonoidHom) (ψ ∘ e) = indFun φ ψ := by
  classical
  funext s
  simp only [indFun_apply]
  rw [Nat.card_congr e.toEquiv]
  congr 1
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  exact Fintype.sum_equiv e.toEquiv _ _ fun h' ↦ by
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Function.comp_apply,
      MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv]
    exact if_congr Iff.rfl rfl rfl

theorem indFun_subtype_indLin (K : Subgroup G) (L : Subgroup K) (μ : L →* ℂˣ) :
    indFun K.subtype (indLin L μ) = indLin (L.map K.subtype)
      (μ.comp (L.equivMapOfInjective K.subtype K.subtype_injective).symm.toMonoidHom) := by
  set e := L.equivMapOfInjective K.subtype K.subtype_injective
  rw [indLin, indFun_indFun, indLin, ← indFun_comp_toMonoidHom _ e]
  congr 1
  ext l
  simp [e]

end Transport

section Spans

variable (E : Subgroup G → Prop)

def monomialSet : Set (G → ℂ) := {f | ∃ K : Subgroup G, E K ∧ ∃ l : K →* ℂˣ, f = indLin K l}

def spanZ : Submodule ℤ (G → ℂ) := Submodule.span ℤ (monomialSet E)

def spanA (ζ : ℂ) : Submodule ℤ (G → ℂ) :=
  Submodule.span ℤ {f | ∃ a ∈ Algebra.adjoin ℤ ({ζ} : Set ℂ), ∃ g ∈ spanZ E, f = a • g}

variable {E}

theorem indLin_mem_spanZ {K : Subgroup G} (hK : E K) (l : K →* ℂˣ) : indLin K l ∈ spanZ E :=
  Submodule.subset_span ⟨K, hK, l, rfl⟩

theorem spanZ_le_spanA (ζ : ℂ) : spanZ E ≤ spanA E ζ := fun g hg ↦
  Submodule.subset_span ⟨1, Subalgebra.one_mem _, g, hg, (one_smul ℂ g).symm⟩

theorem smul_mem_spanA {ζ : ℂ} {a : ℂ} (ha : a ∈ Algebra.adjoin ℤ ({ζ} : Set ℂ)) {g : G → ℂ}
    (hg : g ∈ spanZ E) : a • g ∈ spanA E ζ :=
  Submodule.subset_span ⟨a, ha, g, hg, rfl⟩

theorem spanZ_mono {E' : Subgroup G → Prop} (h : ∀ K, E K → E' K) : spanZ E ≤ spanZ E' :=
  Submodule.span_mono fun _ ⟨K, hK, l, hf⟩ ↦ ⟨K, h K hK, l, hf⟩

theorem smul_mem_spanA_of_mem {ζ : ℂ} {a : ℂ} (ha : a ∈ Algebra.adjoin ℤ ({ζ} : Set ℂ)) {f : G → ℂ}
    (hf : f ∈ spanA E ζ) : a • f ∈ spanA E ζ := by
  induction hf using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨b, hb, g, hg, rfl⟩ := hy
    rw [smul_smul]
    exact smul_mem_spanA (Subalgebra.mul_mem _ ha hb) hg
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
  | smul n x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ n hx

theorem isClassFun_of_mem_spanZ {f : G → ℂ} (hf : f ∈ spanZ E) : IsClassFun f := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨K, -, l, rfl⟩ := hx
    exact isClassFun_indFun _ _
  | zero => intro g h; rfl
  | add x y _ _ hx hy => intro g h; simp [hx g h, hy g h]
  | smul n x _ hx => intro g h; simp [hx g h]

theorem isClassFun_of_mem_spanA {ζ : ℂ} {f : G → ℂ} (hf : f ∈ spanA E ζ) : IsClassFun f := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, -, g, hg, rfl⟩ := hx
    intro s t
    simp [isClassFun_of_mem_spanZ hg s t]
  | zero => intro g h; rfl
  | add x y _ _ hx hy => intro g h; simp [hx g h, hy g h]
  | smul n x _ hx => intro g h; simp [hx g h]

theorem exists_int_charInner_of_mem_spanZ {f : G → ℂ} (hf : f ∈ spanZ E) {ψ : G → ℂ}
    (hψ : IsIrrCharacter ψ) : ∃ k : ℤ, charInner G f ψ = k := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨K, -, l, rfl⟩ := hx
    obtain ⟨n, hn⟩ := (IsCharacter.indLin K l).exists_nat_charInner hψ.isCharacter
    exact ⟨n, by rw [hn]; simp⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by rw [map_add, LinearMap.add_apply, ha, hb]; push_cast; ring⟩
  | smul n x _ hx =>
    obtain ⟨a, ha⟩ := hx
    refine ⟨n * a, ?_⟩
    rw [← Int.cast_smul_eq_zsmul ℂ, map_smul, LinearMap.smul_apply, ha, smul_eq_mul]
    push_cast
    ring

end Spans

section Mono

variable {E : Subgroup G → Prop} (hE : ∀ K L : Subgroup G, E K → L ≤ K → E L)
  (hmono : ∀ K : Subgroup G, E K → ∀ χ : K → ℂ, IsIrrCharacter χ →
    ∃ (L : Subgroup K) (μ : L →* ℂˣ), χ = indLin L μ)
include hE hmono

theorem indFun_mem_spanZ {K : Subgroup G} (hK : E K) {χ : K → ℂ} (hχ : IsCharacter χ) :
    indFun K.subtype χ ∈ spanZ E := by
  classical
  obtain ⟨m, hm⟩ := hχ.exists_nat
  rw [hm, map_sum]
  refine Submodule.sum_mem _ fun ψ hψ ↦ ?_
  obtain ⟨L, μ, hLμ⟩ := hmono K hK ψ (mem_irrChars.mp hψ)
  rw [map_smul, Nat.cast_smul_eq_nsmul ℂ, hLμ, indFun_subtype_indLin]
  exact Submodule.smul_of_tower_mem _ _
    (indLin_mem_spanZ (hE K _ hK (Subgroup.map_subtype_le L)) _)

theorem mul_mem_spanZ {χ : G → ℂ} (hχ : IsCharacter χ) {f : G → ℂ} (hf : f ∈ spanZ E) :
    χ * f ∈ spanZ E := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨K, hK, l, rfl⟩ := hx
    rw [mul_comm, indLin, ← indFun_mul_comp _ _ hχ.isClassFun]
    exact indFun_mem_spanZ hE hmono hK ((isCharacter_monoidHom l).mul (hχ.comp K.subtype))
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
  | smul n x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ n hx

theorem mul_mem_spanZ_of_mem {f g : G → ℂ} (hf : f ∈ spanZ E) (hg : g ∈ spanZ E) :
    f * g ∈ spanZ E := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨K, hK, l, rfl⟩ := hx
    exact mul_mem_spanZ hE hmono (IsCharacter.indLin K l) hg
  | zero => simp
  | add x y _ _ hx hy => rw [add_mul]; exact Submodule.add_mem _ hx hy
  | smul n x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ n hx

theorem mul_mem_spanA_of_mem_spanZ {ζ : ℂ} {f g : G → ℂ} (hf : f ∈ spanA E ζ) (hg : g ∈ spanZ E) :
    f * g ∈ spanA E ζ := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, g', hg', rfl⟩ := hx
    rw [smul_mul_assoc]
    exact smul_mem_spanA ha (mul_mem_spanZ_of_mem hE hmono hg' hg)
  | zero => simp
  | add x y _ _ hx hy => rw [add_mul]; exact Submodule.add_mem _ hx hy
  | smul n x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ n hx

theorem mul_mem_spanA {ζ : ℂ} {f g : G → ℂ} (hf : f ∈ spanA E ζ) (hg : g ∈ spanA E ζ) :
    f * g ∈ spanA E ζ := by
  induction hg using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, g', hg', rfl⟩ := hx
    rw [mul_smul_comm]
    exact smul_mem_spanA_of_mem ha (mul_mem_spanA_of_mem_spanZ hE hmono hf hg')
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
  | smul n x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ n hx

theorem pow_mem_spanA {ζ : ℂ} {f : G → ℂ} (hf : f ∈ spanA E ζ) {M : ℕ} (hM : M ≠ 0) :
    f ^ M ∈ spanA E ζ := by
  induction M with
  | zero => exact absurd rfl hM
  | succ M ih =>
    rcases Nat.eq_zero_or_pos M with rfl | hM'
    · simpa using hf
    · rw [pow_succ]
      exact mul_mem_spanA hE hmono (ih hM'.ne') hf

end Mono

section Descent

variable {E : Subgroup G → Prop}

theorem mem_spanZ_of_mem_spanA {ζ : ℂ} (hζ : IsIntegral ℤ ζ) {f : G → ℂ} (hf : f ∈ spanA E ζ)
    (hint : ∀ ψ ∈ irrChars G, ∃ k : ℤ, charInner G f ψ = k) : f ∈ spanZ E := by
  obtain ⟨π, hπ⟩ := exists_retraction_adjoin hζ
  obtain ⟨n, c, x, hx⟩ := (Submodule.mem_span_set').mp hf
  have hS : ∀ i, ∃ a : Algebra.adjoin ℤ ({ζ} : Set ℂ), ∃ g ∈ spanZ E,
      (x i : G → ℂ) = (a : ℂ) • g := fun i ↦ by
    obtain ⟨a, ha, g, hg, h⟩ := (x i).2
    exact ⟨⟨a, ha⟩, g, hg, h⟩
  choose a g hg hxag using hS
  set f' : G → ℂ := ∑ i, (c i * π (a i)) • g i with hf'def
  have hf' : f' ∈ spanZ E := Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ (hg i)
  have hfeq : f = ∑ i, c i • ((a i : ℂ) • g i) := by
    rw [← hx]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [hxag i]
  suffices f = f' by rw [this]; exact hf'
  apply eq_of_isClassFun_of_charInner (isClassFun_of_mem_spanA hf) (isClassFun_of_mem_spanZ hf')
  intro ψ hψ
  obtain ⟨k, hk⟩ := hint ψ hψ
  have hn : ∀ i, ∃ m : ℤ, charInner G (g i) ψ = m := fun i ↦
    exists_int_charInner_of_mem_spanZ (hg i) (mem_irrChars.mp hψ)
  choose m hm using hn
  have h1 : charInner G f ψ = ∑ i, ((c i * m i : ℤ) : ℂ) * (a i : ℂ) := by
    rw [hfeq, map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← Int.cast_smul_eq_zsmul ℂ, map_smul, map_smul, LinearMap.smul_apply, LinearMap.smul_apply, hm i,
      smul_eq_mul, smul_eq_mul]
    push_cast
    ring
  have hA : (∑ i, (c i * m i) • a i) = k • (1 : Algebra.adjoin ℤ ({ζ} : Set ℂ)) := by
    apply Subtype.ext
    simp only [AddSubmonoidClass.coe_finsetSum, zsmul_eq_mul, mul_one]
    push_cast
    rw [← hk, h1]
    push_cast
    rfl
  have hπA := congrArg π hA
  rw [map_sum, map_zsmul, hπ, smul_eq_mul, mul_one] at hπA
  simp only [map_zsmul, smul_eq_mul] at hπA
  rw [hk, hf'def, map_sum, LinearMap.sum_apply]
  rw [← hπA]
  push_cast
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← Int.cast_smul_eq_zsmul ℂ, map_smul, LinearMap.smul_apply, hm i, smul_eq_mul]
  push_cast
  ring

end Descent

end GroundTheory.LocalField
