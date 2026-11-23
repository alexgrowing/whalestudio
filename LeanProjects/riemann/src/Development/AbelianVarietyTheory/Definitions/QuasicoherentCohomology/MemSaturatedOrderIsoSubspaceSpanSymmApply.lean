import Mathlib

open scoped nonZeroDivisors Pointwise

namespace GlobalTheory

section Basic

variable {R : Type*} [CommRing R] {M M' : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup M'] [Module R M']

def saturation (N : Submodule R M) : Submodule R M :=
  (Submodule.torsion R (M ⧸ N)).comap N.mkQ

def IsSaturatedSubmodule (N : Submodule R M) : Prop :=
  saturation N = N

theorem saturation_eq_comap_torsion (N : Submodule R M) :
    saturation N = (Submodule.torsion R (M ⧸ N)).comap N.mkQ := rfl

theorem mem_saturation_iff' {N : Submodule R M} {x : M} :
    x ∈ saturation N ↔ ∃ a ∈ R⁰, a • x ∈ N := by
  change N.mkQ x ∈ Submodule.torsion R (M ⧸ N) ↔ _
  rw [Submodule.mem_torsion_iff]
  constructor
  · rintro ⟨⟨a, ha⟩, h⟩
    refine ⟨a, ha, ?_⟩
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul]
    exact h
  · rintro ⟨a, ha, h⟩
    refine ⟨⟨a, ha⟩, ?_⟩
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul] at h
    exact h

theorem mem_saturation_iff [IsDomain R] {N : Submodule R M} {x : M} :
    x ∈ saturation N ↔ ∃ a : R, a ≠ 0 ∧ a • x ∈ N := by
  rw [mem_saturation_iff']
  simp only [mem_nonZeroDivisors_iff_ne_zero]

theorem coe_saturation [IsDomain R] (N : Submodule R M) :
    (saturation N : Set M) = {x | ∃ a : R, a ≠ 0 ∧ a • x ∈ N} := by
  ext x
  exact mem_saturation_iff

theorem mem_saturation_of_smul_mem [IsDomain R] {N : Submodule R M} {a : R} {x : M} (ha : a ≠ 0)
    (hx : a • x ∈ N) : x ∈ saturation N := mem_saturation_iff.2 ⟨a, ha, hx⟩

theorem le_saturation (N : Submodule R M) : N ≤ saturation N := fun x hx => mem_saturation_iff'.2 ⟨1, one_mem _, by rwa [one_smul]⟩

@[gcongr]
theorem saturation_mono {N N' : Submodule R M} (h : N ≤ N') : saturation N ≤ saturation N' := by
  intro x hx
  obtain ⟨a, ha, hax⟩ := mem_saturation_iff'.1 hx
  exact mem_saturation_iff'.2 ⟨a, ha, h hax⟩

@[simp]
theorem saturation_saturation (N : Submodule R M) : saturation (saturation N) = saturation N := by
  refine le_antisymm (fun x hx => ?_) (le_saturation _)
  obtain ⟨a, ha, hax⟩ := mem_saturation_iff'.1 hx
  obtain ⟨b, hb, hbx⟩ := mem_saturation_iff'.1 hax
  refine mem_saturation_iff'.2 ⟨b * a, mul_mem hb ha, ?_⟩
  rwa [mul_smul]

variable (R M) in

def saturationClosure : ClosureOperator (Submodule R M) where
  toFun := saturation
  monotone' _ _ := saturation_mono
  le_closure' := le_saturation
  idempotent' := saturation_saturation
  IsClosed := IsSaturatedSubmodule
  isClosed_iff := Iff.rfl

@[simp]
theorem saturationClosure_apply (N : Submodule R M) :
    saturationClosure R M N = saturation N := rfl

@[simp]
theorem saturationClosure_isClosed_iff (N : Submodule R M) :
    (saturationClosure R M).IsClosed N ↔ IsSaturatedSubmodule N := by rfl

theorem IsSaturatedSubmodule.saturation_eq {N : Submodule R M} (h : IsSaturatedSubmodule N) :
    saturation N = N := h

theorem isSaturatedSubmodule_iff_le {N : Submodule R M} :
    IsSaturatedSubmodule N ↔ saturation N ≤ N := ⟨fun h => h.saturation_eq.le, fun h => le_antisymm h (le_saturation N)⟩

theorem isSaturatedSubmodule_iff' {N : Submodule R M} :
    IsSaturatedSubmodule N ↔ ∀ a ∈ R⁰, ∀ x : M, a • x ∈ N → x ∈ N := by
  rw [isSaturatedSubmodule_iff_le]
  constructor
  · intro h a ha x hx
    exact h (mem_saturation_iff'.2 ⟨a, ha, hx⟩)
  · intro h x hx
    obtain ⟨a, ha, hax⟩ := mem_saturation_iff'.1 hx
    exact h a ha x hax

theorem isSaturatedSubmodule_iff [IsDomain R] {N : Submodule R M} :
    IsSaturatedSubmodule N ↔ ∀ a : R, a ≠ 0 → ∀ x : M, a • x ∈ N → x ∈ N := by
  rw [isSaturatedSubmodule_iff']
  simp only [mem_nonZeroDivisors_iff_ne_zero]

theorem IsSaturatedSubmodule.mem_of_smul_mem [IsDomain R] {N : Submodule R M}
    (h : IsSaturatedSubmodule N) {a : R} (ha : a ≠ 0) {x : M} (hx : a • x ∈ N) : x ∈ N := isSaturatedSubmodule_iff.1 h a ha x hx

theorem IsSaturatedSubmodule.smul_mem_iff [IsDomain R] {N : Submodule R M}
    (h : IsSaturatedSubmodule N) {a : R} (ha : a ≠ 0) {x : M} : a • x ∈ N ↔ x ∈ N := ⟨h.mem_of_smul_mem ha, fun hx => N.smul_mem a hx⟩

theorem isSaturatedSubmodule_iff_torsion_eq_bot {N : Submodule R M} :
    IsSaturatedSubmodule N ↔ Submodule.torsion R (M ⧸ N) = ⊥ := by
  rw [isSaturatedSubmodule_iff_le, Submodule.eq_bot_iff]
  constructor
  · intro h y hy
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective N y
    exact (Submodule.Quotient.mk_eq_zero N).2 (h (show x ∈ saturation N from hy))
  · intro h x hx
    exact (Submodule.Quotient.mk_eq_zero N).1 (h (N.mkQ x) hx)

theorem isSaturatedSubmodule_iff_isTorsionFree [IsDomain R] {N : Submodule R M} :
    IsSaturatedSubmodule N ↔ Module.IsTorsionFree R (M ⧸ N) := by
  rw [isSaturatedSubmodule_iff_torsion_eq_bot, Submodule.isTorsionFree_iff_torsion_eq_bot]

theorem IsSaturatedSubmodule.isTorsionFree_quotient [IsDomain R] {N : Submodule R M}
    (h : IsSaturatedSubmodule N) : Module.IsTorsionFree R (M ⧸ N) := isSaturatedSubmodule_iff_isTorsionFree.1 h

theorem isSaturatedSubmodule_saturation (N : Submodule R M) :
    IsSaturatedSubmodule (saturation N) := by
  rw [isSaturatedSubmodule_iff_le, saturation_saturation]

instance isTorsionFree_quotient_saturation [IsDomain R] (N : Submodule R M) :
    Module.IsTorsionFree R (M ⧸ saturation N) :=
  (isSaturatedSubmodule_saturation N).isTorsionFree_quotient

theorem IsSaturatedSubmodule.saturation_le_iff {N P : Submodule R M}
    (h : IsSaturatedSubmodule P) : saturation N ≤ P ↔ N ≤ P := ⟨fun hN => (le_saturation N).trans hN, fun hN => (saturation_mono hN).trans h.saturation_eq.le⟩

theorem IsSaturatedSubmodule.eq_saturation {N P : Submodule R M}
    (h : IsSaturatedSubmodule P) (h₁ : N ≤ P) (h₂ : P ≤ saturation N) : P = saturation N := le_antisymm h₂ (h.saturation_le_iff.2 h₁)

theorem saturation_eq_of_le_of_le {N P : Submodule R M} (h₁ : N ≤ P) (h₂ : P ≤ saturation N) :
    saturation P = saturation N := le_antisymm ((saturation_mono h₂).trans (saturation_saturation N).le) (saturation_mono h₁)

@[simp]
theorem saturation_bot : saturation (⊥ : Submodule R M) = Submodule.torsion R M := by
  ext x
  rw [mem_saturation_iff', Submodule.mem_torsion_iff]
  simp only [Submodule.mem_bot]
  exact ⟨fun ⟨a, ha, h⟩ => ⟨⟨a, ha⟩, h⟩, fun ⟨a, h⟩ => ⟨a, a.2, h⟩⟩

@[simp]
theorem saturation_top : saturation (⊤ : Submodule R M) = ⊤ := top_unique (le_saturation _)

theorem isSaturatedSubmodule_top : IsSaturatedSubmodule (⊤ : Submodule R M) := by
  rw [isSaturatedSubmodule_iff_le]
  exact le_top

theorem isSaturatedSubmodule_bot_iff [IsDomain R] :
    IsSaturatedSubmodule (⊥ : Submodule R M) ↔ Module.IsTorsionFree R M := by
  unfold IsSaturatedSubmodule
  rw [saturation_bot, Submodule.isTorsionFree_iff_torsion_eq_bot]

theorem isSaturatedSubmodule_bot [IsDomain R] [Module.IsTorsionFree R M] :
    IsSaturatedSubmodule (⊥ : Submodule R M) := isSaturatedSubmodule_bot_iff.2 ‹_›

theorem torsion_le_saturation (N : Submodule R M) : Submodule.torsion R M ≤ saturation N := by
  rw [← saturation_bot]
  exact saturation_mono bot_le

theorem saturation_eq_top_iff {N : Submodule R M} :
    saturation N = ⊤ ↔ Module.IsTorsion R (M ⧸ N) := by
  rw [eq_top_iff]
  constructor
  · intro h y
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective N y
    exact h (Submodule.mem_top (x := x))
  · intro h x _
    exact @h (N.mkQ x)

theorem saturation_inf (N P : Submodule R M) :
    saturation (N ⊓ P) = saturation N ⊓ saturation P := by
  refine le_antisymm (le_inf (saturation_mono inf_le_left) (saturation_mono inf_le_right)) ?_
  intro x hx
  obtain ⟨hN, hP⟩ := Submodule.mem_inf.1 hx
  obtain ⟨a, ha, hax⟩ := mem_saturation_iff'.1 hN
  obtain ⟨b, hb, hbx⟩ := mem_saturation_iff'.1 hP
  refine mem_saturation_iff'.2 ⟨a * b, mul_mem ha hb, Submodule.mem_inf.2 ⟨?_, ?_⟩⟩
  · rw [mul_comm, mul_smul]
    exact N.smul_mem b hax
  · rw [mul_smul]
    exact P.smul_mem a hbx

theorem saturation_sup_saturation (N P : Submodule R M) :
    saturation (saturation N ⊔ saturation P) = saturation (N ⊔ P) := by
  refine le_antisymm ?_ (saturation_mono (sup_le_sup (le_saturation N) (le_saturation P)))
  calc saturation (saturation N ⊔ saturation P) ≤ saturation (saturation (N ⊔ P)) :=
        saturation_mono (sup_le (saturation_mono le_sup_left) (saturation_mono le_sup_right))
    _ = saturation (N ⊔ P) := saturation_saturation _

theorem IsSaturatedSubmodule.inf {N P : Submodule R M} (hN : IsSaturatedSubmodule N)
    (hP : IsSaturatedSubmodule P) : IsSaturatedSubmodule (N ⊓ P) := by
  unfold IsSaturatedSubmodule
  rw [saturation_inf, hN.saturation_eq, hP.saturation_eq]

theorem isSaturatedSubmodule_iInf {ι : Sort*} {N : ι → Submodule R M}
    (h : ∀ i, IsSaturatedSubmodule (N i)) : IsSaturatedSubmodule (⨅ i, N i) := by
  rw [isSaturatedSubmodule_iff_le]
  intro x hx
  rw [Submodule.mem_iInf]
  intro i
  exact (h i).saturation_eq.le (saturation_mono (iInf_le N i) hx)

theorem saturation_comap (f : M →ₗ[R] M') (N : Submodule R M') :
    saturation (N.comap f) = (saturation N).comap f := by
  ext x
  simp only [Submodule.mem_comap, mem_saturation_iff', map_smul]

theorem IsSaturatedSubmodule.comap {N : Submodule R M'} (h : IsSaturatedSubmodule N)
    (f : M →ₗ[R] M') : IsSaturatedSubmodule (N.comap f) := by
  unfold IsSaturatedSubmodule
  rw [saturation_comap, h.saturation_eq]

theorem isSaturatedSubmodule_ker [IsDomain R] [Module.IsTorsionFree R M'] (f : M →ₗ[R] M') :
    IsSaturatedSubmodule (LinearMap.ker f) := by
  rw [isSaturatedSubmodule_iff]
  intro a ha x hx
  rw [LinearMap.mem_ker] at hx ⊢
  rw [map_smul] at hx
  exact (smul_eq_zero_iff_right ha).1 hx

theorem map_saturation_le (f : M →ₗ[R] M') (N : Submodule R M) :
    (saturation N).map f ≤ saturation (N.map f) := by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨a, ha, hax⟩ := mem_saturation_iff'.1 hx
  refine mem_saturation_iff'.2 ⟨a, ha, ?_⟩
  rw [← map_smul]
  exact Submodule.mem_map_of_mem hax

theorem map_saturation_of_injective {f : M →ₗ[R] M'} (hf : Function.Injective f)
    (N : Submodule R M) :
    (saturation N).map f = LinearMap.range f ⊓ saturation (N.map f) := by
  refine le_antisymm (le_inf LinearMap.map_le_range (map_saturation_le f N)) ?_
  intro y hy
  obtain ⟨hr, hs⟩ := Submodule.mem_inf.1 hy
  obtain ⟨x, rfl⟩ := LinearMap.mem_range.1 hr
  obtain ⟨a, ha, hmem⟩ := mem_saturation_iff'.1 hs
  obtain ⟨n, hn, hfn⟩ := Submodule.mem_map.1 hmem
  refine Submodule.mem_map_of_mem (mem_saturation_iff'.2 ⟨a, ha, ?_⟩)
  rw [← map_smul] at hfn
  rw [← hf hfn]
  exact hn

theorem map_saturation_equiv (e : M ≃ₗ[R] M') (N : Submodule R M) :
    (saturation N).map (e : M →ₗ[R] M') = saturation (N.map (e : M →ₗ[R] M')) := by
  rw [map_saturation_of_injective e.injective, LinearEquiv.range, top_inf_eq]

theorem isSaturatedSubmodule_map_equiv_iff (e : M ≃ₗ[R] M') {N : Submodule R M} :
    IsSaturatedSubmodule (N.map (e : M →ₗ[R] M')) ↔ IsSaturatedSubmodule N := by
  unfold IsSaturatedSubmodule
  rw [← map_saturation_equiv]
  exact (Submodule.map_injective_of_injective e.injective).eq_iff

theorem isSaturatedSubmodule_comap_iff_of_surjective {f : M →ₗ[R] M'}
    (hf : Function.Surjective f) {N : Submodule R M'} :
    IsSaturatedSubmodule (N.comap f) ↔ IsSaturatedSubmodule N := by
  unfold IsSaturatedSubmodule
  rw [saturation_comap]
  exact (Submodule.comap_injective_of_surjective hf).eq_iff

theorem IsSaturatedSubmodule.map_subtype {P : Submodule R M} {N : Submodule R P}
    (hN : IsSaturatedSubmodule N) (hP : IsSaturatedSubmodule P) :
    IsSaturatedSubmodule (N.map P.subtype) := by
  rw [isSaturatedSubmodule_iff'] at hN
  rw [isSaturatedSubmodule_iff'] at hP
  rw [isSaturatedSubmodule_iff']
  intro a ha x hx
  obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.1 hx
  have haxP : a • x ∈ P := by
    rw [← hyx]
    exact y.2
  have hxP : x ∈ P := hP a ha x haxP
  have hy' : a • (⟨x, hxP⟩ : P) = y := Subtype.ext (by simpa using hyx.symm)
  refine Submodule.mem_map.2 ⟨⟨x, hxP⟩, hN a ha _ ?_, rfl⟩
  rw [hy']
  exact hy

theorem isSaturatedSubmodule_of_isCompl [IsDomain R] [Module.IsTorsionFree R M]
    {N P : Submodule R M} (h : IsCompl N P) : IsSaturatedSubmodule N := by
  rw [isSaturatedSubmodule_iff]
  intro a ha x hx
  have hxs : x ∈ N ⊔ P := by
    rw [h.sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨n, hn, p, hp, rfl⟩ := Submodule.mem_sup.1 hxs
  have hap : a • p ∈ N := by
    have e : a • p = a • (n + p) - a • n := by rw [smul_add, add_sub_cancel_left]
    rw [e]
    exact N.sub_mem hx (N.smul_mem a hn)
  have h0 : a • p ∈ N ⊓ P := Submodule.mem_inf.2 ⟨hap, P.smul_mem a hp⟩
  rw [h.inf_eq_bot, Submodule.mem_bot] at h0
  rw [(smul_eq_zero_iff_right ha).1 h0, add_zero]
  exact hn

theorem IsSaturatedSubmodule.inf_smul_top [IsDomain R] {N : Submodule R M}
    (h : IsSaturatedSubmodule N) {a : R} (ha : a ≠ 0) :
    N ⊓ a • (⊤ : Submodule R M) = a • N := by
  ext x
  rw [Submodule.mem_inf, Submodule.mem_smul_pointwise_iff_exists,
    Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨hx, y, -, rfl⟩
    exact ⟨y, h.mem_of_smul_mem ha hx, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨N.smul_mem a hy, y, Submodule.mem_top, rfl⟩

theorem saturation_smul [IsDomain R] (N : Submodule R M) {a : R} (ha : a ≠ 0) :
    saturation (a • N) = saturation N := by
  apply le_antisymm
  · apply saturation_mono
    intro x hx
    obtain ⟨y, hy, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx
    exact N.smul_mem a hy
  · refine (isSaturatedSubmodule_saturation (a • N)).saturation_le_iff.2 fun x hx => ?_
    exact mem_saturation_of_smul_mem ha (Submodule.smul_mem_pointwise_smul x a N hx)

theorem isTorsion_saturation_quotient (N : Submodule R M) :
    Module.IsTorsion R (saturation N ⧸ N.submoduleOf (saturation N)) := by
  intro y
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ y
  obtain ⟨a, ha, hax⟩ := mem_saturation_iff'.1 x.2
  refine ⟨⟨a, ha⟩, ?_⟩
  show a • (N.submoduleOf (saturation N)).mkQ x = 0
  rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact hax

theorem isSaturatedSubmodule_int_iff {A : Type*} [AddCommGroup A] (N : Submodule ℤ A) :
    IsSaturatedSubmodule N ↔ N.toAddSubgroup.NSMulSaturated := by
  rw [isSaturatedSubmodule_iff, AddSubgroup.saturated_iff_zsmul]
  constructor
  · intro h n g hg
    by_cases hn : n = 0
    · exact Or.inl hn
    · exact Or.inr (h n hn g hg)
  · intro h a ha x hx
    exact (h a x hx).resolve_left ha

theorem isSaturatedSubmodule_of_field {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (W : Submodule K V) : IsSaturatedSubmodule W := by
  rw [isSaturatedSubmodule_iff]
  intro a ha x hx
  have hx' := W.smul_mem a⁻¹ hx
  rwa [smul_smul, inv_mul_cancel₀ ha, one_smul] at hx'

end Basic

section Rank

variable {R : Type*} [CommRing R] [IsDomain R] {M : Type*} [AddCommGroup M] [Module R M]

theorem rank_saturation (N : Submodule R M) :
    Module.rank R (saturation N) = Module.rank R N := by
  have h1 := rank_quotient_add_rank_of_isDomain (N.submoduleOf (saturation N))
  have h2 : Module.rank R (saturation N ⧸ N.submoduleOf (saturation N)) = 0 := by
    rw [rank_eq_zero_iff]
    intro y
    have ht := isTorsion_saturation_quotient N
    obtain ⟨⟨a, ha⟩, hay⟩ := @ht y
    exact ⟨a, nonZeroDivisors.ne_zero ha, hay⟩
  rw [h2, zero_add, (Submodule.submoduleOfEquivOfLe (le_saturation N)).rank_eq] at h1
  exact h1.symm

theorem finrank_saturation [Module.Finite R M] (N : Submodule R M) :
    Module.finrank R (saturation N) = Module.finrank R N := congrArg Cardinal.toNat (rank_saturation N)

theorem le_saturation_of_rank_le {N P : Submodule R M} (h : N ≤ P)
    (hN : Module.rank R N < Cardinal.aleph0) (hr : Module.rank R P ≤ Module.rank R N) :
    P ≤ saturation N := by
  intro x hx
  have hadd := rank_quotient_add_rank_of_isDomain (N.submoduleOf P)
  rw [(Submodule.submoduleOfEquivOfLe h).rank_eq] at hadd
  have hq : Module.rank R (P ⧸ N.submoduleOf P) = 0 := by
    obtain ⟨n, hn⟩ := Cardinal.lt_aleph0.1 hN
    have hlt : Module.rank R (P ⧸ N.submoduleOf P) + Module.rank R N < Cardinal.aleph0 := by
      rw [hadd]
      exact hr.trans_lt hN
    obtain ⟨m, hm⟩ := Cardinal.lt_aleph0.1 (Cardinal.add_lt_aleph0_iff.1 hlt).1
    have hle : (m : Cardinal) + n ≤ n := by
      rw [← hm, ← hn, hadd]
      exact hr
    have hm0 : m = 0 := by
      have hmn : m + n ≤ n := by exact_mod_cast hle
      omega
    rw [hm, hm0, Nat.cast_zero]
  obtain ⟨a, ha, hax⟩ := rank_eq_zero_iff.1 hq (Submodule.Quotient.mk ⟨x, hx⟩)
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hax
  exact mem_saturation_of_smul_mem ha hax

theorem le_saturation_iff_finrank_eq [Module.Finite R M] {N P : Submodule R M} (h : N ≤ P) :
    P ≤ saturation N ↔ Module.finrank R N = Module.finrank R P := by
  have hfin : ∀ Q : Submodule R M, Module.rank R Q < Cardinal.aleph0 := fun Q =>
    (Submodule.rank_le Q).trans_lt (Module.rank_lt_aleph0 R M)
  constructor
  · intro hP
    have h1 : Module.rank R N ≤ Module.rank R P := Submodule.rank_mono h
    have h2 : Module.rank R P ≤ Module.rank R N :=
      (Submodule.rank_mono hP).trans_eq (rank_saturation N)
    exact congrArg Cardinal.toNat (le_antisymm h1 h2)
  · intro he
    refine le_saturation_of_rank_le h (hfin N) ?_
    rw [← Cardinal.cast_toNat_of_lt_aleph0 (hfin P), ← Cardinal.cast_toNat_of_lt_aleph0 (hfin N)]
    exact_mod_cast he.ge

theorem IsSaturatedSubmodule.eq_of_le_of_finrank_eq [Module.Finite R M] {N P : Submodule R M}
    (hN : IsSaturatedSubmodule N) (h : N ≤ P) (hr : Module.finrank R N = Module.finrank R P) :
    N = P := le_antisymm h (((le_saturation_iff_finrank_eq h).2 hr).trans hN.saturation_eq.le)

end Rank

section Relative

variable {R : Type*} [CommRing R] {V V' : Type*} [AddCommGroup V] [Module R V]
  [AddCommGroup V'] [Module R V']

def saturationIn (M N : Submodule R V) : Submodule R V :=
  M ⊓ saturation N

def IsSaturatedIn (M N : Submodule R V) : Prop :=
  saturationIn M N = N

theorem saturationIn_def (M N : Submodule R V) : saturationIn M N = M ⊓ saturation N := rfl

theorem mem_saturationIn_iff [IsDomain R] {M N : Submodule R V} {x : V} :
    x ∈ saturationIn M N ↔ x ∈ M ∧ ∃ a : R, a ≠ 0 ∧ a • x ∈ N := by
  rw [saturationIn_def, Submodule.mem_inf, mem_saturation_iff]

theorem saturationIn_le (M N : Submodule R V) : saturationIn M N ≤ M := inf_le_left

theorem le_saturationIn {M N : Submodule R V} (h : N ≤ M) : N ≤ saturationIn M N := le_inf h (le_saturation N)

@[gcongr]
theorem saturationIn_mono {M M' N N' : Submodule R V} (hM : M ≤ M') (hN : N ≤ N') :
    saturationIn M N ≤ saturationIn M' N' := inf_le_inf hM (saturation_mono hN)

@[simp]
theorem saturationIn_top (N : Submodule R V) : saturationIn ⊤ N = saturation N := by
  rw [saturationIn_def, top_inf_eq]

@[simp]
theorem isSaturatedIn_top_iff {N : Submodule R V} :
    IsSaturatedIn ⊤ N ↔ IsSaturatedSubmodule N := by
  unfold IsSaturatedIn IsSaturatedSubmodule
  rw [saturationIn_top]

theorem saturationIn_inf (M N : Submodule R V) : saturationIn M (M ⊓ N) = saturationIn M N := by
  rw [saturationIn_def, saturationIn_def, saturation_inf, ← inf_assoc,
    inf_of_le_left (le_saturation M)]

@[simp]
theorem saturationIn_saturationIn (M N : Submodule R V) :
    saturationIn M (saturationIn M N) = saturationIn M N := by
  rw [saturationIn_def, saturationIn_def, saturation_inf, saturation_saturation, ← inf_assoc,
    inf_of_le_left (le_saturation M)]

theorem isSaturatedIn_saturationIn (M N : Submodule R V) : IsSaturatedIn M (saturationIn M N) := by
  unfold IsSaturatedIn
  rw [saturationIn_saturationIn]

theorem saturation_saturationIn {M N : Submodule R V} (h : N ≤ M) :
    saturation (saturationIn M N) = saturation N := by
  rw [saturationIn_def, saturation_inf, saturation_saturation, inf_of_le_right (saturation_mono h)]

theorem map_subtype_saturation (M : Submodule R V) (N : Submodule R M) :
    (saturation N).map M.subtype = saturationIn M (N.map M.subtype) := by
  rw [map_saturation_of_injective (f := M.subtype) Subtype.coe_injective, Submodule.range_subtype,
    saturationIn_def]

theorem submoduleOf_saturationIn (M N : Submodule R V) :
    (saturationIn M N).submoduleOf M = saturation (N.submoduleOf M) := by
  rw [saturationIn_def, Submodule.submoduleOf, Submodule.submoduleOf, Submodule.comap_inf,
    saturation_comap, Submodule.comap_subtype_self, top_inf_eq]

theorem map_subtype_saturation_submoduleOf (M N : Submodule R V) :
    (saturation (N.submoduleOf M)).map M.subtype = saturationIn M N := by
  rw [map_subtype_saturation, Submodule.submoduleOf, Submodule.map_comap_subtype, saturationIn_inf]

theorem IsSaturatedIn.le {M N : Submodule R V} (h : IsSaturatedIn M N) : N ≤ M := by
  have h' : saturationIn M N = N := h
  rw [← h']
  exact saturationIn_le M N

theorem IsSaturatedIn.saturationIn_eq {M N : Submodule R V} (h : IsSaturatedIn M N) :
    saturationIn M N = N := h

theorem isSaturatedIn_iff {M N : Submodule R V} :
    IsSaturatedIn M N ↔ N ≤ M ∧ IsSaturatedSubmodule (N.submoduleOf M) := by
  constructor
  · intro hs
    refine ⟨hs.le, ?_⟩
    unfold IsSaturatedSubmodule
    rw [← submoduleOf_saturationIn, hs.saturationIn_eq]
  · rintro ⟨hle, hs⟩
    unfold IsSaturatedIn
    rw [← map_subtype_saturation_submoduleOf, hs.saturation_eq, Submodule.submoduleOf,
      Submodule.map_comap_subtype, inf_of_le_right hle]

theorem isSaturatedIn_map_subtype_iff {M : Submodule R V} {N : Submodule R M} :
    IsSaturatedIn M (N.map M.subtype) ↔ IsSaturatedSubmodule N := by
  unfold IsSaturatedIn IsSaturatedSubmodule
  rw [← map_subtype_saturation]
  exact (Submodule.map_injective_of_injective (f := M.subtype) Subtype.coe_injective).eq_iff

theorem isSaturatedIn_iff_isTorsionFree [IsDomain R] {M N : Submodule R V} :
    IsSaturatedIn M N ↔ N ≤ M ∧ Module.IsTorsionFree R (M ⧸ N.submoduleOf M) := by
  rw [isSaturatedIn_iff, isSaturatedSubmodule_iff_isTorsionFree]

theorem isSaturatedIn_iff_smul_mem [IsDomain R] {M N : Submodule R V} :
    IsSaturatedIn M N ↔ N ≤ M ∧ ∀ a : R, a ≠ 0 → ∀ x ∈ M, a • x ∈ N → x ∈ N := by
  constructor
  · intro hs
    refine ⟨hs.le, fun a ha x hx hax => ?_⟩
    rw [← hs.saturationIn_eq]
    exact mem_saturationIn_iff.2 ⟨hx, a, ha, hax⟩
  · rintro ⟨hle, hs⟩
    show saturationIn M N = N
    refine le_antisymm (fun x hx => ?_) (le_saturationIn hle)
    obtain ⟨hxM, a, ha, hax⟩ := mem_saturationIn_iff.1 hx
    exact hs a ha x hxM hax

theorem IsSaturatedSubmodule.isSaturatedIn_inf {W : Submodule R V} (h : IsSaturatedSubmodule W)
    (M : Submodule R V) : IsSaturatedIn M (M ⊓ W) := by
  unfold IsSaturatedIn
  rw [saturationIn_inf, saturationIn_def, h.saturation_eq]

theorem IsSaturatedIn.trans {M P N : Submodule R V} (hP : IsSaturatedIn M P)
    (hN : IsSaturatedIn P N) : IsSaturatedIn M N := by
  have hNP := hN.le
  have hPM := hP.le
  show saturationIn M N = N
  refine le_antisymm (fun x hx => ?_) (le_saturationIn (hNP.trans hPM))
  rw [saturationIn_def, Submodule.mem_inf] at hx
  have hxP : x ∈ P := by
    rw [← hP.saturationIn_eq, saturationIn_def]
    exact Submodule.mem_inf.2 ⟨hx.1, saturation_mono hNP hx.2⟩
  rw [← hN.saturationIn_eq, saturationIn_def]
  exact Submodule.mem_inf.2 ⟨hxP, hx.2⟩

theorem map_saturationIn_of_injective {f : V →ₗ[R] V'} (hf : Function.Injective f)
    (M N : Submodule R V) :
    (saturationIn M N).map f = saturationIn (M.map f) (N.map f) := by
  rw [saturationIn_def, saturationIn_def, Submodule.map_inf f hf, map_saturation_of_injective hf,
    ← inf_assoc, inf_of_le_left LinearMap.map_le_range]

theorem rank_saturationIn [IsDomain R] {M N : Submodule R V} (h : N ≤ M) :
    Module.rank R (saturationIn M N) = Module.rank R N := by
  rw [← map_subtype_saturation_submoduleOf,
    ← (Submodule.equivMapOfInjective M.subtype Subtype.coe_injective
      (saturation (N.submoduleOf M))).rank_eq, rank_saturation,
    (Submodule.submoduleOfEquivOfLe h).rank_eq]

theorem finrank_saturationIn [IsDomain R] {M N : Submodule R V} [Module.Finite R M] (h : N ≤ M) :
    Module.finrank R (saturationIn M N) = Module.finrank R N := congrArg Cardinal.toNat (rank_saturationIn h)

end Relative

section Localisation

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
  (S : Type*) [CommRing S] [Algebra R S] (p : Submonoid R) [IsLocalization p S]
  {Mp : Type*} [AddCommGroup Mp] [Module R Mp] [Module S Mp] [IsScalarTower R S Mp]
  (f : M →ₗ[R] Mp) [IsLocalizedModule p f]

theorem mk'_mem_localized'_iff (N : Submodule R M) (x : M) (s : p) :
    IsLocalizedModule.mk' f x s ∈ N.localized' S p f ↔ ∃ a ∈ p, a • x ∈ N := by
  rw [Submodule.mem_localized']
  constructor
  · rintro ⟨m, hm, t, ht⟩
    obtain ⟨c, hc⟩ := (IsLocalizedModule.mk'_eq_mk'_iff f m x t s).1 ht
    refine ⟨((c * t : p) : R), (c * t).2, ?_⟩
    have e : ((c * t : p) : R) • x = ((c * s : p) : R) • m := by
      simp only [Submonoid.coe_mul, mul_smul]
      simpa only [Submonoid.smul_def] using hc
    rw [e]
    exact N.smul_mem _ hm
  · rintro ⟨a, ha, hax⟩
    exact ⟨a • x, hax, ⟨a, ha⟩ * s, IsLocalizedModule.mk'_cancel_left f x ⟨a, ha⟩ s⟩

theorem localized'_saturation (hp : p ≤ R⁰) (N : Submodule R M) :
    (saturation N).localized' S p f = saturation (N.localized' S p f) := by
  apply le_antisymm
  · refine ((Submodule.localized'gi S p f).gc _ _).2 fun m hm => ?_
    obtain ⟨a, ha, ham⟩ := mem_saturation_iff'.1 hm
    rw [Submodule.mem_comap, Submodule.restrictScalars_mem]
    refine mem_saturation_iff'.2
      ⟨algebraMap R S a, IsLocalization.nonZeroDivisors_le_comap (M := p) (S := S) ha, ?_⟩
    rw [algebraMap_smul, ← map_smul]
    exact (Submodule.mem_localized' S p f N _).2 ⟨a • m, ham, 1, IsLocalizedModule.mk'_one p f _⟩
  · intro y hy
    obtain ⟨b, hb, hby⟩ := mem_saturation_iff'.1 hy
    obtain ⟨⟨m, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective p f y
    obtain ⟨⟨r, t⟩, rfl⟩ := IsLocalization.mk'_surjective p b
    simp only [Function.uncurry_apply_pair] at hby ⊢
    rw [IsLocalizedModule.mk'_smul_mk', mk'_mem_localized'_iff] at hby
    obtain ⟨c, hc, hcr⟩ := hby
    have hr : r ∈ R⁰ := by
      have h1 : algebraMap R S r ∈ S⁰ := by
        rw [← IsLocalization.mk'_spec S r t]
        exact mul_mem hb (IsLocalization.map_units S t).mem_nonZeroDivisors
      exact mem_nonZeroDivisors_of_injective (IsLocalization.injective S hp) h1
    refine (Submodule.mem_localized' S p f _ _).2
      ⟨m, mem_saturation_iff'.2 ⟨c * r, mul_mem (hp hc) hr, ?_⟩, s, rfl⟩
    rwa [mul_smul]

theorem IsSaturatedSubmodule.localized' (hp : p ≤ R⁰) {N : Submodule R M}
    (h : IsSaturatedSubmodule N) : IsSaturatedSubmodule (N.localized' S p f) := by
  unfold IsSaturatedSubmodule
  rw [← localized'_saturation S p f hp, h.saturation_eq]

theorem IsSaturatedSubmodule.comap_localized' (hp : p ≤ R⁰) {N : Submodule R M}
    (h : IsSaturatedSubmodule N) : ((N.localized' S p f).restrictScalars R).comap f = N := by
  refine le_antisymm (fun m hm => ?_) (((Submodule.localized'gi S p f).gc _ _).1 le_rfl)
  rw [Submodule.mem_comap, Submodule.restrictScalars_mem, ← IsLocalizedModule.mk'_one p f m,
    mk'_mem_localized'_iff] at hm
  obtain ⟨a, ha, ham⟩ := hm
  exact h.saturation_eq.le (mem_saturation_iff'.2 ⟨a, hp ha, ham⟩)

theorem localized'_saturationIn (hp : p ≤ R⁰) (P N : Submodule R M) :
    (saturationIn P N).localized' S p f =
      saturationIn (P.localized' S p f) (N.localized' S p f) := by
  rw [saturationIn_def, saturationIn_def, Submodule.localized'_inf, localized'_saturation S p f hp]

theorem localized_saturation_atPrime [IsDomain R] (P : Ideal R) [P.IsPrime] (N : Submodule R M) :
    (saturation N).localized P.primeCompl = saturation (N.localized P.primeCompl) := localized'_saturation (Localization P.primeCompl) P.primeCompl
    (LocalizedModule.mkLinearMap P.primeCompl M) P.primeCompl_le_nonZeroDivisors N

theorem isSaturatedSubmodule_iff_localized_maximal [IsDomain R] {N : Submodule R M} :
    IsSaturatedSubmodule N ↔
      ∀ (P : Ideal R) [P.IsMaximal], IsSaturatedSubmodule (N.localized P.primeCompl) := by
  constructor
  · intro h P _
    exact h.localized' (Localization P.primeCompl) P.primeCompl
      (LocalizedModule.mkLinearMap P.primeCompl M) P.primeCompl_le_nonZeroDivisors
  · intro h
    rw [isSaturatedSubmodule_iff_le]
    refine Submodule.le_of_localization_maximal (fun P _ => LocalizedModule P.primeCompl M)
      (fun P _ => LocalizedModule.mkLinearMap P.primeCompl M) fun P _ => ?_
    exact (congrArg (Submodule.restrictScalars R)
      ((localized_saturation_atPrime P N).trans (h P).saturation_eq)).le

end Localisation

section AmbientLocalisation

variable {R : Type*} [CommRing R] (S : Type*) [CommRing S] [Algebra R S] (p : Submonoid R)
  [IsLocalization p S] {V : Type*} [AddCommGroup V] [Module R V] [Module S V]
  [IsScalarTower R S V]

include p

theorem mem_span_localization_iff (N : Submodule R V) (x : V) :
    x ∈ Submodule.span S (N : Set V) ↔ ∃ a ∈ p, a • x ∈ N := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact ⟨1, one_mem _, by rwa [one_smul]⟩
    | zero => exact ⟨1, one_mem _, by rw [smul_zero]; exact N.zero_mem⟩
    | add y z _ _ hy hz =>
      obtain ⟨a, ha, hay⟩ := hy
      obtain ⟨b, hb, hbz⟩ := hz
      refine ⟨a * b, mul_mem ha hb, ?_⟩
      rw [smul_add]
      refine N.add_mem ?_ ?_
      · rw [mul_comm, mul_smul]
        exact N.smul_mem b hay
      · rw [mul_smul]
        exact N.smul_mem a hbz
    | smul s y _ hy =>
      obtain ⟨a, ha, hay⟩ := hy
      obtain ⟨⟨r, t⟩, rfl⟩ := IsLocalization.mk'_surjective p s
      refine ⟨(t : R) * a, mul_mem t.2 ha, ?_⟩
      have e : ((t : R) * a) • (IsLocalization.mk' S r t • y) = r • (a • y) := by
        rw [mul_smul, smul_comm a (IsLocalization.mk' S r t) y, ← algebraMap_smul S (t : R),
          smul_smul (algebraMap R S t), IsLocalization.mk'_spec', algebraMap_smul]
      rw [e]
      exact N.smul_mem r hay
  · rintro ⟨a, ha, hax⟩
    have hu : IsUnit (algebraMap R S a) := IsLocalization.map_units S (⟨a, ha⟩ : p)
    rw [← Submodule.smul_mem_iff_of_isUnit _ hu, algebraMap_smul]
    exact Submodule.subset_span hax

theorem isLocalizedModule_inclusionSpan (M : Submodule R V) :
    IsLocalizedModule p (M.inclusionSpan S) where
  map_units := by
    intro x
    rw [Module.End.isUnit_iff]
    have hu : IsUnit (algebraMap R S x) := IsLocalization.map_units S x
    constructor
    · intro y z hyz
      simp only [Module.algebraMap_end_apply] at hyz
      rw [← algebraMap_smul S (x : R) y, ← algebraMap_smul S (x : R) z] at hyz
      exact (hu.smul_left_cancel).1 hyz
    · intro y
      obtain ⟨u, hu'⟩ := hu
      refine ⟨(↑u⁻¹ : S) • y, ?_⟩
      simp only [Module.algebraMap_end_apply]
      rw [← algebraMap_smul S (x : R), smul_smul, ← hu', Units.mul_inv, one_smul]
  surj y := by
    obtain ⟨a, ha, hay⟩ := (mem_span_localization_iff S p M (y : V)).1 y.2
    exact ⟨(⟨a • (y : V), hay⟩, ⟨a, ha⟩), Subtype.ext rfl⟩
  exists_of_eq {x₁ x₂} h := ⟨1, by
    rw [one_smul, one_smul]
    exact Submodule.injective_inclusionSpan (p := M) (S := S) h⟩

theorem span_localization_inf (M N : Submodule R V) :
    Submodule.span S ((M ⊓ N : Submodule R V) : Set V) =
      Submodule.span S (M : Set V) ⊓ Submodule.span S (N : Set V) := by
  refine le_antisymm (le_inf (Submodule.span_mono fun _ hx => (Submodule.mem_inf.1 hx).1)
    (Submodule.span_mono fun _ hx => (Submodule.mem_inf.1 hx).2)) ?_
  intro x hx
  obtain ⟨hM, hN⟩ := Submodule.mem_inf.1 hx
  obtain ⟨a, ha, hax⟩ := (mem_span_localization_iff S p M x).1 hM
  obtain ⟨b, hb, hbx⟩ := (mem_span_localization_iff S p N x).1 hN
  refine (mem_span_localization_iff S p (M ⊓ N) x).2
    ⟨a * b, mul_mem ha hb, Submodule.mem_inf.2 ⟨?_, ?_⟩⟩
  · rw [mul_comm, mul_smul]
    exact M.smul_mem b hax
  · rw [mul_smul]
    exact N.smul_mem a hbx

theorem span_localization_inf_restrictScalars (M : Submodule R V) (W : Submodule S V) :
    Submodule.span S ((M ⊓ W.restrictScalars R : Submodule R V) : Set V) =
      Submodule.span S (M : Set V) ⊓ W := by
  rw [span_localization_inf S p, Submodule.coe_restrictScalars, Submodule.span_eq]

theorem span_localization_saturation (hp : p ≤ R⁰) (N : Submodule R V) :
    Submodule.span S (saturation N : Set V) = saturation (Submodule.span S (N : Set V)) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    intro x hx
    obtain ⟨a, ha, hax⟩ := mem_saturation_iff'.1 hx
    refine mem_saturation_iff'.2
      ⟨algebraMap R S a, IsLocalization.nonZeroDivisors_le_comap (M := p) (S := S) ha, ?_⟩
    rw [algebraMap_smul]
    exact Submodule.subset_span hax
  · intro y hy
    obtain ⟨b, hb, hby⟩ := mem_saturation_iff'.1 hy
    obtain ⟨c, hc, hcb⟩ := (mem_span_localization_iff S p N _).1 hby
    obtain ⟨⟨r, t⟩, rfl⟩ := IsLocalization.mk'_surjective p b
    have hr : r ∈ R⁰ := by
      have h1 : algebraMap R S r ∈ S⁰ := by
        rw [← IsLocalization.mk'_spec S r t]
        exact mul_mem hb (IsLocalization.map_units S t).mem_nonZeroDivisors
      exact mem_nonZeroDivisors_of_injective (IsLocalization.injective S hp) h1
    have e : (t : R) • c • (IsLocalization.mk' S r t • y) = (c * r) • y := by
      rw [smul_comm c (IsLocalization.mk' S r t) y, ← algebraMap_smul S (t : R),
        smul_smul (algebraMap R S t), IsLocalization.mk'_spec', algebraMap_smul, smul_smul,
        mul_comm]
    refine Submodule.subset_span (mem_saturation_iff'.2 ⟨c * r, mul_mem (hp hc) hr, ?_⟩)
    rw [← e]
    exact N.smul_mem _ hcb

theorem span_localization_saturationIn (hp : p ≤ R⁰) (M N : Submodule R V) :
    Submodule.span S (saturationIn M N : Set V) =
      saturationIn (Submodule.span S (M : Set V)) (Submodule.span S (N : Set V)) := by
  rw [saturationIn_def, saturationIn_def, span_localization_inf S p,
    span_localization_saturation S p hp]

theorem IsSaturatedIn.span_localization (hp : p ≤ R⁰) {M N : Submodule R V}
    (h : IsSaturatedIn M N) :
    IsSaturatedIn (Submodule.span S (M : Set V)) (Submodule.span S (N : Set V)) := by
  unfold IsSaturatedIn
  rw [← span_localization_saturationIn S p hp, h.saturationIn_eq]

end AmbientLocalisation

section GenericFibre

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
  (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
  {V : Type*} [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
  (f : M →ₗ[R] V) [IsLocalizedModule R⁰ f]

theorem saturation_eq_comap_localized' (N : Submodule R M) :
    saturation N = ((N.localized' K R⁰ f).restrictScalars R).comap f := by
  ext x
  rw [Submodule.mem_comap, Submodule.restrictScalars_mem, ← IsLocalizedModule.mk'_one R⁰ f x,
    mk'_mem_localized'_iff, mem_saturation_iff']

def saturatedOrderIsoSubspace :
    {N : Submodule R M // IsSaturatedSubmodule N} ≃o Submodule K V where
  toFun N := N.1.localized' K R⁰ f
  invFun W := ⟨(W.restrictScalars R).comap f, by
    rw [IsSaturatedSubmodule, saturation_eq_comap_localized' K f,
      (Submodule.localized'gi K R⁰ f).l_u_eq W]⟩
  left_inv N := Subtype.ext (N.2.comap_localized' K R⁰ f le_rfl)
  right_inv W := (Submodule.localized'gi K R⁰ f).l_u_eq W
  map_rel_iff' {N P} := by
    refine ((Submodule.localized'gi K R⁰ f).gc N.1 (P.1.localized' K R⁰ f)).trans ?_
    rw [P.2.comap_localized' K R⁰ f le_rfl]
    rfl

theorem saturatedOrderIsoSubspace_apply (N : {N : Submodule R M // IsSaturatedSubmodule N}) :
    saturatedOrderIsoSubspace K f N = Submodule.span K (f '' N.1) := by
  show N.1.localized' K R⁰ f = _
  exact Submodule.localized'_eq_span K R⁰ f N.1

@[simp]
theorem saturatedOrderIsoSubspace_symm_apply (W : Submodule K V) :
    ((saturatedOrderIsoSubspace K f).symm W).1 = (W.restrictScalars R).comap f := rfl

theorem localized'_saturation_fractionRing (N : Submodule R M) :
    (saturation N).localized' K R⁰ f = N.localized' K R⁰ f := by
  rw [localized'_saturation K R⁰ f le_rfl, (isSaturatedSubmodule_of_field _).saturation_eq]

end GenericFibre

section Lattice

variable {R : Type*} [CommRing R] (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
  {V : Type*} [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]

theorem saturation_eq_span (N : Submodule R V) :
    saturation N = (Submodule.span K (N : Set V)).restrictScalars R := by
  ext x
  rw [Submodule.restrictScalars_mem, mem_span_localization_iff K R⁰ N x, mem_saturation_iff']

theorem saturationIn_eq_inf_span (M N : Submodule R V) :
    saturationIn M N = M ⊓ (Submodule.span K (N : Set V)).restrictScalars R := by
  rw [saturationIn_def, saturation_eq_span K]

theorem map_subtype_saturation_eq_inf_span (M : Submodule R V) (N : Submodule R M) :
    (saturation N).map M.subtype =
      M ⊓ (Submodule.span K (N.map M.subtype : Set V)).restrictScalars R := by
  rw [map_subtype_saturation, saturationIn_eq_inf_span K]

theorem mem_saturation_iff_mem_span {M : Submodule R V} {N : Submodule R M} {x : M} :
    x ∈ saturation N ↔ (x : V) ∈ Submodule.span K (N.map M.subtype : Set V) := by
  have e := map_subtype_saturation_eq_inf_span K M N
  constructor
  · intro hx
    have hx' : (x : V) ∈ (saturation N).map M.subtype := Submodule.mem_map_of_mem hx
    rw [e] at hx'
    exact (Submodule.mem_inf.1 hx').2
  · intro hx
    have hx' : (x : V) ∈ M ⊓ (Submodule.span K (N.map M.subtype : Set V)).restrictScalars R :=
      Submodule.mem_inf.2 ⟨x.2, hx⟩
    rw [← e] at hx'
    obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.1 hx'
    have hxy : y = x := Subtype.ext hyx
    rw [← hxy]
    exact hy

variable {K} in

theorem isSaturatedSubmodule_restrictScalars (W : Submodule K V) :
    IsSaturatedSubmodule (W.restrictScalars R) := by
  unfold IsSaturatedSubmodule
  rw [saturation_eq_span K, Submodule.coe_restrictScalars, Submodule.span_eq]

variable {K} in

theorem isSaturatedIn_inf_restrictScalars (M : Submodule R V) (W : Submodule K V) :
    IsSaturatedIn M (M ⊓ W.restrictScalars R) := (isSaturatedSubmodule_restrictScalars W).isSaturatedIn_inf M

variable {K} in

theorem isSaturatedSubmodule_comap_restrictScalars {M : Type*} [AddCommGroup M] [Module R M]
    (f : M →ₗ[R] V) (W : Submodule K V) :
    IsSaturatedSubmodule ((W.restrictScalars R).comap f) := (isSaturatedSubmodule_restrictScalars W).comap f

theorem isSaturatedIn_iff_inf_span_eq {M N : Submodule R V} :
    IsSaturatedIn M N ↔ M ⊓ (Submodule.span K (N : Set V)).restrictScalars R = N := by
  unfold IsSaturatedIn
  rw [saturationIn_eq_inf_span K]

theorem isSaturatedIn_iff_exists_subspace {M N : Submodule R V} :
    IsSaturatedIn M N ↔ ∃ W : Submodule K V, M ⊓ W.restrictScalars R = N := by
  constructor
  · intro h
    exact ⟨Submodule.span K (N : Set V), (isSaturatedIn_iff_inf_span_eq K).1 h⟩
  · rintro ⟨W, rfl⟩
    exact isSaturatedIn_inf_restrictScalars M W

variable {K} in

theorem span_inf_restrictScalars (M : Submodule R V) (W : Submodule K V) :
    Submodule.span K ((M ⊓ W.restrictScalars R : Submodule R V) : Set V) =
      Submodule.span K (M : Set V) ⊓ W := span_localization_inf_restrictScalars K R⁰ M W

variable {K} in

theorem span_inf_restrictScalars_of_le {M : Submodule R V} {W : Submodule K V}
    (h : W ≤ Submodule.span K (M : Set V)) :
    Submodule.span K ((M ⊓ W.restrictScalars R : Submodule R V) : Set V) = W := by
  rw [span_inf_restrictScalars, inf_of_le_right h]

theorem span_saturationIn {M N : Submodule R V} (h : N ≤ M) :
    Submodule.span K (saturationIn M N : Set V) = Submodule.span K (N : Set V) := by
  rw [saturationIn_eq_inf_span K, span_inf_restrictScalars, inf_of_le_right (Submodule.span_mono h)]

def saturatedOrderIsoSubspaceSpan (M : Submodule R V) :
    {N : Submodule R M // IsSaturatedSubmodule N} ≃o
      Submodule K (Submodule.span K (M : Set V)) :=
  haveI := isLocalizedModule_inclusionSpan K R⁰ M
  saturatedOrderIsoSubspace K (M.inclusionSpan K)

theorem map_saturatedOrderIsoSubspaceSpan_apply (M : Submodule R V)
    (N : {N : Submodule R M // IsSaturatedSubmodule N}) :
    (saturatedOrderIsoSubspaceSpan K M N).map (Submodule.span K (M : Set V)).subtype =
      Submodule.span K (N.1.map M.subtype : Set V) := by
  have := isLocalizedModule_inclusionSpan K R⁰ M
  have e : saturatedOrderIsoSubspaceSpan K M N = Submodule.span K (M.inclusionSpan K '' N.1) :=
    saturatedOrderIsoSubspace_apply K (M.inclusionSpan K) N
  rw [e, Submodule.map_span, ← Set.image_comp]
  rfl

theorem mem_saturatedOrderIsoSubspaceSpan_symm_apply (M : Submodule R V)
    (W : Submodule K (Submodule.span K (M : Set V))) (x : M) :
    x ∈ ((saturatedOrderIsoSubspaceSpan K M).symm W).1 ↔ M.inclusionSpan K x ∈ W := Iff.rfl

def saturatedInOrderIso (M : Submodule R V) :
    {N : Submodule R V // IsSaturatedIn M N} ≃o Set.Iic (Submodule.span K (M : Set V)) where
  toFun N := ⟨Submodule.span K (N.1 : Set V), Submodule.span_mono N.2.le⟩
  invFun W := ⟨M ⊓ W.1.restrictScalars R, isSaturatedIn_inf_restrictScalars M W.1⟩
  left_inv N := Subtype.ext ((isSaturatedIn_iff_inf_span_eq K).1 N.2)
  right_inv W := Subtype.ext (span_inf_restrictScalars_of_le W.2)
  map_rel_iff' {N P} := by
    refine ⟨fun h => ?_, fun h => Submodule.span_mono h⟩
    change N.1 ≤ P.1
    rw [← (isSaturatedIn_iff_inf_span_eq K).1 P.2]
    exact le_inf N.2.le fun x hx => h (Submodule.subset_span hx)

@[simp]
theorem saturatedInOrderIso_apply (M : Submodule R V)
    (N : {N : Submodule R V // IsSaturatedIn M N}) :
    (saturatedInOrderIso K M N).1 = Submodule.span K (N.1 : Set V) := rfl

@[simp]
theorem saturatedInOrderIso_symm_apply (M : Submodule R V)
    (W : Set.Iic (Submodule.span K (M : Set V))) :
    ((saturatedInOrderIso K M).symm W).1 = M ⊓ W.1.restrictScalars R := rfl

theorem rank_eq_rank_span (N : Submodule R V) :
    Module.rank R N = Module.rank K (Submodule.span K (N : Set V)) := by
  have := isLocalizedModule_inclusionSpan K R⁰ N
  rw [IsLocalization.rank_eq K R⁰ le_rfl, IsLocalizedModule.rank_eq R⁰ le_rfl (N.inclusionSpan K)]

variable {K} in

theorem rank_inf_restrictScalars {M : Submodule R V} {W : Submodule K V}
    (h : W ≤ Submodule.span K (M : Set V)) :
    Module.rank R (M ⊓ W.restrictScalars R : Submodule R V) = Module.rank K W := by
  rw [rank_eq_rank_span K, span_inf_restrictScalars_of_le h]

variable {K} in

theorem finrank_inf_restrictScalars {M : Submodule R V} {W : Submodule K V}
    [FiniteDimensional K W] (h : W ≤ Submodule.span K (M : Set V)) :
    Module.finrank R (M ⊓ W.restrictScalars R : Submodule R V) = Module.finrank K W := congrArg Cardinal.toNat (rank_inf_restrictScalars h)

variable {K} in
omit [IsFractionRing R K] in

theorem smul_inf_restrictScalars (M : Submodule R V) (W : Submodule K V) {c : K} (hc : c ≠ 0) :
    c • M ⊓ W.restrictScalars R = c • (M ⊓ W.restrictScalars R) := by
  ext x
  simp only [Submodule.mem_inf, Submodule.mem_smul_pointwise_iff_exists,
    Submodule.restrictScalars_mem]
  constructor
  · rintro ⟨⟨y, hy, rfl⟩, hw⟩
    refine ⟨y, ⟨hy, ?_⟩, rfl⟩
    have hw' := W.smul_mem c⁻¹ hw
    rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at hw'
  · rintro ⟨y, ⟨hy, hw⟩, rfl⟩
    exact ⟨⟨y, hy, rfl⟩, W.smul_mem c hw⟩

variable {K} in

theorem saturationIn_smul_left (M N : Submodule R V) {c : K} (hc : c ≠ 0) :
    saturationIn (c • M) N = c • saturationIn M N := by
  rw [saturationIn_eq_inf_span K, saturationIn_eq_inf_span K, smul_inf_restrictScalars M _ hc]

end Lattice

section Examples

theorem isSaturatedSubmodule_span_one_two :
    IsSaturatedSubmodule (Submodule.span ℤ {((1, 2) : ℤ × ℤ)}) := by
  rw [isSaturatedSubmodule_iff]
  intro a ha x hx
  rw [Submodule.mem_span_singleton] at hx ⊢
  obtain ⟨k, hk⟩ := hx
  have h1 : k = a * x.1 := by simpa using congrArg Prod.fst hk
  have h2 : k * 2 = a * x.2 := by simpa using congrArg Prod.snd hk
  refine ⟨x.1, Prod.ext ?_ ?_⟩
  · simp
  · have h3 : a * (x.1 * 2) = a * x.2 := by linear_combination (-2 : ℤ) * h1 + h2
    simpa using mul_left_cancel₀ ha h3

example : saturation (Submodule.span ℤ {((3, 6) : ℤ × ℤ)}) =
    Submodule.span ℤ {((1, 2) : ℤ × ℤ)} := by
  refine (isSaturatedSubmodule_span_one_two.eq_saturation ?_ ?_).symm
  · rw [Submodule.span_singleton_le_iff_mem]
    exact Submodule.mem_span_singleton.2 ⟨3, rfl⟩
  · rw [Submodule.span_singleton_le_iff_mem]
    exact mem_saturation_of_smul_mem (a := 3) (by norm_num) (Submodule.mem_span_singleton_self _)

example : ¬ IsSaturatedSubmodule (Submodule.span ℤ {(2 : ℤ)}) := by
  intro h
  have h₁ : (1 : ℤ) ∈ Submodule.span ℤ {(2 : ℤ)} :=
    h.mem_of_smul_mem (a := 2) (by norm_num) (Submodule.mem_span_singleton_self _)
  obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.1 h₁
  simp only [smul_eq_mul] at hb
  omega

example : saturation (⊥ : Submodule ℤ (ZMod 2)) = ⊤ :=
  top_le_iff.1 fun x _ => mem_saturation_of_smul_mem (a := 2) (by norm_num) (by
    rw [Submodule.mem_bot]; exact (by decide : ∀ y : ZMod 2, (2 : ℤ) • y = 0) x)

example : saturationIn (Submodule.span ℤ {(2 : ℚ)}) (Submodule.span ℤ {(6 : ℚ)}) =
      Submodule.span ℤ {(2 : ℚ)} ∧ saturation (Submodule.span ℤ {(6 : ℚ)}) = ⊤ := by
  have h : saturation (Submodule.span ℤ {(6 : ℚ)}) = ⊤ := by
    rw [saturation_eq_span ℚ, Submodule.span_span_of_tower, Submodule.restrictScalars_eq_top_iff,
      Submodule.span_singleton_eq_top_iff]
    intro v
    exact ⟨v / 6, by simp⟩
  exact ⟨by rw [saturationIn, h, inf_top_eq], h⟩

end Examples

end GlobalTheory
