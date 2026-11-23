import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.MemSpanSSelf

open Module

noncomputable section

namespace Formalism.L2.SG.Pf.G3

open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0 Formalism.HermitianLattices.Ext.L3.WA

section

variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
variable {S : Subring K} {π : K} {h : V →ₗ⋆[K] V →ₗ[K] K}

private theorem mem_iff_lemma {ι : Type} [Fintype ι] (b : ι → V) (v : V) :
    v ∈ spanS S b ↔ ∃ c : ι → K, (∀ i, c i ∈ S) ∧ v = ∑ i, c i • b i := Iff.rfl

private theorem smul_mem_lemma_2 {ι : Type} [Fintype ι] {g : ι → V} {a : K} (ha : a ∈ S) {v : V}
    (hv : v ∈ spanS S g) : a • v ∈ spanS S g := by
  rw [mem_iff_lemma] at hv ⊢
  obtain ⟨d, hd, rfl⟩ := hv
  exact ⟨fun i => a * d i, fun i => S.mul_mem ha (hd i), by simp [Finset.smul_sum, mul_smul]⟩

theorem spanS_le_of {κ ι : Type} [Fintype κ] [Fintype ι] {f : κ → V} {g : ι → V}
    (hfg : ∀ k, f k ∈ spanS S g) {v : V} (hv : v ∈ spanS S f) : v ∈ spanS S g := by
  rw [mem_iff_lemma] at hv
  obtain ⟨c, hc, rfl⟩ := hv
  exact AddSubgroup.sum_mem _ fun k _ => smul_mem_lemma_2 (hc k) (hfg k)

theorem mem_span_of_spanS {ι : Type} [Fintype ι] {g : ι → V} {v : V} (hv : v ∈ spanS S g) :
    v ∈ Submodule.span K (Set.range g) := by
  rw [mem_iff_lemma] at hv
  obtain ⟨c, -, rfl⟩ := hv
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem spans_eq {κ ι : Type} [Fintype κ] [Fintype ι] {f : κ → V} {g : ι → V}
    (h1 : ∀ k, f k ∈ spanS S g) (h2 : ∀ i, g i ∈ spanS S f) :
    Submodule.span K (Set.range f) = Submodule.span K (Set.range g) ∧
      ∀ v, v ∈ spanS S f ↔ v ∈ spanS S g := by
  refine ⟨le_antisymm ?_ ?_, fun v => ⟨spanS_le_of h1, spanS_le_of h2⟩⟩
  · rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    exact mem_span_of_spanS (h1 k)
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact mem_span_of_spanS (h2 i)

theorem form_pair (x y : V) (hxy : h x y = 0) (hyx : h y x = 0) (α β γ δ : K) :
    h (α • x + β • y) (γ • x + δ • y) = star α * γ * h x x + star β * δ * h y y := by
  simp only [map_add, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, map_smul, hxy, hyx,
    smul_eq_mul, starRingEnd_apply, RingHom.id_apply, mul_zero, add_zero, zero_add]
  ring

theorem form_pair_orth (x y z : V) (hxz : h x z = 0) (hyz : h y z = 0) (α β : K) :
    h (α • x + β • y) z = 0 := by
  simp only [map_add, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, hxz, hyz,
    smul_eq_mul, mul_zero, add_zero]

theorem hermitian_coefficient_identity_one {A B D α β : K} (hA : A ≠ 0) (hD : D ≠ 0)
    (hDdef : D = star α * α * A + star β * β * B) :
    A * D⁻¹ * (star α * α + β * (star β * (B * A⁻¹))) = 1 := by
  have hAA : A * A⁻¹ = 1 := mul_inv_cancel₀ hA
  have e : A * (star α * α + β * (star β * (B * A⁻¹))) = D := by
    rw [hDdef]
    linear_combination (β * star β * B) * hAA
  calc A * D⁻¹ * (star α * α + β * (star β * (B * A⁻¹)))
      = D⁻¹ * (A * (star α * α + β * (star β * (B * A⁻¹)))) := by ring
    _ = 1 := by rw [e, inv_mul_cancel₀ hD]

theorem hermitian_coefficient_identity_two {A B D α β : K} (hA : A ≠ 0) (hD : D ≠ 0)
    (hDdef : D = star α * α * A + star β * β * B) :
    A * D⁻¹ * (star β * (B * A⁻¹) * β + α * star α) = 1 := by
  have hAA : A * A⁻¹ = 1 := mul_inv_cancel₀ hA
  have e : A * (star β * (B * A⁻¹) * β + α * star α) = D := by
    rw [hDdef]
    linear_combination (star β * β * B) * hAA
  calc A * D⁻¹ * (star β * (B * A⁻¹) * β + α * star α)
      = D⁻¹ * (A * (star β * (B * A⁻¹) * β + α * star α)) := by ring
    _ = 1 := by rw [e, inv_mul_cancel₀ hD]

private theorem isUnitIn_mul_dual_family_counting {a c : K} (ha : IsUnitIn S a) (hc : IsUnitIn S c) :
    IsUnitIn S (a * c) :=
  And.intro (mul_ne_zero ha.1 hc.1)
    (And.intro (S.mul_mem ha.2.1 hc.2.1) (by rw [mul_inv]; exact S.mul_mem ha.2.2 hc.2.2))

private theorem isUnitIn_inv {a : K} (ha : IsUnitIn S a) : IsUnitIn S a⁻¹ :=
  And.intro (inv_ne_zero ha.1) (And.intro ha.2.2 (by rw [inv_inv]; exact ha.2.1))

theorem rot2 (hS : IsHermSemilocal S) (hπ : IsUnif S π) (hs : h.IsSymm) {ι : Type} [Fintype ι]
    [DecidableEq ι] {b : ι → V} {e : ι → ℕ} (ho : ∀ i j, i ≠ j → h (b i) (b j) = 0)
    (hu : ∀ i, IsUnitIn S (h (b i) (b i) * (π ^ e i)⁻¹)) {i₀ j : ι} (hij : i₀ ≠ j)
    (hm : e i₀ ≤ e j) {α β : K} (hα : α ∈ S) (hβ : β ∈ S)
    (hY : IsUnitIn S (h (α • b i₀ + β • b j) (α • b i₀ + β • b j) * (π ^ e i₀)⁻¹)) :
    ∃ c : ι → V, (∀ p q, p ≠ q → h (c p) (c q) = 0) ∧
      (∀ i, IsUnitIn S (h (c i) (c i) * (π ^ e i)⁻¹)) ∧ c i₀ = α • b i₀ + β • b j ∧
      (∀ k, k ≠ i₀ → k ≠ j → c k = b k) ∧
      Submodule.span K (Set.range c) = Submodule.span K (Set.range b) ∧
      ∀ v, v ∈ spanS S c ↔ v ∈ spanS S b := by
  set A := h (b i₀) (b i₀) with hAdef
  set B := h (b j) (b j) with hBdef
  set Y := α • b i₀ + β • b j with hYdef
  set D := h Y Y with hDdef'
  have hA : A ≠ 0 := unit_ne (hu i₀)
  have hD : D ≠ 0 := unit_ne hY
  have hAA : A * A⁻¹ = 1 := mul_inv_cancel₀ hA
  have hπ0 : π ≠ 0 := hπ.ne
  have hAs : star A = A := by
    have := hs.eq (b i₀) (b i₀)
    rwa [starRingEnd_apply] at this
  have hBs : star B = B := by
    have := hs.eq (b j) (b j)
    rwa [starRingEnd_apply] at this
  have hDdef : D = star α * α * A + star β * β * B :=
    form_pair (b i₀) (b j) (ho i₀ j hij) (ho j i₀ hij.symm) α β α β
  obtain ⟨d, hd⟩ : ∃ d, e j = e i₀ + d := ⟨_, (Nat.add_sub_of_le hm).symm⟩
  have hBA : B * A⁻¹ ∈ S := by
    have eq : B * A⁻¹ = (B * (π ^ e j)⁻¹) * (A * (π ^ e i₀)⁻¹)⁻¹ * π ^ d := by
      rw [hd, pow_add]
      field_simp
    rw [eq]
    exact S.mul_mem (S.mul_mem (hu j).2.1 (hu i₀).2.2) (S.pow_mem hπ.mem d)
  have hAD : A * D⁻¹ ∈ S := by
    have eq : A * D⁻¹ = (A * (π ^ e i₀)⁻¹) * (D * (π ^ e i₀)⁻¹)⁻¹ := by
      field_simp
    rw [eq]
    exact S.mul_mem (hu i₀).2.1 hY.2.2
  have hγ : -(star β * (B * A⁻¹)) ∈ S := S.neg_mem (S.mul_mem (hS.star_mem β hβ) hBA)
  have hδ : star α ∈ S := hS.star_mem α hα
  set Z := (-(star β * (B * A⁻¹))) • b i₀ + star α • b j with hZdef
  have hYZ : h Y Z = 0 := by
    calc h Y Z = star α * (-(star β * (B * A⁻¹))) * A + star β * star α * B :=
          form_pair (b i₀) (b j) (ho i₀ j hij) (ho j i₀ hij.symm) _ _ _ _
      _ = 0 := by linear_combination (-(star α * star β * B)) * hAA
  have hZY : h Z Y = 0 := by
    have := hs.eq Y Z
    rw [hYZ, map_zero] at this
    exact this.symm
  have hsg : star (-(star β * (B * A⁻¹))) = -(A⁻¹ * B * β) := by
    rw [star_neg, star_mul, star_mul, star_star, star_inv₀, hAs, hBs]
  have hZZ : h Z Z = B * A⁻¹ * D := by
    calc h Z Z = star (-(star β * (B * A⁻¹))) * (-(star β * (B * A⁻¹))) * A
          + star (star α) * star α * B :=
          form_pair (b i₀) (b j) (ho i₀ j hij) (ho j i₀ hij.symm) _ _ _ _
      _ = B * A⁻¹ * D := by
          rw [hsg, star_star, hDdef]
          linear_combination (A⁻¹ * B ^ 2 * β * star β - α * star α * B) * hAA
  have hZu : IsUnitIn S (h Z Z * (π ^ e j)⁻¹) := by
    have eqZ : h Z Z * (π ^ e j)⁻¹
        = (B * (π ^ e j)⁻¹) * (D * (π ^ e i₀)⁻¹) * (A * (π ^ e i₀)⁻¹)⁻¹ := by
      rw [hZZ]
      field_simp
    rw [eqZ]
    exact isUnitIn_mul_dual_family_counting (isUnitIn_mul_dual_family_counting (hu j) hY) (isUnitIn_inv (hu i₀))
  obtain ⟨c, hc0, hcj, hck⟩ : ∃ c : ι → V, c i₀ = Y ∧ c j = Z ∧ ∀ k, k ≠ i₀ → k ≠ j → c k = b k :=
    ⟨Function.update (Function.update b i₀ Y) j Z, by simp [Function.update_apply, hij],
      by simp [Function.update_apply], fun k h1 h2 => by simp [Function.update_apply, h1, h2]⟩
  have hYk : ∀ k, k ≠ i₀ → k ≠ j → h Y (b k) = 0 := fun k h1 h2 =>
    form_pair_orth _ _ _ (ho i₀ k (Ne.symm h1)) (ho j k (Ne.symm h2)) α β
  have hZk : ∀ k, k ≠ i₀ → k ≠ j → h Z (b k) = 0 := fun k h1 h2 =>
    form_pair_orth _ _ _ (ho i₀ k (Ne.symm h1)) (ho j k (Ne.symm h2)) _ _
  have hkY : ∀ k, k ≠ i₀ → k ≠ j → h (b k) Y = 0 := by
    intro k h1 h2
    show h (b k) (α • b i₀ + β • b j) = 0
    rw [map_add, map_smul, map_smul, ho k i₀ h1, ho k j h2, smul_zero, smul_zero, add_zero]
  have hkZ : ∀ k, k ≠ i₀ → k ≠ j → h (b k) Z = 0 := by
    intro k h1 h2
    show h (b k) ((-(star β * (B * A⁻¹))) • b i₀ + star α • b j) = 0
    rw [map_add, map_smul, map_smul, ho k i₀ h1, ho k j h2, smul_zero, smul_zero, add_zero]
  have ortho : ∀ p q, p ≠ q → h (c p) (c q) = 0 := by
    intro p q hpq
    by_cases hp0 : p = i₀
    · rw [hp0] at hpq ⊢
      by_cases hqj : q = j
      · rw [hqj, hc0, hcj]
        exact hYZ
      · rw [hc0, hck q (Ne.symm hpq) hqj]
        exact hYk q (Ne.symm hpq) hqj
    · by_cases hpj : p = j
      · rw [hpj] at hpq ⊢
        by_cases hq0 : q = i₀
        · rw [hq0, hcj, hc0]
          exact hZY
        · rw [hcj, hck q hq0 (Ne.symm hpq)]
          exact hZk q hq0 (Ne.symm hpq)
      · rw [hck p hp0 hpj]
        by_cases hq0 : q = i₀
        · rw [hq0, hc0]
          exact hkY p hp0 hpj
        · by_cases hqj : q = j
          · rw [hqj, hcj]
            exact hkZ p hp0 hpj
          · rw [hck q hq0 hqj]
            exact ho p q hpq
  have units : ∀ i, IsUnitIn S (h (c i) (c i) * (π ^ e i)⁻¹) := by
    intro i
    by_cases hi0 : i = i₀
    · rw [hi0, hc0]
      exact hY
    · by_cases hij' : i = j
      · rw [hij', hcj]
        exact hZu
      · rw [hck i hi0 hij']
        exact hu i
  have memb : ∀ x y : K, x ∈ S → y ∈ S → x • b i₀ + y • b j ∈ spanS S b := fun x y hx hy =>
    add_mem (smul_mem_lemma_2 hx (mem_spanS_self b i₀)) (smul_mem_lemma_2 hy (mem_spanS_self b j))
  have h1 : ∀ k, c k ∈ spanS S b := by
    intro k
    by_cases hk0 : k = i₀
    · rw [hk0, hc0]
      exact memb α β hα hβ
    · by_cases hkj : k = j
      · rw [hkj, hcj]
        exact memb _ _ hγ hδ
      · rw [hck k hk0 hkj]
        exact mem_spanS_self b k
  have memc : ∀ x y : K, x ∈ S → y ∈ S → x • Y + y • Z ∈ spanS S c := fun x y hx hy => by
    have := add_mem (smul_mem_lemma_2 hx (mem_spanS_self c i₀)) (smul_mem_lemma_2 hy (mem_spanS_self c j))
    rwa [hc0, hcj] at this
  have exp2 : ∀ a1 a2 : K, a1 • Y + a2 • Z = (a1 * α + a2 * (-(star β * (B * A⁻¹)))) • b i₀
      + (a1 * β + a2 * star α) • b j := by
    intro a1 a2
    rw [hYdef, hZdef]
    simp only [smul_add, smul_smul, add_smul]
    abel
  have h2 : ∀ i, b i ∈ spanS S c := by
    intro i
    by_cases hi0 : i = i₀
    · rw [hi0]
      have e1 : b i₀ = (A * D⁻¹ * star α) • Y + (-(A * D⁻¹ * β)) • Z := by
        rw [exp2]
        have c1 : A * D⁻¹ * star α * α + -(A * D⁻¹ * β) * -(star β * (B * A⁻¹)) = 1 := by
          linear_combination hermitian_coefficient_identity_one hA hD hDdef
        have c2 : A * D⁻¹ * star α * β + -(A * D⁻¹ * β) * star α = 0 := by ring
        rw [c1, c2, one_smul, zero_smul, add_zero]
      rw [e1]
      exact memc _ _ (S.mul_mem hAD hδ) (S.neg_mem (S.mul_mem hAD hβ))
    · by_cases hij' : i = j
      · rw [hij']
        have e2 : b j = (A * D⁻¹ * (star β * (B * A⁻¹))) • Y + (A * D⁻¹ * α) • Z := by
          rw [exp2]
          have c1 : A * D⁻¹ * (star β * (B * A⁻¹)) * α + A * D⁻¹ * α * -(star β * (B * A⁻¹))
              = 0 := by ring
          have c2 : A * D⁻¹ * (star β * (B * A⁻¹)) * β + A * D⁻¹ * α * star α = 1 := by
            linear_combination hermitian_coefficient_identity_two hA hD hDdef
          rw [c1, c2, zero_smul, one_smul, zero_add]
        rw [e2]
        exact memc _ _ (S.mul_mem hAD (S.mul_mem (hS.star_mem β hβ) hBA)) (S.mul_mem hAD hα)
      · rw [← hck i hi0 hij']
        exact mem_spanS_self c i
  obtain ⟨hsp, hiff⟩ := spans_eq h1 h2
  exact ⟨c, ortho, units, hc0, hck, hsp, hiff⟩

end

end Formalism.L2.SG.Pf.G3
