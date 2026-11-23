import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.SplitAtOf

open Module

noncomputable section

namespace Formalism.L2.SG.Pf.G3

open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0 Formalism.HermitianLattices.Ext.L3.WA

section

variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
variable {S : Subring K} {π : K} {h : V →ₗ⋆[K] V →ₗ[K] K}

theorem spanS_smul_mem {ι : Type} [Fintype ι] {b : ι → V} {a : K} (ha : a ∈ S) {v : V}
    (hv : v ∈ spanS S b) : a • v ∈ spanS S b := by
  obtain ⟨c, hc, rfl⟩ := hv
  refine Exists.intro (fun i => a * c i) ⟨fun i => S.mul_mem ha (hc i), ?_⟩
  simp only [Finset.smul_sum, smul_smul]

theorem form_sum_orth {ι : Type} [Fintype ι] {b : ι → V} (ho : ∀ i j, i ≠ j → h (b i) (b j) = 0)
    (c : ι → K) (i : ι) : h (b i) (∑ j, c j • b j) = c i * h (b i) (b i) := by
  simp only [map_sum, map_smul, smul_eq_mul]
  rw [Finset.sum_eq_single i (fun j _ hji => by rw [ho i j (Ne.symm hji), mul_zero])
    (fun hi => absurd (Finset.mem_univ i) hi)]

theorem mem_spanS_iff_sub {ι : Type} [Fintype ι] [DecidableEq ι] {b : ι → V}
    (ho : ∀ i j, i ≠ j → h (b i) (b j) = 0) {i₀ : ι} (h0 : h (b i₀) (b i₀) ≠ 0) (T : Subring K)
    (v : V) : (v ∈ spanS T b ∧ h (b i₀) v = 0) ↔
      v ∈ spanS T (fun j : {i // i ≠ i₀} => b j) := by
  constructor
  · rintro ⟨⟨c, hc, rfl⟩, hv⟩
    have hci : c i₀ = 0 := by
      rw [form_sum_orth ho c i₀] at hv
      exact (mul_eq_zero.mp hv).resolve_right h0
    refine Exists.intro (fun j => c j) ⟨fun j => hc j, ?_⟩
    rw [Fintype.sum_eq_add_sum_subtype_ne _ i₀, hci, zero_smul, zero_add]
  · rintro ⟨d, hd, rfl⟩
    refine ⟨Exists.intro (fun i => if hi : i = i₀ then 0 else d ⟨i, hi⟩) ⟨fun i => ?_, ?_⟩, ?_⟩
    · dsimp only
      split_ifs
      exacts [T.zero_mem, hd _]
    · rw [Fintype.sum_eq_add_sum_subtype_ne _ i₀]
      dsimp only
      rw [dif_pos rfl, zero_smul, zero_add]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [dif_neg j.2]
    · rw [map_sum]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [map_smul, ho i₀ j (Ne.symm j.2), smul_zero]

theorem mem_span_iff_spanS {ι : Type} [Fintype ι] (b : ι → V) (v : V) :
    v ∈ Submodule.span K (Set.range b) ↔ v ∈ spanS (⊤ : Subring K) b := by
  rw [Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, rfl⟩
    exact Exists.intro c ⟨fun _ => Subring.mem_top _, rfl⟩
  · rintro ⟨c, _, rfl⟩
    exact ⟨c, rfl⟩

theorem mem_cutW_span_iff {ι : Type} [Fintype ι] [DecidableEq ι] {b : ι → V}
    (ho : ∀ i j, i ≠ j → h (b i) (b j) = 0) {i₀ : ι} (h0 : h (b i₀) (b i₀) ≠ 0) (v : V) :
    v ∈ cutW h (Submodule.span K (Set.range b)) (b i₀) ↔
      v ∈ Submodule.span K (Set.range (fun j : {i // i ≠ i₀} => b j)) := by
  simp only [cutW, Submodule.mem_inf, LinearMap.mem_ker]
  rw [mem_span_iff_spanS, mem_span_iff_spanS]
  exact mem_spanS_iff_sub ho h0 ⊤ v

theorem mem_cutM_spanS_iff {ι : Type} [Fintype ι] [DecidableEq ι] {b : ι → V}
    (ho : ∀ i j, i ≠ j → h (b i) (b j) = 0) {i₀ : ι} (h0 : h (b i₀) (b i₀) ≠ 0) (v : V) :
    v ∈ cutM h (spanS S b) (b i₀) ↔ v ∈ spanS S (fun j : {i // i ≠ i₀} => b j) := by
  simp only [cutM, AddSubgroup.mem_inf, Submodule.mem_toAddSubgroup, LinearMap.mem_ker]
  exact mem_spanS_iff_sub ho h0 S v

theorem coef_mem {ι : Type} [Fintype ι] {b : ι → V} (ho : ∀ i j, i ≠ j → h (b i) (b j) = 0)
    {i₀ : ι} (h0 : h (b i₀) (b i₀) ≠ 0) {m : V} (hm : m ∈ spanS S b) :
    h (b i₀) m * (h (b i₀) (b i₀))⁻¹ ∈ S := by
  obtain ⟨c, hc, rfl⟩ := hm
  rw [form_sum_orth ho c i₀, mul_inv_cancel_right₀ h0]
  exact hc i₀

theorem mem_iff_of_cut' {M N : AddSubgroup V} (hMs : ∀ a ∈ S, ∀ m ∈ M, a • m ∈ M)
    (hNs : ∀ a ∈ S, ∀ m ∈ N, a • m ∈ N) {x X : V} (hx : x ∈ M) (hX : X ∈ N)
    (hMx : ∀ m ∈ M, h x m * (h x x)⁻¹ ∈ S) (hNX : ∀ m ∈ N, h X m * (h X X)⁻¹ ∈ S)
    {g : V ≃ₗ[K] V} (hg : g ∈ Formalism.HermitianLatticesTheory.isom h) (hgx : g x = X) (hxx : h x x ≠ 0)
    (hcut : ∀ v, v ∈ cutM h M x ↔ g v ∈ cutM h N X) : ∀ v, v ∈ M ↔ g v ∈ N := by
  have hcut' : ∀ v, (v ∈ M ∧ h x v = 0) ↔ (g v ∈ N ∧ h X (g v) = 0) := by
    intro v
    have := hcut v
    simp only [cutM, AddSubgroup.mem_inf, Submodule.mem_toAddSubgroup, LinearMap.mem_ker] at this
    exact this
  have hiso : ∀ u w, h (g u) (g w) = h u w := hg
  have hXX : h X X ≠ 0 := by
    rw [← hgx, hiso x x]
    exact hxx
  intro v
  constructor
  · intro hv
    have hαS : h x v * (h x x)⁻¹ ∈ S := hMx v hv
    have h1 : v - (h x v * (h x x)⁻¹) • x ∈ M := M.sub_mem hv (hMs _ hαS x hx)
    have h2 : h x (v - (h x v * (h x x)⁻¹) • x) = 0 := by
      rw [map_sub, map_smul, smul_eq_mul, inv_mul_cancel_right₀ hxx, sub_self]
    obtain ⟨h3, -⟩ := (hcut' _).mp ⟨h1, h2⟩
    rw [map_sub, map_smul, hgx] at h3
    have := N.add_mem h3 (hNs _ hαS X hX)
    rwa [sub_add_cancel] at this
  · intro hv
    have hβS : h X (g v) * (h X X)⁻¹ ∈ S := hNX _ hv
    have h1 : g (v - (h X (g v) * (h X X)⁻¹) • x) ∈ N := by
      rw [map_sub, map_smul, hgx]
      exact N.sub_mem hv (hNs _ hβS X hX)
    have h2 : h X (g (v - (h X (g v) * (h X X)⁻¹) • x)) = 0 := by
      rw [map_sub, map_smul, hgx, map_sub, map_smul, smul_eq_mul, inv_mul_cancel_right₀ hXX,
        sub_self]
    obtain ⟨h3, -⟩ := (hcut' _).mpr ⟨h1, h2⟩
    have := M.add_mem h3 (hMs _ hβS x hx)
    rwa [sub_add_cancel] at this

end

end Formalism.L2.SG.Pf.G3
