import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.MemSpanIffSpanS

open Module

noncomputable section

namespace Formalism.L2.SG.Pf.G3

open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0 Formalism.HermitianLattices.Ext.L3.WA

section

variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
variable {S : Subring K} {π : K} {h : V →ₗ⋆[K] V →ₗ[K] K}

theorem unit_ne {a : K} {k : ℕ} (hu : IsUnitIn S (a * (π ^ k)⁻¹)) : a ≠ 0 := by
  intro ha
  apply hu.1
  rw [ha, zero_mul]

private theorem mem_iff_lemma {ι : Type} [Fintype ι] (b : ι → V) (v : V) :
    v ∈ spanS S b ↔ ∃ c : ι → K, (∀ i, c i ∈ S) ∧ v = ∑ i, c i • b i := Iff.rfl

theorem spanS_empty {ι : Type} [Fintype ι] [IsEmpty ι] (b : ι → V) (v : V) :
    v ∈ spanS S b ↔ v = 0 := by
  rw [mem_iff_lemma]
  constructor
  · rintro ⟨c, -, rfl⟩
    simp
  · rintro rfl
    exact ⟨0, fun _ => S.zero_mem, by simp⟩

theorem mem_spanS_self {ι : Type} [Fintype ι] [DecidableEq ι] (b : ι → V) (i : ι) :
    b i ∈ spanS S b := by
  refine (mem_iff_lemma b (b i)).2 ⟨fun j => if j = i then 1 else 0, fun j => ?_, ?_⟩
  · dsimp only
    split_ifs
    · exact S.one_mem
    · exact S.zero_mem
  · simp [ite_smul]

theorem core_empty {ι : Type} [Fintype ι] [IsEmpty ι] (b b' : ι → V) {φ : V ≃ₗ[K] V}
    (hφ : φ ∈ Formalism.HermitianLatticesTheory.isom h) :
    ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, (∀ v, (∀ w ∈ Submodule.span K (Set.range b), h w v = 0) → g v = φ v) ∧
      ∀ v, v ∈ spanS S b ↔ g v ∈ spanS S b' := by
  refine ⟨φ, hφ, fun v _ => rfl, fun v => ?_⟩
  rw [spanS_empty b v, spanS_empty b' (φ v)]
  constructor
  · intro h0
    rw [h0, map_zero]
  · intro h0
    apply φ.injective
    rw [h0, map_zero]

private theorem span_ne_eq_cutW_of_orthogonal {ι : Type} [Fintype ι] [DecidableEq ι] {f : ι → V}
    (ho : ∀ i j, i ≠ j → h (f i) (f j) = 0) {i₀ : ι} (hf0 : h (f i₀) (f i₀) ≠ 0) :
    Submodule.span K (Set.range (fun i : {i // i ≠ i₀} => f i)) =
      cutW h (Submodule.span K (Set.range f)) (f i₀) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    show f i ∈ Submodule.span K (Set.range f) ⊓ LinearMap.ker (h (f i₀))
    exact Submodule.mem_inf.2 ⟨Submodule.subset_span ⟨i, rfl⟩,
      LinearMap.mem_ker.2 (ho i₀ i (Ne.symm i.2))⟩
  · intro v hv
    have hv' : v ∈ Submodule.span K (Set.range f) ⊓ LinearMap.ker (h (f i₀)) := hv
    obtain ⟨hv1, hv2⟩ := Submodule.mem_inf.1 hv'
    obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hv1
    have ha0 : a i₀ = 0 := by
      rw [LinearMap.mem_ker, map_sum, Finset.sum_eq_single i₀] at hv2
      · rw [map_smul, smul_eq_mul] at hv2
        exact (mul_eq_zero.1 hv2).resolve_right hf0
      · intro i _ hi
        rw [map_smul, ho i₀ i (Ne.symm hi), smul_zero]
      · intro h'
        exact absurd (Finset.mem_univ i₀) h'
    rw [Fintype.sum_eq_add_sum_subtype_ne _ i₀, ha0, zero_smul, zero_add]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

private theorem mem_spanS_iff_smul_add_mem_spanS_ne {ι : Type} [Fintype ι] [DecidableEq ι] (f : ι → V) (i₀ : ι)
    (v : V) : v ∈ spanS S f ↔
      ∃ a ∈ S, ∃ w ∈ spanS S (fun i : {i // i ≠ i₀} => f i), v = a • f i₀ + w := by
  rw [mem_iff_lemma]
  constructor
  · rintro ⟨c, hc, rfl⟩
    refine ⟨c i₀, hc i₀, ∑ i : {i // i ≠ i₀}, c i • f i,
      (mem_iff_lemma _ _).2 ⟨fun i => c i, fun i => hc i, rfl⟩, ?_⟩
    exact Fintype.sum_eq_add_sum_subtype_ne _ i₀
  · rintro ⟨a, ha, w, hw, rfl⟩
    rw [mem_iff_lemma] at hw
    obtain ⟨d, hd, rfl⟩ := hw
    refine ⟨fun i => if hi : i = i₀ then a else d ⟨i, hi⟩, fun i => ?_, ?_⟩
    · dsimp only
      split_ifs
      · exact ha
      · exact hd _
    · rw [Fintype.sum_eq_add_sum_subtype_ne _ i₀]
      dsimp only
      rw [dif_pos rfl]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [dif_neg i.2]

theorem core_of_split (hs : h.IsSymm) (hd : ∀ x, h x x = 0 → x = 0) (hsp : SplitAt S π h) :
    ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι], Fintype.card ι ≤ n →
    ∀ (b b' : ι → V) (e : ι → ℕ) (φ : V ≃ₗ[K] V),
    (∀ i j, i ≠ j → h (b i) (b j) = 0) → (∀ i j, i ≠ j → h (b' i) (b' j) = 0) →
    (∀ i, IsUnitIn S (h (b i) (b i) * (π ^ e i)⁻¹)) →
    (∀ i, IsUnitIn S (h (b' i) (b' i) * (π ^ e i)⁻¹)) → φ ∈ Formalism.HermitianLatticesTheory.isom h →
    (∀ v, v ∈ Submodule.span K (Set.range b) ↔ φ v ∈ Submodule.span K (Set.range b')) →
    ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, (∀ v, (∀ w ∈ Submodule.span K (Set.range b), h w v = 0) → g v = φ v) ∧
      ∀ v, v ∈ spanS S b ↔ g v ∈ spanS S b' := by
  intro n
  induction n with
  | zero =>
    intro ι _ _ hcard b b' e φ _ _ _ _ hφ _
    have : IsEmpty ι := Fintype.card_eq_zero_iff.1 (Nat.le_zero.1 hcard)
    exact core_empty b b' hφ
  | succ n ih =>
    intro ι _ _ hcard b b' e φ ho ho' hu hu' hφ hW
    rcases isEmpty_or_nonempty ι with hι | hι
    · exact core_empty b b' hφ
    obtain ⟨i₀, -, hmin⟩ := Finset.exists_min_image Finset.univ e Finset.univ_nonempty
    have hb0 : b i₀ ∈ Submodule.span K (Set.range b) := Submodule.subset_span ⟨i₀, rfl⟩
    have hξ : φ (b i₀) ∈ Submodule.span K (Set.range b') := (hW _).1 hb0
    have hφn : h (φ (b i₀)) (φ (b i₀)) = h (b i₀) (b i₀) := hφ (b i₀) (b i₀)
    obtain ⟨c, hoc, huc, hcc, hspc, hiffc⟩ := hsp ι b' e i₀ ho' hu'
      (fun i => hmin i (Finset.mem_univ i)) (φ (b i₀)) hξ (by rw [hφn]; exact hu i₀)
    have hWc : ∀ v, v ∈ Submodule.span K (Set.range b) ↔
        φ v ∈ Submodule.span K (Set.range c) := by
      intro v
      rw [hspc]
      exact hW v
    obtain ⟨φ', hφ', hφ'0, hcut, hagree⟩ := exists_prep hs hd hφ hWc hb0
      (Submodule.subset_span ⟨i₀, rfl⟩) (by rw [hcc, hφn])
    have hA : h (b i₀) (b i₀) ≠ 0 := unit_ne (hu i₀)
    have hC : h (c i₀) (c i₀) ≠ 0 := unit_ne (huc i₀)
    have hcardS : Fintype.card {i // i ≠ i₀} ≤ n := by
      have := Fintype.card_subtype_lt (p := fun i => i ≠ i₀) (x := i₀) (by simp)
      omega
    have hWbb : ∀ v, v ∈ Submodule.span K (Set.range (fun i : {i // i ≠ i₀} => b i)) ↔
        φ' v ∈ Submodule.span K (Set.range (fun i : {i // i ≠ i₀} => c i)) := by
      intro v
      rw [span_ne_eq_cutW_of_orthogonal ho hA, span_ne_eq_cutW_of_orthogonal hoc hC]
      exact hcut v
    obtain ⟨g, hg, hgagree, hgiff⟩ := ih {i // i ≠ i₀} hcardS (fun i => b i) (fun i => c i)
      (fun i => e i) φ' (fun i j hij => ho i j (fun h' => hij (Subtype.ext h')))
      (fun i j hij => hoc i j (fun h' => hij (Subtype.ext h'))) (fun i => hu i) (fun i => huc i)
      hφ' hWbb
    have hperp : ∀ w ∈ Submodule.span K (Set.range (fun i : {i // i ≠ i₀} => b i)),
        h w (b i₀) = 0 := by
      intro w hw
      obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hw
      rw [map_sum, LinearMap.sum_apply]
      exact Finset.sum_eq_zero fun i _ => by
        rw [map_smulₛₗ, LinearMap.smul_apply, ho i i₀ i.2, smul_zero]
    have hg0 : g (b i₀) = c i₀ := by rw [hgagree _ hperp, hφ'0]
    refine ⟨g, hg, fun v hv => ?_, fun v => ?_⟩
    · have hv' : ∀ w ∈ Submodule.span K (Set.range (fun i : {i // i ≠ i₀} => b i)), h w v = 0 :=
        fun w hw => hv w (Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact ⟨i, rfl⟩) hw)
      rw [hgagree v hv', hagree v hv]
    · rw [← hiffc, mem_spanS_iff_smul_add_mem_spanS_ne b i₀, mem_spanS_iff_smul_add_mem_spanS_ne c i₀]
      constructor
      · rintro ⟨a, ha, w, hw, rfl⟩
        refine ⟨a, ha, g w, (hgiff w).1 hw, ?_⟩
        rw [map_add, map_smul, hg0]
      · rintro ⟨a, ha, u, hu2, huv⟩
        refine ⟨a, ha, g.symm u, (hgiff _).2 (by rw [LinearEquiv.apply_symm_apply]; exact hu2), ?_⟩
        apply g.injective
        rw [huv, map_add, map_smul, hg0, LinearEquiv.apply_symm_apply]

end

end Formalism.L2.SG.Pf.G3
