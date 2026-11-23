import Mathlib
import ReciprocityTheory.ClassFieldTheory.LocalClassField.RecDefs
import ReciprocityTheory.ClassFieldTheory.LocalClassField.GalBasic
import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsDvdQKPowSubOne

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh Function

variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))

open Topology
open scoped commutatorElement

variable {p K L}

theorem IsAbLK.normal (h : IsAbLK p K L) : (subG p K L).Normal := by
  refine ⟨fun n hn g => ?_⟩
  have h1 : g * n * g⁻¹ = ⁅g, n⁆ * n := by
    rw [commutatorElement_def]; group
  rw [h1]
  exact mul_mem (h.comm (Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top n))) hn

theorem isAbLK_self (hK : FiniteDimensional ℚ_[p] K) : IsAbLK p K K :=
  ⟨le_rfl, hK, fun σ _ x hx => σ.commutes ⟨x, hx⟩⟩

theorem subG_sup_eq_inf (L L' : IntermediateField ℚ_[p] (PadicAlgCl p)) :
    subG p K (L ⊔ L') = subG p K L ⊓ subG p K L' := by
  refine le_antisymm (le_inf (subG_anti le_sup_left) (subG_anti le_sup_right)) fun σ hσ => ?_
  have hle : L ⊔ L' ≤ (IntermediateField.fixedField (Subgroup.zpowers σ)).restrictScalars ℚ_[p] := by
    refine sup_le (fun x hx => ?_) (fun x hx => ?_)
    · rw [IntermediateField.mem_restrictScalars, IntermediateField.mem_fixedField_iff]
      intro τ hτ
      exact (Subgroup.zpowers_le.2 hσ.1 : Subgroup.zpowers σ ≤ subG p K L) hτ x hx
    · rw [IntermediateField.mem_restrictScalars, IntermediateField.mem_fixedField_iff]
      intro τ hτ
      exact (Subgroup.zpowers_le.2 hσ.2 : Subgroup.zpowers σ ≤ subG p K L') hτ x hx
  intro x hx
  have := hle hx
  rw [IntermediateField.mem_restrictScalars, IntermediateField.mem_fixedField_iff] at this
  exact this σ (Subgroup.mem_zpowers σ)

theorem IsAbLK.sup {L' : IntermediateField ℚ_[p] (PadicAlgCl p)} (h : IsAbLK p K L) (h' : IsAbLK p K L') : IsAbLK p K (L ⊔ L') := by
  refine ⟨h.le.trans le_sup_left, ?_, ?_⟩
  · have := h.fin
    have := h'.fin
    exact IntermediateField.finiteDimensional_sup L L'
  · rw [subG_sup_eq_inf]
    exact le_inf h.comm h'.comm

theorem IsAbLK.of_le {L' : IntermediateField ℚ_[p] (PadicAlgCl p)} (h' : IsAbLK p K L') (hK : K ≤ L) (hL : L ≤ L') : IsAbLK p K L := by
  refine ⟨hK, ?_, h'.comm.trans (subG_anti hL)⟩
  have := h'.fin
  exact Module.Finite.of_injective (IntermediateField.inclusion hL).toLinearMap
    (IntermediateField.inclusion hL).injective

theorem isAbLK_of_cyclic (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L) [(subG p K L).Normal] (g₀ : GalLK p K L)
    (hg : ∀ g, g ∈ Subgroup.zpowers g₀) : IsAbLK p K L := by
  refine ⟨h, hL, Subgroup.Normal.quotient_commutative_iff_commutator_le.1 ⟨⟨fun a b => ?_⟩⟩⟩
  obtain ⟨i, rfl⟩ := hg a
  obtain ⟨j, rfl⟩ := hg b
  exact (zpow_mul_comm g₀ i j)

theorem isAbLK_Kn (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) : IsAbLK p K (Kn p K n) :=
  isAbLK_of_cyclic (finiteDimensional_Kn p K hK hn) (le_Kn p K n) (frobLK p K (Kn p K n))
    (mem_zpowers_frobLK_Kn hK hn)

theorem toAbK_surjective : Surjective (toAbK p K) := QuotientGroup.mk'_surjective _

theorem continuous_toAbK : Continuous (toAbK p K) := QuotientGroup.continuous_mk

theorem isOpenMap_toAbK : IsOpenMap (toAbK p K) := QuotientGroup.isOpenMap_coe

theorem mem_closure_commutator_iff (hK : FiniteDimensional ℚ_[p] K) (g : GK p K) :
    g ∈ (commutator (GK p K)).topologicalClosure ↔ ∀ L, IsAbLK p K L → g ∈ subG p K L := by
  constructor
  · intro hg L hL
    exact Subgroup.topologicalClosure_minimal _ hL.comm (isClosed_subG p K L) hg
  · intro hg
    obtain ⟨M, hM, hMe⟩ := exists_subG_eq (commutator (GK p K)).topologicalClosure
      (Subgroup.isClosed_topologicalClosure _)
    rw [← hMe]
    intro x hx
    have hint : IsIntegral ℚ_[p] x := Algebra.IsIntegral.isIntegral x
    have hfd : FiniteDimensional ℚ_[p] (IntermediateField.adjoin ℚ_[p] {x}) :=
      IntermediateField.adjoin.finiteDimensional hint
    have hle : K ⊔ IntermediateField.adjoin ℚ_[p] {x} ≤ M :=
      sup_le hM (IntermediateField.adjoin_le_iff.2 (Set.singleton_subset_iff.2 hx))
    have hab : IsAbLK p K (K ⊔ IntermediateField.adjoin ℚ_[p] {x}) := by
      refine ⟨le_sup_left, IntermediateField.finiteDimensional_sup _ _, ?_⟩
      refine le_trans ?_ (subG_anti hle)
      rw [hMe]
      exact Subgroup.le_topologicalClosure _
    exact hg _ hab x (le_sup_right (a := K) (IntermediateField.mem_adjoin_simple_self ℚ_[p] x))

theorem toAbK_eq_iff (hK : FiniteDimensional ℚ_[p] K) (g g' : GK p K) :
    toAbK p K g = toAbK p K g' ↔ ∀ L, IsAbLK p K L → g⁻¹ * g' ∈ subG p K L := by
  rw [← mem_closure_commutator_iff hK]
  exact QuotientGroup.eq

theorem exists_of_compatible (hK : FiniteDimensional ℚ_[p] K) (γ : IntermediateField ℚ_[p] (PadicAlgCl p) → GK p K)
    (hγ : ∀ L L', IsAbLK p K L → IsAbLK p K L' → L ≤ L' → (γ L)⁻¹ * γ L' ∈ subG p K L) :
    ∃ g : GK p K, ∀ L, IsAbLK p K L → (γ L)⁻¹ * g ∈ subG p K L := by
  have : Nonempty {L // IsAbLK p K L} := ⟨⟨K, isAbLK_self hK⟩⟩
  let t : {L // IsAbLK p K L} → Set (GK p K) := fun L => {g | (γ L.1)⁻¹ * g ∈ subG p K L.1}
  have hcl : ∀ i, IsClosed (t i) := fun i =>
    (isClosed_subG p K i.1).preimage (continuous_const.mul continuous_id)
  have hmono : ∀ i j : {L // IsAbLK p K L}, i.1 ≤ j.1 → t j ⊆ t i := fun i j hij g hg => by
    have h1 : (γ i.1)⁻¹ * g = ((γ i.1)⁻¹ * γ j.1) * ((γ j.1)⁻¹ * g) := by group
    show (γ i.1)⁻¹ * g ∈ subG p K i.1
    rw [h1]
    exact mul_mem (hγ _ _ i.2 j.2 hij) (subG_anti hij hg)
  obtain ⟨g, hg⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed t
    (fun i j => ⟨⟨i.1 ⊔ j.1, i.2.sup j.2⟩, hmono _ _ le_sup_left, hmono _ _ le_sup_right⟩)
    (fun i => ⟨γ i.1, by show (γ i.1)⁻¹ * γ i.1 ∈ subG p K i.1; rw [inv_mul_cancel]; exact one_mem _⟩)
    (fun i => (hcl i).isCompact) hcl
  exact ⟨g, fun L hL => Set.mem_iInter.1 hg ⟨L, hL⟩⟩

theorem exists_subG_subset (hK : FiniteDimensional ℚ_[p] K) (O : Set (GK p K)) (hO : IsOpen O)
    (h : ((commutator (GK p K)).topologicalClosure : Set (GK p K)) ⊆ O) :
    ∃ L, IsAbLK p K L ∧ (subG p K L : Set (GK p K)) ⊆ O := by
  have : Nonempty {L // IsAbLK p K L} := ⟨⟨K, isAbLK_self hK⟩⟩
  obtain ⟨i, hi⟩ := hO.isClosed_compl.isCompact.elim_directed_family_closed
    (fun L : {L // IsAbLK p K L} => (subG p K L.1 : Set (GK p K))) (fun i => isClosed_subG p K i.1)
    (by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro g ⟨hg1, hg2⟩
      exact hg1 (h ((mem_closure_commutator_iff hK g).2 fun L hL => Set.mem_iInter.1 hg2 ⟨L, hL⟩)))
    (fun i j => ⟨⟨i.1 ⊔ j.1, i.2.sup j.2⟩, subG_anti le_sup_left, subG_anti le_sup_right⟩)
  refine ⟨i.1, i.2, fun g hg => ?_⟩
  by_contra hgO
  exact (Set.eq_empty_iff_forall_notMem.1 hi g) ⟨hgO, hg⟩

theorem exists_coset_subset (hK : FiniteDimensional ℚ_[p] K) (g : GK p K) (W : Set (GKab p K))
    (hW : W ∈ 𝓝 (toAbK p K g)) :
    ∃ L, IsAbLK p K L ∧ ∀ g' : GK p K, g⁻¹ * g' ∈ subG p K L → toAbK p K g' ∈ W := by
  obtain ⟨V, hVW, hV, hgV⟩ := mem_nhds_iff.1 hW
  obtain ⟨L, hL, hsub⟩ := exists_subG_subset hK ((fun h : GK p K => toAbK p K (g * h)) ⁻¹' V)
    (hV.preimage (continuous_toAbK.comp (continuous_const.mul continuous_id))) (fun h hh => by
      show toAbK p K (g * h) ∈ V
      have : toAbK p K (g * h) = toAbK p K g := by
        rw [map_mul, show toAbK p K h = 1 from (QuotientGroup.eq_one_iff h).2 hh, mul_one]
      rw [this]; exact hgV)
  refine ⟨L, hL, fun g' hg' => hVW ?_⟩
  have := hsub hg'
  simpa using this

theorem coset_mem_nhds (hL : IsAbLK p K L) (g : GK p K) :
    toAbK p K '' {g' | g⁻¹ * g' ∈ subG p K L} ∈ 𝓝 (toAbK p K g) := by
  refine (isOpenMap_toAbK _ ?_).mem_nhds ⟨g, ?_, rfl⟩
  · exact (isOpen_subG hL.fin).preimage (continuous_const.mul continuous_id)
  · show g⁻¹ * g ∈ subG p K L
    rw [inv_mul_cancel]; exact one_mem _

theorem continuous_GKab_iff (hK : FiniteDimensional ℚ_[p] K) {X : Type*} [TopologicalSpace X] (f : X → GKab p K) :
    Continuous f ↔ ∀ L, IsAbLK p K L → ∀ x, ∀ᶠ y in 𝓝 x, ∀ g g' : GK p K, toAbK p K g = f x → toAbK p K g' = f y →
      g⁻¹ * g' ∈ subG p K L := by
  constructor
  · intro hf L hL x
    obtain ⟨g₀, hg₀⟩ := toAbK_surjective (f x)
    have hn := coset_mem_nhds hL g₀
    rw [hg₀] at hn
    filter_upwards [hf.continuousAt hn] with y hy g g' hg hg'
    obtain ⟨g₁, hg₁, hg₁y⟩ := hy
    have h1 : g⁻¹ * g₀ ∈ subG p K L := (toAbK_eq_iff hK g g₀).1 (hg.trans hg₀.symm) L hL
    have h2 : g₁⁻¹ * g' ∈ subG p K L := (toAbK_eq_iff hK g₁ g').1 (hg₁y.trans hg'.symm) L hL
    have h3 : g⁻¹ * g' = (g⁻¹ * g₀) * (g₀⁻¹ * g₁) * (g₁⁻¹ * g') := by group
    rw [h3]
    exact mul_mem (mul_mem h1 hg₁) h2
  · intro h
    rw [continuous_iff_continuousAt]
    intro x W hW
    obtain ⟨g₀, hg₀⟩ := toAbK_surjective (f x)
    rw [← hg₀] at hW
    obtain ⟨L, hL, hsub⟩ := exists_coset_subset hK g₀ W hW
    rw [Filter.mem_map]
    filter_upwards [h L hL x] with y hy
    obtain ⟨g₁, hg₁⟩ := toAbK_surjective (f y)
    show f y ∈ W
    rw [← hg₁]
    exact hsub g₁ (hy g₀ g₁ hg₀ hg₁)

theorem denseRange_GKab_iff (hK : FiniteDimensional ℚ_[p] K) {X : Type*} (f : X → GKab p K) :
    DenseRange f ↔ ∀ L, IsAbLK p K L → ∀ g : GK p K, ∃ (x : X) (g' : GK p K), toAbK p K g' = f x ∧
      g'⁻¹ * g ∈ subG p K L := by
  constructor
  · intro hf L hL g
    obtain ⟨x, g', hg', hx⟩ := hf.mem_nhds (coset_mem_nhds hL g)
    refine ⟨x, g', hx, ?_⟩
    have : g'⁻¹ * g = (g⁻¹ * g')⁻¹ := by group
    rw [this]
    exact inv_mem hg'
  · intro h y
    obtain ⟨g, rfl⟩ := toAbK_surjective y
    rw [mem_closure_iff_nhds]
    intro W hW
    obtain ⟨L, hL, hsub⟩ := exists_coset_subset hK g W hW
    obtain ⟨x, g', hg', hx⟩ := h L hL g
    refine ⟨f x, ?_, x, rfl⟩
    rw [← hg']
    refine hsub g' ?_
    have : g⁻¹ * g' = (g'⁻¹ * g)⁻¹ := by group
    rw [this]
    exact inv_mem hx

theorem exists_hom_GKab (hK : FiniteDimensional ℚ_[p] K) {A : Type*} [Group A] (γ : IntermediateField ℚ_[p] (PadicAlgCl p) → A → GK p K)
    (hmul : ∀ L, IsAbLK p K L → ∀ a b, (γ L (a * b))⁻¹ * (γ L a * γ L b) ∈ subG p K L)
    (hγ : ∀ L L', IsAbLK p K L → IsAbLK p K L' → L ≤ L' → ∀ a, (γ L a)⁻¹ * γ L' a ∈ subG p K L) :
    ∃ f : A →* GKab p K, ∀ L, IsAbLK p K L → ∀ (a : A) (g : GK p K), toAbK p K g = f a →
      (γ L a)⁻¹ * g ∈ subG p K L := by
  have hex : ∀ a, ∃ g : GK p K, ∀ L, IsAbLK p K L → (γ L a)⁻¹ * g ∈ subG p K L := fun a =>
    exists_of_compatible hK (fun L => γ L a) fun L L' hL hL' hle => hγ L L' hL hL' hle a
  choose s hs using hex
  refine ⟨MonoidHom.mk' (fun a => toAbK p K (s a)) fun a b => ?_, fun L hL a g hg => ?_⟩
  · rw [← map_mul, toAbK_eq_iff hK]
    intro L hL
    have := hL.normal
    rw [← QuotientGroup.eq, QuotientGroup.mk_mul, ← QuotientGroup.eq.2 (hs a L hL), ← QuotientGroup.eq.2 (hs b L hL),
      ← QuotientGroup.eq.2 (hs (a * b) L hL), ← QuotientGroup.mk_mul]
    exact QuotientGroup.eq.2 (hmul L hL a b)
  · have h1 : (s a)⁻¹ * g ∈ subG p K L := (toAbK_eq_iff hK (s a) g).1 hg.symm L hL
    have h2 : (γ L a)⁻¹ * g = ((γ L a)⁻¹ * s a) * ((s a)⁻¹ * g) := by group
    rw [h2]
    exact mul_mem (hs a L hL) h1

end ReciprocityTheory.DiscreteGroups.LocalClassField
