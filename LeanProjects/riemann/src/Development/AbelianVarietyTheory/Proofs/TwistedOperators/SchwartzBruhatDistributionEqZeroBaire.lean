import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHilbertSchmidtOfFiniteDimensional

open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL

namespace GlobalTheory.BaireDistribution

section General

variable {X : Type} [TopologicalSpace X]

theorem indicator_mem {C : Set X} (hC : IsClopen C) (φ : SB X) : C.indicator φ.1 ∈ SB X := by
  refine ⟨?_, φ.2.2.mono fun x hx => ?_⟩
  · rw [IsLocallyConstant.iff_exists_open]
    intro x
    by_cases hx : x ∈ C
    · obtain ⟨U, hU, hxU, h⟩ := φ.2.1.exists_open x
      exact ⟨C ∩ U, hC.2.inter hU, ⟨hx, hxU⟩, fun y hy => by
        rw [Set.indicator_of_mem hy.1, Set.indicator_of_mem hx, h y hy.2]⟩
    · exact ⟨Cᶜ, hC.1.isOpen_compl, hx, fun y hy => by
        rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]⟩
  · rw [Set.support_indicator] at hx
    exact hx.2

theorem isCompact_support (φ : SB X) : IsCompact (Function.support φ.1) := by
  have h : IsClosed (Function.support φ.1) := by
    have := (φ.2.1 {0}).isClosed_compl
    convert this using 1
    ext x
    simp
  have h2 := φ.2.2.isCompact
  rwa [tsupport, h.closure_eq] at h2

theorem glue (D : SB X →ₗ[ℂ] ℂ) (𝒞 : Set X → Prop) (hcl : ∀ C, 𝒞 C → IsClopen C) (h0 : 𝒞 ∅)
    (hu : ∀ C C', 𝒞 C → 𝒞 C' → 𝒞 (C ∪ C')) (hi : ∀ C C', 𝒞 C → 𝒞 C' → 𝒞 (C ∩ C'))
    (hd : ∀ C C', 𝒞 C → 𝒞 C' → 𝒞 (C \ C')) (φ : SB X)
    (h : ∀ x ∈ Function.support φ.1, ∃ C, 𝒞 C ∧ x ∈ C ∧
      ∀ C', 𝒞 C' → C' ⊆ C → ∀ ψ : SB X, ψ.1 = C'.indicator φ.1 → D ψ = 0) : D φ = 0 := by
  have key : ∃ C, 𝒞 C ∧ Function.support φ.1 ⊆ C ∧
      ∀ C', 𝒞 C' → C' ⊆ C → ∀ ψ : SB X, ψ.1 = C'.indicator φ.1 → D ψ = 0 := by
    refine (isCompact_support φ).induction_on (p := fun s => ∃ C, 𝒞 C ∧ s ⊆ C ∧
      ∀ C', 𝒞 C' → C' ⊆ C → ∀ ψ : SB X, ψ.1 = C'.indicator φ.1 → D ψ = 0) ?_ ?_ ?_ ?_
    · refine ⟨∅, h0, subset_rfl, fun C' _ hC' ψ hψ => ?_⟩
      have : ψ = 0 := Subtype.ext (by rw [hψ, Set.subset_empty_iff.1 hC']; ext; simp)
      rw [this, map_zero]
    · rintro s t hst ⟨C, h1, h2, h3⟩
      exact ⟨C, h1, hst.trans h2, h3⟩
    · rintro s t ⟨C, h1, h2, h3⟩ ⟨E, e1, e2, e3⟩
      refine ⟨C ∪ E, hu _ _ h1 e1, Set.union_subset_union h2 e2, fun C' hC' hs ψ hψ => ?_⟩
      have a1 := h3 (C' ∩ C) (hi _ _ hC' h1) Set.inter_subset_right
        ⟨_, indicator_mem (hcl _ (hi _ _ hC' h1)) φ⟩ rfl
      have a2 := e3 (C' \ C) (hd _ _ hC' h1) (fun x hx => (hs hx.1).resolve_left hx.2)
        ⟨_, indicator_mem (hcl _ (hd _ _ hC' h1)) φ⟩ rfl
      have : ψ = ⟨_, indicator_mem (hcl _ (hi _ _ hC' h1)) φ⟩ +
          ⟨_, indicator_mem (hcl _ (hd _ _ hC' h1)) φ⟩ := by
        apply Subtype.ext
        rw [hψ]
        ext x
        by_cases a : x ∈ C' <;> by_cases b : x ∈ C <;> simp [Set.indicator, a, b]
      rw [this, map_add, a1, a2, add_zero]
    · intro x hx
      obtain ⟨C, h1, h2, h3⟩ := h x hx
      exact ⟨C, mem_nhdsWithin_of_mem_nhds ((hcl _ h1).2.mem_nhds h2), C, h1, subset_rfl, h3⟩
  obtain ⟨C, h1, h2, h3⟩ := key
  exact h3 C h1 subset_rfl φ (Set.indicator_eq_self.2 h2).symm

end General

section Group

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem isClopen_of_invariant {K : Subgroup G} (hK : IsOpen (K : Set G)) {C : Set G}
    (hC : ∀ a ∈ K, ∀ b ∈ K, ∀ g, a * g * b ∈ C ↔ g ∈ C) : IsClopen C := by
  have aux : ∀ S : Set G, (∀ a ∈ K, ∀ g ∈ S, a * g ∈ S) → IsOpen S := by
    intro S hS
    rw [isOpen_iff_forall_mem_open]
    intro g hg
    refine ⟨(fun y => y * g⁻¹) ⁻¹' K, fun y hy => ?_, hK.preimage (by fun_prop), by simp⟩
    simpa using hS _ hy g hg
  refine ⟨isOpen_compl_iff.1 (aux _ fun a ha g hg h => hg ?_), aux _ fun a ha g hg => ?_⟩
  · exact (hC a ha 1 K.one_mem g).1 (by simpa using h)
  · simpa using (hC a ha 1 K.one_mem g).2 hg

omit [TopologicalSpace G] [IsTopologicalGroup G] in

theorem doubleCoset_invariant (K : Subgroup G) (x : G) : ∀ a ∈ K, ∀ b ∈ K, ∀ g,
    a * g * b ∈ {g : G | ∃ a ∈ K, ∃ b ∈ K, g = a * x * b} ↔
      g ∈ {g : G | ∃ a ∈ K, ∃ b ∈ K, g = a * x * b} := by
  intro a ha b hb g
  constructor
  · rintro ⟨c, hc, d, hd, h⟩
    refine ⟨a⁻¹ * c, K.mul_mem (K.inv_mem ha) hc, d * b⁻¹, K.mul_mem hd (K.inv_mem hb), ?_⟩
    have : g = a⁻¹ * (a * g * b) * b⁻¹ := by group
    rw [this, h]; group
  · rintro ⟨c, hc, d, hd, rfl⟩
    exact ⟨a * c, K.mul_mem ha hc, d * b, K.mul_mem hd hb, by group⟩

theorem exists_nhds_invariant (φ : SB G) :
    ∃ U ∈ nhds (1 : G), ∀ a ∈ U, ∀ b ∈ U, ∀ g, φ.1 (a * g * b) = φ.1 g := by
  have h1 := GlobalTheory.OpTrace.isOpen_leftStabilizer φ.2.1 φ.2.2
  have h2 := GlobalTheory.OpTrace.isOpen_leftStabilizer (f := fun g => φ.1 g⁻¹)
    (φ.2.1.comp_continuous continuous_inv) (φ.2.2.comp_homeomorph (Homeomorph.inv G))
  refine ⟨_, (h1.inter h2).mem_nhds ⟨Subgroup.one_mem _, Subgroup.one_mem _⟩,
    fun a ha b hb g => ?_⟩
  have e1 : ∀ g, φ.1 (a * g) = φ.1 g := ha.1
  have e2 : ∀ g, φ.1 (b * g)⁻¹ = φ.1 g⁻¹ := hb.2
  rw [mul_assoc, e1]
  simpa using (e2 (g * b)⁻¹).symm

end Group

theorem eq_zero : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] (ι : Type) [Countable ι] (K : ι → ℕ → Subgroup G), (∀ i m, IsOpen (K i m : Set G) ∧ IsCompact (K i m : Set G)) → (∀ i, ∀ U ∈ nhds (1 : G), ∃ m, (K i m : Set G) ⊆ U) → ∀ D : SB G →ₗ[ℂ] ℂ, (∀ x : G, ∃ i, ∀ (m : ℕ) (φ : SB G), φ.1 = Set.indicator {g : G | ∃ a ∈ K i m, ∃ b ∈ K i m, g = a * x * b} (fun _ => (1 : ℂ)) → D φ = 0) → D = 0 := by
  intro G _ _ _ _ _ ι _ K hK hb D hD
  let O : Set G := {x | ∃ W, IsOpen W ∧ x ∈ W ∧ ∀ φ : SB G, Function.support φ.1 ⊆ W → D φ = 0}
  have hO : IsOpen O := by
    rw [isOpen_iff_forall_mem_open]
    rintro x ⟨W, h1, h2, h3⟩
    exact ⟨W, fun y hy => ⟨W, h1, hy, h3⟩, h1, h2⟩
  have h1 : ∀ φ : SB G, Function.support φ.1 ⊆ O → D φ = 0 := by
    intro φ hφ
    refine glue D IsClopen (fun _ h => h) isClopen_empty (fun _ _ => IsClopen.union)
      (fun _ _ => IsClopen.inter) (fun _ _ => IsClopen.diff) φ fun x hx => ?_
    obtain ⟨W, w1, w2, w3⟩ := hφ hx
    obtain ⟨i, -⟩ := hD x
    obtain ⟨m, hm⟩ := hb i ((fun y => x * y) ⁻¹' W)
      ((w1.preimage (by fun_prop)).mem_nhds (by simpa using w2))
    refine ⟨(fun y => x⁻¹ * y) ⁻¹' K i m, IsClopen.preimage
      ⟨(K i m).isClosed_of_isOpen (hK i m).1, (hK i m).1⟩ (by fun_prop), by simp,
      fun C' _ hC' ψ hψ => w3 ψ fun y hy => ?_⟩
    rw [hψ, Set.support_indicator] at hy
    simpa using hm (hC' hy.1)
  suffices hall : ∀ x, x ∈ O from LinearMap.ext fun φ => h1 φ fun x _ => hall x
  by_contra hne
  push_neg at hne
  let Z : ι → Set G := fun i => {x | ∀ (m : ℕ) (φ : SB G), φ.1 =
    Set.indicator {g : G | ∃ a ∈ K i m, ∃ b ∈ K i m, g = a * x * b} (fun _ => (1 : ℂ)) → D φ = 0}
  haveI : LocallyCompactSpace (Oᶜ : Set G) := hO.isClosed_compl.locallyCompactSpace
  haveI : Nonempty (Oᶜ : Set G) := ⟨⟨hne.choose, hne.choose_spec⟩⟩
  obtain ⟨i, y, hy⟩ := nonempty_interior_of_iUnion_of_closed (X := (Oᶜ : Set G))
    (f := fun i => Subtype.val ⁻¹' closure (Z i))
    (fun i => isClosed_closure.preimage continuous_subtype_val)
    (Set.eq_univ_of_forall fun x => by
      obtain ⟨i, hi⟩ := hD x.1
      exact Set.mem_iUnion.2 ⟨i, subset_closure hi⟩)
  obtain ⟨t, t1, t2, t3⟩ := mem_interior.1 hy
  obtain ⟨W, hW, rfl⟩ := isOpen_induced_iff.1 t2
  refine y.2 ⟨W, hW, t3, fun φ hφ => ?_⟩
  obtain ⟨U, hU, hinv⟩ := exists_nhds_invariant φ
  obtain ⟨m, hm⟩ := hb i U hU
  refine glue D (fun C => ∀ a ∈ K i m, ∀ b ∈ K i m, ∀ g, a * g * b ∈ C ↔ g ∈ C)
    (fun C hC => isClopen_of_invariant (hK i m).1 hC) (by simp)
    (fun C C' h h' a ha b hb g => or_congr (h a ha b hb g) (h' a ha b hb g))
    (fun C C' h h' a ha b hb g => and_congr (h a ha b hb g) (h' a ha b hb g))
    (fun C C' h h' a ha b hb g => and_congr (h a ha b hb g) (not_congr (h' a ha b hb g))) φ
    fun x hx => ⟨_, doubleCoset_invariant (K i m) x,
      ⟨1, Subgroup.one_mem _, 1, Subgroup.one_mem _, by simp⟩, fun C hC hs ψ hψ => ?_⟩
  have hval : ∀ g ∈ C, φ.1 g = φ.1 x := fun g hg => by
    obtain ⟨a, ha, b, hb, rfl⟩ := hs hg
    exact hinv a (hm ha) b (hm hb) x
  by_cases hCO : C ⊆ O
  · refine h1 ψ fun g hg => hCO ?_
    rw [hψ, Set.support_indicator] at hg
    exact hg.1
  obtain ⟨w, w1, w2⟩ := Set.not_subset.1 hCO
  have w3 : w ∈ closure (Z i) := t1 (show (⟨w, w2⟩ : (Oᶜ : Set G)) ∈ Subtype.val ⁻¹' W from
    hφ (show φ.1 w ≠ 0 by rw [hval w w1]; exact hx))
  obtain ⟨z, z1, z2⟩ := mem_closure_iff.1 w3 C (isClopen_of_invariant (hK i m).1 hC).2 w1
  have hCz : C = {g : G | ∃ a ∈ K i m, ∃ b ∈ K i m, g = a * z * b} := by
    ext g
    constructor
    · intro hg
      obtain ⟨a, ha, b, hb, rfl⟩ := hs hg
      obtain ⟨c, hc, d, hd, rfl⟩ := hs z1
      exact ⟨a * c⁻¹, mul_mem ha (inv_mem hc), d⁻¹ * b, mul_mem (inv_mem hd) hb, by group⟩
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact (hC a ha b hb z).2 z1
  have hx' : φ.1 x ≠ 0 := hx
  have := z2 m ((φ.1 x)⁻¹ • ψ) (by
    rw [← hCz, Submodule.coe_smul, hψ]
    ext g
    by_cases hg : g ∈ C
    · simp [Set.indicator_of_mem hg, hval g hg, hx']
    · simp [Set.indicator_of_notMem hg])
  simpa [hx'] using this

end GlobalTheory.BaireDistribution
