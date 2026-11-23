import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Formalism.HermitianLattices.HermitianLatticesProofs.DualLattice
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WittExtensionTotallyDefiniteHermitianStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLatticeDiscriminantOrderNeZeroUnimodulaStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatticeQuotientGensAndIntermediateCountStatement

open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

namespace GlobalTheory.Mass.PrimDisc

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

omit [FiniteDimensional K V] in
theorem mem_dual (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) (x : V) :
    x ∈ dual h L ↔ ∀ y ∈ L, h y x ∈ (1 : Submodule (𝓞 K) K) := by
  simp [dual, Formalism.E.hdual, Submodule.mem_iInf]

omit [NumberField K] in
theorem star_range (r : 𝓞 K) : star (algebraMap (𝓞 K) K r) ∈ Set.range (algebraMap (𝓞 K) K) :=
  ⟨RingOfIntegers.mapRingHom (starRingEnd K) r, rfl⟩

omit [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem nondeg (h : V →ₗ⋆[K] V →ₗ[K] K) (hp : PD h) : h.Nondegenerate := by
  let φ : K →+* ℂ := (IsAlgClosed.lift : K →ₐ[ℚ] ℂ).toRingHom
  constructor
  · intro x hx
    by_contra h0
    have := hp φ x h0
    rw [hx x] at this
    simp at this
  · intro x hx
    by_contra h0
    have := hp φ x h0
    rw [hx x] at this
    simp at this

omit [StarRing K] [FiniteDimensional K V] in
theorem lat_map (A : Submodule K V) (p : V →ₗ[K] A) (hp : Function.Surjective p)
    (N : Submodule (𝓞 K) V) (hN : Submodule.IsLattice K N) :
    Submodule.IsLattice K (N.map (p.restrictScalars (𝓞 K))) := by
  refine ⟨hN.fg.map _, ?_⟩
  have e : ((N.map (p.restrictScalars (𝓞 K)) : Submodule (𝓞 K) A) : Set A) = p '' (N : Set V) := rfl
  rw [e, ← Submodule.map_span, hN.span_eq_top, Submodule.map_top, LinearMap.range_eq_top.2 hp]

theorem dual_latIn (h : V →ₗ⋆[K] V →ₗ[K] K) (hs : h.IsSymm) (hp : PD h) (A : Submodule K V)
    (hsA : (hRes h A).IsSymm) (hpA : PD (hRes h A)) (p : V →ₗ[K] A) (hsur : Function.Surjective p)
    (hh : ∀ (x : V) (a : A), h (p x : V) (a : V) = h x a)
    (L : Submodule (𝓞 K) V) (hL : IsIntLat h L) :
    IsIntLat (hRes h A) (latIn A L) ∧
      dual (hRes h A) (latIn A L) = (dual h L).map (p.restrictScalars (𝓞 K)) := by
  obtain ⟨h1, h2, -⟩ := dualLattice (𝓞 K) K V h hs (nondeg h hp) star_range L hL.1
  obtain ⟨k1, k2, -⟩ := dualLattice (𝓞 K) K A (hRes h A) hsA (nondeg _ hpA) star_range _
    (lat_map A p hsur _ h1)
  have e : dual (hRes h A) ((dual h L).map (p.restrictScalars (𝓞 K))) = latIn A L := by
    ext a
    have : a ∈ latIn A L ↔ (a : V) ∈ dual h (dual h L) := by rw [h2]; rfl
    rw [this, mem_dual, mem_dual]
    constructor
    · intro H y hy
      rw [← hh]
      exact H (p y) ⟨y, hy, rfl⟩
    · rintro H _ ⟨y, hy, rfl⟩
      have := H y hy
      rw [← hh] at this
      exact this
  rw [e] at k1 k2
  exact ⟨⟨k1, fun x hx y hy => hL.2 x hx y hy⟩, k2⟩

omit [StarRing K] [FiniteDimensional K V] [NumberField K] in
theorem idx_swap (A B : Submodule K V) (p : V →ₗ[K] A) (q : V →ₗ[K] B)
    (hpq : ∀ x, (p x : V) + q x = x) (L : Submodule (𝓞 K) V) :
    idxN (L.map (p.restrictScalars (𝓞 K))) (latIn A L) =
      idxN (L.map (q.restrictScalars (𝓞 K))) (latIn B L) := by
  unfold idxN
  rw [Submodule.map_toAddSubgroup, Submodule.map_toAddSubgroup, ← AddSubgroup.relIndex_comap,
    ← AddSubgroup.relIndex_comap, ← AddSubgroup.inf_relIndex_right]
  conv_rhs => rw [← AddSubgroup.inf_relIndex_right]
  congr 1
  ext x
  change ((p x : V) ∈ L ∧ x ∈ L) ↔ ((q x : V) ∈ L ∧ x ∈ L)
  refine and_congr_left fun hx => ?_
  rw [← hpq x] at hx
  exact ⟨fun H => (L.add_mem_iff_right H).1 hx, fun H => (L.add_mem_iff_left H).1 hx⟩

omit [StarRing K] [FiniteDimensional K V] [NumberField K] in
theorem idx_map_dvd (A : Submodule K V) (p : V →ₗ[K] A) (L N : Submodule (𝓞 K) V) :
    idxN (N.map (p.restrictScalars (𝓞 K))) (L.map (p.restrictScalars (𝓞 K))) ∣ idxN N L := by
  unfold idxN
  rw [Submodule.map_toAddSubgroup _ N, ← AddSubgroup.relIndex_comap]
  exact AddSubgroup.relIndex_dvd_of_le_left _ fun x hx => ⟨x, hx, rfl⟩

omit [StarRing K] [FiniteDimensional K V] [NumberField K] [Module K V] [IsScalarTower (𝓞 K) K V] in
theorem idx_mul (A B C : Submodule (𝓞 K) V) (h1 : A ≤ B) (h2 : B ≤ C) :
    idxN B A * idxN C B = idxN C A :=
  AddSubgroup.relIndex_mul_relIndex _ _ _ h1 h2

omit [StarRing K] [FiniteDimensional K V] [NumberField K] in
theorem latIn_le (A : Submodule K V) (p : V →ₗ[K] A) (hp : ∀ a : A, p a = a)
    (L : Submodule (𝓞 K) V) : latIn A L ≤ L.map (p.restrictScalars (𝓞 K)) :=
  fun a ha => ⟨a, ha, hp a⟩

omit [StarRing K] [FiniteDimensional K V] [NumberField K] in
theorem gens_swap (A B : Submodule K V) (p : V →ₗ[K] A) (q : V →ₗ[K] B)
    (hp : ∀ a : A, p a = a) (hpq : ∀ x, (p x : V) + q x = x) (L : Submodule (𝓞 K) V) (t : Finset B)
    (ht : L.map (q.restrictScalars (𝓞 K)) = latIn B L ⊔ Submodule.span (𝓞 K) (t : Set B)) :
    ∃ t' : Finset A, t'.card ≤ t.card ∧
      L.map (p.restrictScalars (𝓞 K)) = latIn A L ⊔ Submodule.span (𝓞 K) (t' : Set A) := by
  have hl : ∀ b : t, ∃ l ∈ L, q l = b := fun b => by
    have : (b : B) ∈ L.map (q.restrictScalars (𝓞 K)) := by
      rw [ht]
      exact Submodule.mem_sup_right (Submodule.subset_span b.2)
    exact this
  choose f hf1 hf2 using hl
  refine ⟨Finset.univ.image fun b => p (f b), Finset.card_image_le.trans (by simp), ?_⟩
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    have hq : q x ∈ latIn B L ⊔ Submodule.span (𝓞 K) (t : Set B) := ht ▸ ⟨x, hx, rfl⟩
    have e : (t : Set B) = (q.restrictScalars (𝓞 K)) '' Set.range f := by
      ext b
      constructor
      · intro hb
        exact ⟨f ⟨b, hb⟩, ⟨_, rfl⟩, hf2 _⟩
      · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
        have : q (f c) ∈ t := by rw [hf2]; exact c.2
        exact this
    rw [e, ← Submodule.map_span] at hq
    obtain ⟨s, hs, _, ⟨y, hy, rfl⟩, hsy⟩ := Submodule.mem_sup.1 hq
    have hyL : y ∈ L := (Submodule.span_le.2 (by rintro _ ⟨c, rfl⟩; exact hf1 c)) hy
    refine Submodule.mem_sup.2 ⟨p (x - y), ?_, p y, ?_, by simp⟩
    · have e1 : q (x - y) = s := by
        rw [map_sub, ← hsy]; simp
      have e2 := hpq (x - y)
      rw [e1] at e2
      change (p (x - y) : V) ∈ L
      rw [eq_sub_of_add_eq e2]
      exact L.sub_mem (L.sub_mem hx hyL) hs
    · have : p y ∈ (Submodule.span (𝓞 K) (Set.range f)).map (p.restrictScalars (𝓞 K)) := ⟨y, hy, rfl⟩
      rw [Submodule.map_span, ← Set.range_comp] at this
      simpa [Function.comp_def] using this
  · refine sup_le (latIn_le A p hp L) (Submodule.span_le.2 ?_)
    intro a ha
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ] at ha
    obtain ⟨b, rfl⟩ := ha
    exact ⟨f b, hf1 b, rfl⟩

theorem main : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → PD h → ∀ (L : Submodule (𝓞 K) V) (U : Submodule K V) (e : ℕ), IsIntLat h L → (∃ t : Finset V, t.card ≤ e ∧ dual h L = L ⊔ Submodule.span (𝓞 K) (t : Set _)) → IsIntLat (hRes h U) (latIn U L) ∧ IsIntLat (hRes h (perp h U)) (latIn (perp h U) L) ∧ discN (hRes h (perp h U)) (latIn (perp h U) L) ≤ discN (hRes h U) (latIn U L) * discN h L ∧ (∃ t : Finset ↥U, t.card ≤ (Module.finrank K (perp h U) + e) ∧ dual (hRes h U) (latIn U L) = (latIn U L) ⊔ Submodule.span (𝓞 K) (t : Set _)) := by
  intro K V _ _ _ _ _ _ _ _ h hK hs hp L U e hL ⟨t, hte, ht⟩
  obtain ⟨hc, hsU, hpU, -⟩ := (GlobalTheory.T.witt_extension_totally_definite_hermitian K V h hK hs hp).2 U
  obtain ⟨-, hsW, hpW, -⟩ := (GlobalTheory.T.witt_extension_totally_definite_hermitian K V h hK hs hp).2 (perp h U)
  set W := perp h U with hW
  have horth : ∀ (u : U) (w : W), h (u : V) (w : V) = 0 := fun u w => by
    have := w.2
    simp only [hW, perp, Submodule.mem_iInf, LinearMap.mem_ker] at this
    exact this u u.2
  have horth' : ∀ (u : U) (w : W), h (w : V) (u : V) = 0 := fun u w => by
    rw [← hs.eq, horth, map_zero]
  let p : V →ₗ[K] U := U.projectionOnto W hc
  let q : V →ₗ[K] W := W.projectionOnto U hc.symm
  have hpq : ∀ x, (p x : V) + q x = x := Submodule.projection_add_projection_eq_self hc
  have hp1 : ∀ a : U, p a = a := Submodule.projectionOnto_apply_left hc
  have hq1 : ∀ a : W, q a = a := Submodule.projectionOnto_apply_left hc.symm
  obtain ⟨iU, dU⟩ := dual_latIn h hs hp U hsU hpU p (Submodule.projectionOnto_surjective hc)
    (fun x a => by conv_rhs => rw [← hpq x, map_add, LinearMap.add_apply, horth', add_zero]) L hL
  obtain ⟨iW, dW⟩ := dual_latIn h hs hp W hsW hpW q (Submodule.projectionOnto_surjective hc.symm)
    (fun x a => by conv_rhs => rw [← hpq x, map_add, LinearMap.add_apply, horth, zero_add]) L hL
  have hLd : L ≤ dual h L := by rw [ht]; exact le_sup_left
  have nL := (GlobalTheory.T.hermitianLatticeDiscriminantOrder_ne_zero_unimodular K V h hK hs (nondeg h hp) L hL).1
  have nU := (GlobalTheory.T.hermitianLatticeDiscriminantOrder_ne_zero_unimodular K U _ hK hsU (nondeg _ hpU) _ iU).1
  have mU := idx_mul _ _ _ (latIn_le U p hp1 L) (Submodule.map_mono hLd)
  have mW := idx_mul _ _ _ (latIn_le W q hq1 L) (Submodule.map_mono hLd)
  have sw := idx_swap U W p q hpq L
  have dvU : idxN (L.map (q.restrictScalars (𝓞 K))) (latIn W L) ∣ discN (hRes h U) (latIn U L) := by
    rw [discN, dU, ← mU, sw]
    exact dvd_mul_right _ _
  refine ⟨iU, iW, ?_, ?_⟩
  · rw [discN, dW, ← mW]
    exact Nat.mul_le_mul (Nat.le_of_dvd (Nat.pos_of_ne_zero nU) dvU)
      (Nat.le_of_dvd (Nat.pos_of_ne_zero nL) (idx_map_dvd W q L _))
  · obtain ⟨s, hs1, hs2⟩ := (GlobalTheory.T.lattice_quotient_gens_and_intermediate_count K W _ _ (latIn_le W q hq1 L)
      (ne_zero_of_dvd_ne_zero nU dvU)).1 (hL.1.fg.map _)
    obtain ⟨s', h1, h2⟩ := gens_swap U W p q hp1 hpq L s hs2
    refine ⟨s' ∪ t.image p, (Finset.card_union_le _ _).trans
      (Nat.add_le_add (h1.trans hs1) (Finset.card_image_le.trans hte)), ?_⟩
    rw [dU, ht, Submodule.map_sup, h2, Submodule.map_span, Finset.coe_union, Submodule.span_union,
      sup_assoc, Finset.coe_image]
    rfl

end GlobalTheory.Mass.PrimDisc
