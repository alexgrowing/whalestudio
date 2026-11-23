import ReciprocityTheory.GroupCohomology.CupConnRightStatement
import ReciprocityTheory.GroupCohomology.DEqZeroOfMemB

namespace ReciprocityTheory.Coh

open ReciprocityTheory.Gal

universe u

section AdmAux

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

private theorem pair_hom_f_coe_of_id {M M' : TRep R G} (P : Pair M M') (h : P.φ = MonoidHom.id G) (n : ℕ)
    (x : M.coch.X n) : (P.hom.f n x).1 = fun g => P.u (x.1 g) := by
  funext g
  show P.u (x.1 fun i => P.φ (g i)) = P.u (x.1 g)
  rw [h]
  rfl

private def mkC (M : TRep R G) (n : ℕ) (f : (Fin n → G) → M.V) (hf : Continuous f) : M.coch.X n := ⟨f, hf⟩

@[simp] private theorem mkC_val (M : TRep R G) (n : ℕ) (f : (Fin n → G) → M.V) (hf : Continuous f) :
    (mkC M n f hf).1 = f := rfl

private theorem coch_cont {M : TRep R G} {n : ℕ} (x : M.coch.X n) : Continuous x.1 := x.2

end AdmAux

theorem admissibility_holds : AdmStatement.{u} := by
  intro R _ G _ _ _ A B C i p h
  refine ⟨fun n x y hxy => ?_, fun n => ?_, fun n => ?_⟩
  · refine Subtype.ext (funext fun g => h.emb.injective ?_)
    have hg := congrArg (fun z => z.1 g) hxy
    simp only [pair_hom_f_coe_of_id i h.i_id] at hg
    exact hg
  · intro y
    constructor
    · intro hy
      have hy' : ∀ g, p.u (y.1 g) = 0 := fun g => by
        have hg := congrArg (fun z => z.1 g) hy
        simp only [pair_hom_f_coe_of_id p h.p_id] at hg
        exact hg
      have hex : ∀ g, ∃ a, i.u a = y.1 g := fun g => (h.exact (y.1 g)).1 (hy' g)
      choose x hx using hex
      have hxc : Continuous x := by
        rw [h.emb.continuous_iff]
        have hfx : (i.u ∘ x) = y.1 := funext hx
        rw [hfx]
        exact y.2
      exact ⟨⟨x, hxc⟩, Subtype.ext ((pair_hom_f_coe_of_id i h.i_id n _).trans (funext hx))⟩
    · rintro ⟨x, rfl⟩
      refine Subtype.ext ((pair_hom_f_coe_of_id p h.p_id n _).trans ?_)
      funext g
      rw [pair_hom_f_coe_of_id i h.i_id]
      exact (h.exact (i.u (x.1 g))).2 ⟨x.1 g, rfl⟩
  · intro c
    obtain ⟨s, hs, hps⟩ := h.sec
    exact ⟨⟨s ∘ c.1, hs.comp c.2⟩,
      Subtype.ext ((pair_hom_f_coe_of_id p h.p_id n _).trans (funext fun g => hps _))⟩

theorem limRep_holds : LimRepStatement.{u} := by
  intro R _ G _ _ _ A _ τ L π hτ hemb hlift
  have cτ : ∀ m n (x : (A (m + 1)).coch.X n), ((τ m).hom.f n x).1 = fun g => (τ m).u (x.1 g) :=
    fun m n x => pair_hom_f_coe_of_id (τ m) (hτ m).1 n x
  have cπ : ∀ m n (x : L.coch.X n), ((π m).hom.f n x).1 = fun g => (π m).u (x.1 g) :=
    fun m n x => pair_hom_f_coe_of_id (π m) (hτ m).2.1 n x
  refine ⟨fun m n c => ?_, fun m n x => ?_, fun n x hx => ?_, fun n y hy => ?_⟩
  · choose s hs using (hτ m).2.2.1
    exact ⟨⟨s ∘ c.1, (continuous_of_discreteTopology (f := s)).comp c.2⟩,
      Subtype.ext ((cτ m n _).trans (funext fun g => hs _))⟩
  · refine Subtype.ext ?_
    rw [cτ, cπ, cπ]
    funext g
    exact (hτ m).2.2.2 _
  · refine Subtype.ext (funext fun g => ?_)
    apply hemb.injective
    funext m
    have hg := congrArg (fun z => z.1 g) (hx m)
    simp only [cπ] at hg
    refine hg.trans ?_
    show (0 : (A m).V) = (π m).u 0
    rw [map_zero]
  · have hy' : ∀ g m, (τ m).u ((y (m + 1)).1 g) = (y m).1 g := fun g m => by
      have hg := congrArg (fun z => z.1 g) (hy m)
      simp only [cτ] at hg
      exact hg
    choose x hx using fun g => hlift (fun m => (y m).1 g) (hy' g)
    have hxc : Continuous x := by
      rw [hemb.continuous_iff]
      have hfx : ((fun (x : L.V) m => (π m).u x) ∘ x) = fun g m => (y m).1 g :=
        funext fun g => funext (hx g)
      rw [hfx]
      exact continuous_pi fun m => by exact (y m).2
    exact ⟨⟨x, hxc⟩, fun m => Subtype.ext ((cπ m n _).trans (funext fun g => hx g m))⟩

section ColimAux

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

private theorem exists_upper_range {ι V : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    (J : ι → Set V) (hJ : ∀ a b, a ≤ b → J a ⊆ J b) (hcov : ∀ x, ∃ a, x ∈ J a) (S : Set V)
    (hS : S.Finite) (a0 : ι) : ∃ b, a0 ≤ b ∧ S ⊆ J b := by
  classical
  choose a ha using hcov
  obtain ⟨z, hz⟩ := (directed_id : Directed (· ≤ ·) (id : ι → ι)).finset_le
    (insert a0 (hS.toFinset.image a))
  refine ⟨z, hz a0 (Finset.mem_insert_self _ _), fun x hx => ?_⟩
  exact hJ _ _ (hz (a x) (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (hS.mem_toFinset.2 hx)))) (ha x)

private theorem pair_hom_f_inj_of_id {M M' : TRep R G} (P : Pair M M') (h : P.φ = MonoidHom.id G)
    (hu : Function.Injective P.u) (n : ℕ) : Function.Injective (P.hom.f n) := by
  intro x y hxy
  apply Subtype.ext
  funext g
  have hg : (P.hom.f n x).1 g = (P.hom.f n y).1 g := by rw [hxy]
  rw [pair_hom_f_coe_of_id P h, pair_hom_f_coe_of_id P h] at hg
  exact hu hg

private theorem pair_hom_lift_of_id {M M' : TRep R G} [DiscreteTopology M'.V] (P : Pair M M')
    (h : P.φ = MonoidHom.id G) (n : ℕ) (c : M'.coch.X n) (hc : Set.range c.1 ⊆ Set.range P.u) :
    ∃ c' : M.coch.X n, P.hom.f n c' = c := by
  classical
  let s : M'.V → M.V := fun y => if hy : y ∈ Set.range P.u then hy.choose else 0
  have hs : ∀ y ∈ Set.range P.u, P.u (s y) = y := fun y hy => by
    simp only [s, dif_pos hy]
    exact hy.choose_spec
  let c' : M.coch.X n := ⟨s ∘ c.1, (continuous_of_discreteTopology (f := s)).comp c.2⟩
  refine ⟨c', ?_⟩
  apply Subtype.ext
  refine (pair_hom_f_coe_of_id P h n c').trans ?_
  funext g
  exact hs _ (hc ⟨g, rfl⟩)

private theorem coch_range_finite [CompactSpace G] {M : TRep R G} [DiscreteTopology M.V] {n : ℕ}
    (c : M.coch.X n) : (Set.range c.1).Finite :=
  (isCompact_range (coch_cont c)).finite_of_discrete

end ColimAux

theorem colim_holds : ColimStatement.{u} := by
  intro R _ G _ _ _ _ ι _ _ _ A L _ _ j t hj ht hcov n
  have hJ : ∀ a b, a ≤ b → Set.range (j a).u ⊆ Set.range (j b).u := by
    rintro a b hab _ ⟨x, rfl⟩
    exact ⟨(t a b hab).u x, (ht a b hab).2 x⟩
  have hJc : ∀ x, ∃ a, x ∈ Set.range (j a).u := fun x => by
    obtain ⟨a, y, hy⟩ := hcov x
    exact ⟨a, y, hy⟩
  have lift : ∀ m (c : L.coch.X m) (a0 : ι),
      ∃ b, a0 ≤ b ∧ ∃ c' : (A b).coch.X m, (j b).hom.f m c' = c := by
    intro m c a0
    obtain ⟨b, hab, hsub⟩ :=
      exists_upper_range (fun a => Set.range (j a).u) hJ hJc _ (coch_range_finite c) a0
    exact ⟨b, hab, pair_hom_lift_of_id (j b) (hj b).1 m c hsub⟩
  have cj : ∀ a m (x : (A a).coch.X m), ((j a).hom.f m x).1 = fun g => (j a).u (x.1 g) :=
    fun a m x => pair_hom_f_coe_of_id (j a) (hj a).1 m x
  have jt : ∀ a b (h : a ≤ b) m (x : (A a).coch.X m),
      (j b).hom.f m ((t a b h).hom.f m x) = (j a).hom.f m x := by
    intro a b h m x
    apply Subtype.ext
    rw [cj, cj, pair_hom_f_coe_of_id (t a b h) (ht a b h).1]
    funext g
    exact (ht a b h).2 _
  have jinj : ∀ a m, Function.Injective ((j a).hom.f m) := fun a m =>
    pair_hom_f_inj_of_id (j a) (hj a).1 (hj a).2 m
  refine ⟨fun x => ?_, fun a y hy => ?_⟩
  · obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨b, -, c', hc'⟩ := lift n z.1 (Classical.arbitrary ι)
    have hcz : c' ∈ (A b).coch.Z n := by
      show (A b).coch.d n c' = 0
      apply jinj b (n + 1)
      rw [(j b).hom.comm, hc', map_zero]
      exact z.2
    refine ⟨b, Submodule.Quotient.mk ⟨c', hcz⟩, ?_⟩
    unfold Cx.Hom.H
    rw [Submodule.mapQ_apply]
    congr 1
    exact Subtype.ext hc'
  · obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    unfold Cx.Hom.H at hy
    rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hy
    cases n with
    | zero =>
      have hz : z = 0 := by
        apply Subtype.ext
        apply jinj a 0
        show (j a).hom.f 0 z.1 = (j a).hom.f 0 0
        rw [map_zero]
        exact hy
      refine ⟨a, le_refl a, ?_⟩
      rw [hz, Submodule.Quotient.mk_zero, map_zero]
    | succ m =>
      obtain ⟨w, hw⟩ := hy
      obtain ⟨b, hab, w', hw'⟩ := lift m w a
      refine ⟨b, hab, ?_⟩
      unfold Cx.Hom.H
      rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero]
      refine ⟨w', ?_⟩
      apply jinj b (m + 1)
      show (j b).hom.f (m + 1) ((A b).coch.d m w') =
        (j b).hom.f (m + 1) ((t a b hab).hom.f (m + 1) z.1)
      rw [(j b).hom.comm, hw', jt]
      exact hw

end ReciprocityTheory.Coh
