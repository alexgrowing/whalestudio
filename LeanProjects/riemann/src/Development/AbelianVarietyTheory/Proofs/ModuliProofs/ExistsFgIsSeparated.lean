import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MorphismsSpreadOutToFgSubalgebra

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.SpreadSep

universe u

open AlgebraicGeometry CategoryTheory Limits in

theorem _root_.GlobalTheory.SpreadSep.exists_isClosed_preimage_diff {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) (c : Cone D)
    (hc : IsLimit c) [IsCofiltered I] [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)] {i : I}
    (O O' : (D.obj i).Opens) (hO : IsCompact (O : Set (D.obj i)))
    (hO' : IsCompact (O' : Set (D.obj i)))
    (H : IsClosed (c.π.app i ⁻¹' ((O : Set (D.obj i)) \ O'))) :
    ∃ (j : I) (f : j ⟶ i), IsClosed (D.map f ⁻¹' ((O : Set (D.obj i)) \ O')) := by
  have hw : ∀ {a b : I} (g : a ⟶ b) (x : c.pt), D.map g (c.π.app a x) = c.π.app b x := by
    intro a b g x
    rw [← c.w g]; rfl
  have hpw : ∀ {a b : I} (g : a ⟶ b) (W : (D.obj b).Opens),
      c.π.app a ⁻¹ᵁ (D.map g ⁻¹ᵁ W) = c.π.app b ⁻¹ᵁ W := by
    intro a b g W
    ext x
    change D.map g (c.π.app a x) ∈ W ↔ c.π.app b x ∈ W
    rw [hw]
  have hpre : ∀ {a b : I} (g : a ⟶ b) (W : (D.obj b).Opens), IsCompact (W : Set (D.obj b)) →
      IsCompact ((D.map g ⁻¹ᵁ W : (D.obj a).Opens) : Set (D.obj a)) :=
    fun g W hW => QuasiCompact.isCompact_preimage (f := D.map g) _ W.isOpen hW
  haveI := Scheme.compactSpace_of_isLimit D c hc
  let C : c.pt.Opens := ⟨_, H.isOpen_compl⟩
  have hCmem : ∀ x, x ∈ C ↔ (c.π.app i x ∈ O → c.π.app i x ∈ O') := by
    intro x
    change x ∉ c.π.app i ⁻¹' ((O : Set (D.obj i)) \ O') ↔ _
    simp only [Set.mem_preimage, Set.mem_diff, SetLike.mem_coe, not_and, not_not]
  let K : Set c.pt := ((c.π.app i ⁻¹ᵁ O : c.pt.Opens) : Set c.pt)ᶜ
  have hK : IsCompact K := IsClosed.isCompact (X := c.pt) (c.π.app i ⁻¹ᵁ O).isOpen.isClosed_compl
  let P : c.pt.Opens → Prop := fun A => (∃ (k : I) (_ : k ⟶ i) (W : (D.obj k).Opens),
    IsCompact (W : Set (D.obj k)) ∧ c.π.app k ⁻¹ᵁ W = A) ∧ A ≤ C
  let ι := {A : c.pt.Opens // P A}
  haveI : Nonempty ι := ⟨⟨⊥, ⟨i, 𝟙 i, ⊥, by simp, by ext x; simp⟩, bot_le⟩⟩
  have hdir : Directed (· ⊆ ·) (fun A : ι => (A.1 : Set c.pt)) := by
    rintro ⟨A₁, ⟨k₁, f₁, W₁, hW₁, rfl⟩, hA₁⟩ ⟨A₂, ⟨k₂, f₂, W₂, hW₂, rfl⟩, hA₂⟩
    let l₁ := IsCofiltered.minToLeft k₁ k₂
    let l₂ := IsCofiltered.minToRight k₁ k₂
    have he : c.π.app _ ⁻¹ᵁ (D.map l₁ ⁻¹ᵁ W₁ ⊔ D.map l₂ ⁻¹ᵁ W₂) =
        c.π.app k₁ ⁻¹ᵁ W₁ ⊔ c.π.app k₂ ⁻¹ᵁ W₂ := by
      rw [Scheme.Hom.preimage_sup, hpw, hpw]
    refine ⟨⟨c.π.app k₁ ⁻¹ᵁ W₁ ⊔ c.π.app k₂ ⁻¹ᵁ W₂,
      ⟨_, l₁ ≫ f₁, _, (hpre _ _ hW₁).union (hpre _ _ hW₂), he⟩, sup_le hA₁ hA₂⟩, ?_, ?_⟩
    · exact fun x hx => Or.inl hx
    · exact fun x hx => Or.inr hx
  have hB := isBasis_preimage_isAffineOpen D c hc
  have hcov : K ⊆ ⋃ A : ι, (A.1 : Set c.pt) := by
    intro x hx
    have hxC : x ∈ C := (hCmem x).2 fun h => absurd h hx
    obtain ⟨U', ⟨j, V, hV, rfl⟩, hxU', hU'C⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 hB hxC
    let m := IsCofiltered.min j i
    refine Set.mem_iUnion.2 ⟨⟨c.π.app m ⁻¹ᵁ (D.map (IsCofiltered.minToLeft j i) ⁻¹ᵁ V),
      ⟨m, IsCofiltered.minToRight j i, _, hpre _ _ hV.isCompact, rfl⟩, ?_⟩, ?_⟩
    · rw [hpw]; exact hU'C
    · change x ∈ c.π.app m ⁻¹ᵁ (D.map (IsCofiltered.minToLeft j i) ⁻¹ᵁ V)
      rw [hpw]; exact hxU'
  obtain ⟨⟨_, ⟨k, f, W, hW, rfl⟩, hWC⟩, hKW⟩ :=
    hK.elim_directed_cover _ (fun A => A.1.isOpen) hcov hdir
  have h₁ : c.π.app k ⁻¹ᵁ (W ⊔ D.map f ⁻¹ᵁ O) = ⊤ := by
    rw [Scheme.Hom.preimage_sup, hpw, eq_top_iff]
    intro x _
    by_cases hx : c.π.app i x ∈ O
    · exact Or.inr hx
    · exact Or.inl (hKW hx)
  obtain ⟨l, g, hg⟩ := exists_map_eq_top D c hc _ h₁
  have hcpt : IsCompact ((D.map g ⁻¹ᵁ (W ⊓ D.map f ⁻¹ᵁ O) : (D.obj l).Opens) : Set (D.obj l)) :=
    hpre _ _ (QuasiSeparatedSpace.inter_isCompact _ _ W.isOpen hW (D.map f ⁻¹ᵁ O).isOpen
      (hpre _ _ hO))
  have h₂ : c.π.app l ⁻¹ᵁ (D.map g ⁻¹ᵁ (W ⊓ D.map f ⁻¹ᵁ O)) ≤
      c.π.app l ⁻¹ᵁ (D.map g ⁻¹ᵁ (D.map f ⁻¹ᵁ O')) := by
    rw [hpw, hpw, hpw, Scheme.Hom.preimage_inf, hpw]
    rintro x ⟨hxW, hxO⟩
    exact (hCmem x).1 (hWC hxW) hxO
  obtain ⟨m, h, hh⟩ := exists_map_preimage_le_map_preimage D c hc hcpt h₂
  refine ⟨m, h ≫ g ≫ f, ?_⟩
  have ht : ∀ y : D.obj m, D.map g (D.map h y) ∈ W ∨ D.map f (D.map g (D.map h y)) ∈ O := by
    intro y
    have : D.map h y ∈ D.map g ⁻¹ᵁ (W ⊔ D.map f ⁻¹ᵁ O) := by rw [hg]; trivial
    simpa using this
  have hle : ∀ y : D.obj m, D.map g (D.map h y) ∈ W → D.map f (D.map g (D.map h y)) ∈ O →
      D.map f (D.map g (D.map h y)) ∈ O' := by
    intro y hy₁ hy₂
    have : y ∈ D.map h ⁻¹ᵁ (D.map g ⁻¹ᵁ (W ⊓ D.map f ⁻¹ᵁ O)) := by simpa using ⟨hy₁, hy₂⟩
    simpa using hh this
  have hset : D.map (h ≫ g ≫ f) ⁻¹' ((O : Set (D.obj i)) \ O') =
      ((D.map (h ≫ g) ⁻¹ᵁ W ⊔ D.map (h ≫ g ≫ f) ⁻¹ᵁ O' : (D.obj m).Opens) : Set (D.obj m))ᶜ := by
    ext y
    simp only [Functor.map_comp, Set.mem_preimage, Set.mem_diff, SetLike.mem_coe, Set.mem_compl_iff,
      Scheme.Hom.preimage_sup, TopologicalSpace.Opens.coe_sup, Set.mem_union, Scheme.Hom.comp_apply]
    have h1 := ht y
    have h2 := hle y
    tauto
  rw [hset]
  exact (TopologicalSpace.Opens.isOpen _).isClosed_compl

open AlgebraicGeometry CategoryTheory Limits in
private theorem isSeparated_iff_isClosed_range_diagonal {Y Z : Scheme.{0}} (f : Y ⟶ Z) :
    IsSeparated f ↔ IsClosed (Set.range (pullback.diagonal f)) :=
  ⟨fun _ => (pullback.diagonal f).isClosedEmbedding.isClosed_range,
    fun h => ⟨IsClosedImmersion.of_isPreimmersion _ h⟩⟩

open AlgebraicGeometry CategoryTheory Limits in
private theorem isClosed_range_iso_comp_comp_iso_inv_iff {A B C D : Scheme.{0}} (a : A ≅ B) (g : B ⟶ C)
    (e : D ≅ C) : IsClosed (Set.range (a.hom ≫ g ≫ e.inv)) ↔ IsClosed (Set.range g) := by
  have hr : Set.range (a.hom ≫ g ≫ e.inv) = e.hom ⁻¹' Set.range g := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨a.hom x, ?_⟩
      change g (a.hom x) = (e.inv ≫ e.hom) (g (a.hom x))
      rw [e.inv_hom_id]
      rfl
    · rintro ⟨y, hy⟩
      refine ⟨a.inv y, ?_⟩
      change e.inv (g ((a.inv ≫ a.hom) y)) = z
      rw [a.inv_hom_id]
      change e.inv (g y) = z
      rw [hy]
      change (e.hom ≫ e.inv) z = z
      rw [e.hom_inv_id]
      rfl
  rw [hr]
  constructor
  · intro h
    have h' := h.preimage e.inv.continuous
    convert h' using 1
    ext y
    change y ∈ Set.range g ↔ (e.inv ≫ e.hom) y ∈ Set.range g
    rw [e.inv_hom_id]
    rfl
  · intro h
    exact h.preimage e.hom.continuous

open AlgebraicGeometry CategoryTheory Limits in
private theorem isSeparated_pullback_snd_spMap_iff_isClosed_preimage (k R : Type) [CommRing k] [CommRing R] [Algebra k R]
    (X : Scheme.{0}) (p : X ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k) :
    IsSeparated (pullback.snd p (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap k R))) ↔
      IsClosed (pullback.fst (pullback.snd p p ≫ p) (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap k R)) ⁻¹'
        Set.range (pullback.diagonal p)) := by
  rw [← pullbackSymmetry_hom_comp_fst, MorphismProperty.cancel_left_of_respectsIso @IsSeparated,
    isSeparated_iff_isClosed_range_diagonal, diagonal_pullback_fst]
  simp only [Over.pullback_map_left, Over.homMk_left, Over.mk_hom]
  rw [isClosed_range_iso_comp_comp_iso_inv_iff]
  have hL := IsPullback.of_right (h₁₁ := pullback.lift (pullback.fst p (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap k R)) ≫
      pullback.diagonal p) (pullback.snd p (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap k R))) (by simp [pullback.condition]))
    (h₁₂ := pullback.snd (pullback.snd p p ≫ p) (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap k R)))
    (h₂₁ := pullback.diagonal p) (h₂₂ := pullback.snd p p ≫ p)
    (v₁₁ := pullback.fst p (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap k R)))
    (v₁₂ := pullback.fst (pullback.snd p p ≫ p) (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap k R)))
    (v₁₃ := _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap k R))
    (by
      convert (IsPullback.of_hasPullback p (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap k R))).flip using 1
      · exact pullback.lift_snd _ _ _
      · simp) (pullback.lift_fst _ _ _)
    (IsPullback.of_hasPullback (pullback.snd p p ≫ p) (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap k R))).flip
  have hr : Set.range (pullback.lift (pullback.fst p (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap k R)) ≫
      pullback.diagonal p) (pullback.snd p (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap k R))) (by simp [pullback.condition])) =
      pullback.fst (pullback.snd p p ≫ p) (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap k R)) ⁻¹'
        Set.range (pullback.diagonal p) := by
    rw [← Scheme.Pullback.range_fst, ← hL.isoPullback_hom_fst]
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨y, rfl⟩
      refine ⟨hL.isoPullback.inv y, ?_⟩
      change ((hL.isoPullback.inv ≫ hL.isoPullback.hom) ≫ pullback.fst _ _) y = _
      rw [Iso.inv_hom_id, Category.id_comp]
  rw [hr]

open AlgebraicGeometry CategoryTheory Limits in

theorem _root_.GlobalTheory.SpreadSep.exists_fg_isSeparated (k V : Type) [CommRing k] [IsNoetherianRing k] [CommRing V]
    [Algebra k V] (X : Scheme.{0}) (p : X ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k) (h₁ : LocallyOfFiniteType p) (h₂ : QuasiCompact p)
    (h : IsSeparated (pullback.snd p (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap k V)))) :
    ∃ R : Subalgebra k V, R.FG ∧ IsSeparated (pullback.snd p (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap k R))) := by
  haveI := h₁
  haveI := h₂
  let pB : pullback p p ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k := pullback.snd p p ≫ p
  haveI : IsLocallyNoetherian (pullback p p) := LocallyOfFiniteType.isLocallyNoetherian pB
  haveI : CompactSpace ↥(_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k) := by unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp; infer_instance
  haveI : CompactSpace ↥(pullback p p) := QuasiCompact.compactSpace_of_compactSpace pB
  haveI : QuasiSeparated pB := inferInstance
  haveI : AlgebraicGeometry.IsNoetherian (pullback p p) := {}
  let D := _root_.GlobalTheory.Spread.bcDiagram pB V
  let c := _root_.GlobalTheory.Spread.bcCone pB V
  have hc := _root_.GlobalTheory.Spread.isLimitBcCone pB V
  haveI : ∀ {i j : (Finset V)ᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f) :=
    fun f => _root_.GlobalTheory.Spread.instIsAffineHomMapOppositeFinsetSchemeBcDiagram pB V f
  haveI : ∀ i, CompactSpace (D.obj i) := _root_.GlobalTheory.Spread.instCompactSpaceCarrierCarrierCommRingCatObjOppositeFinsetSchemeBcDiagramOfQuasiCompact pB V
  haveI : ∀ i, QuasiSeparatedSpace (D.obj i) := _root_.GlobalTheory.Spread.instQuasiSeparatedSpaceCarrierCarrierCommRingCatObjOppositeFinsetSchemeBcDiagramOfQuasiSeparated pB V
  have hπ : ∀ (j : (Finset V)ᵒᵖ) (x : c.pt),
      pullback.fst pB (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap k (Algebra.adjoin k (↑(Opposite.unop j) : Set V))))
        (c.π.app j x) = pullback.fst pB (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap k V)) x := by
    intro j x
    have e : c.π.app j ≫ pullback.fst pB (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap k
        (Algebra.adjoin k (↑(Opposite.unop j) : Set V)))) = pullback.fst pB (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap k V)) := by
      simp only [c, _root_.GlobalTheory.Spread.bcCone]
      exact _root_.GlobalTheory.Spread.bcMap_fst _ _
    rw [← e]
    try rfl
  have hmap : ∀ {j j' : (Finset V)ᵒᵖ} (f : j ⟶ j') (x : D.obj j),
      pullback.fst pB (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap k (Algebra.adjoin k (↑(Opposite.unop j') : Set V))))
        (D.map f x) =
      pullback.fst pB (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap k (Algebra.adjoin k (↑(Opposite.unop j) : Set V)))) x := by
    intro j j' f x
    have e : D.map f ≫ pullback.fst pB (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap k
        (Algebra.adjoin k (↑(Opposite.unop j') : Set V)))) =
        pullback.fst pB (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap k (Algebra.adjoin k (↑(Opposite.unop j) : Set V)))) := by
      simp only [D, _root_.GlobalTheory.Spread.bcDiagram]
      exact _root_.GlobalTheory.Spread.bcMap_fst _ _
    rw [← e]
    try rfl
  let i₀ : (Finset V)ᵒᵖ := Opposite.op ∅
  let f₀ := pullback.fst pB (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap k (Algebra.adjoin k (↑(Opposite.unop i₀) : Set V))))
  obtain ⟨U, Z, hU, hZ, hT⟩ := (pullback.diagonal p).isLocallyClosed_range
  let O : (D.obj i₀).Opens := f₀ ⁻¹ᵁ ⟨U, hU⟩
  let O' : (D.obj i₀).Opens := f₀ ⁻¹ᵁ ⟨Zᶜ, hZ.isOpen_compl⟩
  have hcpt : ∀ W : (pullback p p).Opens, IsCompact ((f₀ ⁻¹ᵁ W : (D.obj i₀).Opens) : Set (D.obj i₀)) :=
    fun W => QuasiCompact.isCompact_preimage (f := f₀) _ W.isOpen
      (TopologicalSpace.NoetherianSpace.isCompact _)
  have hset : ∀ y : D.obj i₀, y ∈ (O : Set (D.obj i₀)) \ O' ↔ f₀ y ∈ Set.range (pullback.diagonal p) := by
    intro y
    rw [hT]
    change (f₀ y ∈ U ∧ ¬ f₀ y ∈ Zᶜ) ↔ _
    simp
  have H : IsClosed (c.π.app i₀ ⁻¹' ((O : Set (D.obj i₀)) \ O')) := by
    have h' := (isSeparated_pullback_snd_spMap_iff_isClosed_preimage k V X p).1 h
    have hs : c.π.app i₀ ⁻¹' ((O : Set (D.obj i₀)) \ O') =
        pullback.fst pB (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap k V)) ⁻¹' Set.range (pullback.diagonal p) := by
      ext x
      exact (hset (c.π.app i₀ x)).trans
        (Iff.of_eq (congrArg (· ∈ Set.range (pullback.diagonal p)) (hπ i₀ x)))
    rw [hs]
    exact h'
  obtain ⟨j, f, hj⟩ := _root_.GlobalTheory.SpreadSep.exists_isClosed_preimage_diff D c hc O O' (hcpt _) (hcpt _) H
  refine ⟨Algebra.adjoin k (↑(Opposite.unop j) : Set V), Subalgebra.fg_adjoin_finset _, ?_⟩
  rw [isSeparated_pullback_snd_spMap_iff_isClosed_preimage]
  have hs : D.map f ⁻¹' ((O : Set (D.obj i₀)) \ O') =
      pullback.fst pB (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap k (Algebra.adjoin k (↑(Opposite.unop j) : Set V)))) ⁻¹'
        Set.range (pullback.diagonal p) := by
    ext x
    exact (hset (D.map f x)).trans
      (Iff.of_eq (congrArg (· ∈ Set.range (pullback.diagonal p)) (hmap f x)))
  rw [hs] at hj
  exact hj

end GlobalTheory.SpreadSep
