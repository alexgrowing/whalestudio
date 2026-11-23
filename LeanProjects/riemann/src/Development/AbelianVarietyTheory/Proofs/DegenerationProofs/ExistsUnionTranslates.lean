import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.StrictModelTranslatesTwistCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGlueFinitelyManyCompatibleSmoothModelsStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModelGroupLawDefinedAtTranslateStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniqueModelExtensionOfDefinedAtPointsStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
namespace GlobalTheory.SS.FinUnion
variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K] {A A' : Over (Sp K)}

theorem mem_of_closed {S : Scheme.{0}} {W N G U : Over S} (g : W ⟶ N) (h : W ⟶ G) [IsClosedImmersion (lift g h).left]
    (q : U ⟶ N) (φ : U ⟶ G) {T : Scheme.{0}} (t : T ⟶ U.left) (ht : DenseRange t) (r : T ⟶ W.left)
    (h1 : t ≫ q.left = r ≫ g.left) (h2 : t ≫ φ.left = r ≫ h.left) (z : U.left) :
    ∃ w, g.left w = q.left z ∧ h.left w = φ.left z := by
  have e : t ≫ (lift q φ).left = r ≫ (lift g h).left := by
    apply pullback.hom_ext
    · change (t ≫ (lift q φ).left) ≫ (fst N G).left = (r ≫ (lift g h).left) ≫ (fst N G).left
      rw [Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left, lift_fst, lift_fst, h1]
    · change (t ≫ (lift q φ).left) ≫ (snd N G).left = (r ≫ (lift g h).left) ≫ (snd N G).left
      rw [Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left, lift_snd, lift_snd, h2]
  have hc : IsClosed ((lift q φ).left ⁻¹' Set.range (lift g h).left) :=
    (lift g h).left.isClosedEmbedding.isClosed_range.preimage (lift q φ).left.continuous
  have hs : Set.range t ⊆ (lift q φ).left ⁻¹' Set.range (lift g h).left := by
    rintro _ ⟨x, rfl⟩
    exact ⟨r x, by rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, e]⟩
  obtain ⟨w, hw⟩ := hc.closure_subset_iff.2 hs (ht z)
  refine ⟨w, ?_, ?_⟩
  · have := congrArg (fst N G).left hw
    rwa [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Over.comp_left, ← Over.comp_left, lift_fst, lift_fst] at this
  · have := congrArg (snd N G).left hw
    rwa [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Over.comp_left, ← Over.comp_left, lift_snd, lift_snd] at this

theorem range_j (M : Model R A) : Set.range M.j = M.Y.hom ⁻¹' Set.range (spMap (algebraMap R K)) := by
  rw [← Scheme.Pullback.range_fst, Model.j, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
  have : Function.Surjective M.e.inv.left := ((Over.forget _).mapIso M.e).inv.surjective
  rw [this.range_eq, Set.image_univ]

theorem dense_j [IsDomain R] [IsFractionRing R K] (M : Model R A) : DenseRange M.j := by
  have := M.smooth
  have hd : DenseRange (spMap (algebraMap R K)) :=
    (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical (algebraMap R K)).2 (by
      rw [(RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R K)]; exact bot_le)
  unfold DenseRange
  rw [range_j]
  exact hd.preimage M.Y.hom.isOpenMap

theorem dense_res [IsDomain R] [IsFractionRing R K] (M : Model R A) (U : M.Y.left.Opens) : DenseRange (M.j ∣_ U) := by
  have h := (dense_j M).preimage U.ι.isOpenEmbedding.isOpenMap
  refine h.mono ?_
  rintro x ⟨a, ha⟩
  refine ⟨⟨a, show M.j a ∈ U from ha ▸ x.2⟩, Subtype.ext ?_⟩
  exact (morphismRestrict_base_coe M.j U _).trans ha

theorem mem_range_j [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] (M : Model R A) (y : M.Y.left)
    (hy : y ∉ M.sp) : y ∈ Set.range M.j := by
  rw [range_j]
  refine ⟨(⊥ : PrimeSpectrum K), ?_⟩
  have h1 : (M.Y.hom y).asIdeal = ⊥ := by
    by_contra hne
    exact hy (PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal ((M.Y.hom y).isPrime.isMaximal hne)))
  apply PrimeSpectrum.ext
  rw [h1]
  exact (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R K)

theorem ext_apply {M : Model R A} {N : Model R A'} {f : A ⟶ A'} {U : M.Y.left.Opens} {g : U.toScheme ⟶ N.Y.left}
    (h : Extends M N f U g) {T : Scheme.{0}} (t : T ⟶ U.toScheme) (w : T ⟶ A.left) (e : t ≫ U.ι = w ≫ M.j) :
    t ≫ g = w ≫ f.left ≫ N.j := by
  have hp := isPullback_morphismRestrict M.j U
  have a := hp.lift_fst t w e
  have b := hp.lift_snd t w e
  rw [← a, Category.assoc, h.2, ← Category.assoc, b]

theorem prod_j_fst (M : Model R A) (N : Model R A') :
    (M.prod N).j ≫ (fst M.Y N.Y).left = (fst A A').left ≫ M.j := by
  have h : (M.prod N).e.inv ≫ (Over.pullback (spMap (algebraMap R K))).map (fst M.Y N.Y) = fst A A' ≫ M.e.inv := by
    simp [Model.prod]
  have h2 := congrArg (fun x => x.left ≫ pullback.fst M.Y.hom (spMap (algebraMap R K))) h
  simp only [Over.comp_left, Category.assoc, Over.pullback_map_left] at h2
  erw [pullback.lift_fst] at h2
  exact (Category.assoc _ _ _).trans h2

theorem prod_j_snd (M : Model R A) (N : Model R A') :
    (M.prod N).j ≫ (snd M.Y N.Y).left = (snd A A').left ≫ N.j := by
  have h : (M.prod N).e.inv ≫ (Over.pullback (spMap (algebraMap R K))).map (snd M.Y N.Y) = snd A A' ≫ N.e.inv := by
    simp [Model.prod]
  have h2 := congrArg (fun x => x.left ≫ pullback.fst N.Y.hom (spMap (algebraMap R K))) h
  simp only [Over.comp_left, Category.assoc, Over.pullback_map_left] at h2
  erw [pullback.lift_fst] at h2
  exact (Category.assoc _ _ _).trans h2

theorem twist_j (M : Model R A) (f : A ≅ A') : f.hom.left ≫ (M.twist f).j = M.j := by
  simp only [Model.j, Model.twist, Iso.trans_inv, Over.comp_left, Category.assoc]
  rw [← Category.assoc, ← Over.comp_left, Iso.hom_inv_id]; simp

theorem exists_move {X Y S : Scheme.{0}} (f : X ⟶ S) (g : Y ⟶ S) (O : (pullback f g).Opens) (z₀ : ↥(pullback f g))
    (h₀ : z₀ ∈ O) (V : X.Opens) (hirr : IsPreirreducible (f ⁻¹' {g (pullback.snd f g z₀)}))
    (x : X) (hx : x ∈ V) (hx' : f x = g (pullback.snd f g z₀)) :
    ∃ z ∈ O, pullback.snd f g z = pullback.snd f g z₀ ∧ pullback.fst f g z ∈ V := by
  set y := pullback.snd f g z₀ with hy
  have H0 : IsPullback ((pullback.snd f g).fiberι y) ((pullback.snd f g).fiberToSpecResidueField y)
      (pullback.snd f g) (Y.fromSpecResidueField y) := IsPullback.of_hasPullback _ _
  have H1 := H0.paste_horiz (IsPullback.of_hasPullback f g)
  rw [← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField] at H1
  have H2 : IsPullback (f.fiberι (g y)) (f.fiberToSpecResidueField (g y)) f (S.fromSpecResidueField (g y)) :=
    IsPullback.of_hasPullback _ _
  obtain ⟨p, hp1, hp2⟩ := H2.exists_lift ((pullback.snd f g).fiberι y ≫ pullback.fst f g)
    ((pullback.snd f g).fiberToSpecResidueField y ≫ Spec.map (g.residueFieldMap y)) (by
      rw [H1.w, Category.assoc])
  rw [← hp1] at H1
  have H3 := H1.of_right hp2 H2
  have ho : UniversallyOpen p := MorphismProperty.of_isPullback H3.flip inferInstance
  have hp : ∀ w, f.fiberι (g y) (p w) = pullback.fst f g ((pullback.snd f g).fiberι y w) := fun w => by
    rw [← Scheme.Hom.comp_apply, hp1, Scheme.Hom.comp_apply]
  obtain ⟨w₀, hw₀⟩ : z₀ ∈ Set.range ((pullback.snd f g).fiberι y) := by
    rw [Scheme.Hom.range_fiberι]; rfl
  obtain ⟨x₀, hx₀⟩ : x ∈ Set.range (f.fiberι (g y)) := by
    rw [Scheme.Hom.range_fiberι]; exact hx'
  have hI : IsPreirreducible (Set.univ : Set (f.fiber (g y))) := by
    have := Subtype.preirreducibleSpace hirr
    have h := (PreirreducibleSpace.isPreirreducible_univ (X := f ⁻¹' {g y})).image _
      (f.fiberHomeo (g y)).symm.continuous.continuousOn
    rwa [Set.image_univ, (f.fiberHomeo (g y)).symm.surjective.range_eq] at h
  obtain ⟨_, -, ⟨w, hw, rfl⟩, hV⟩ := hI _ _
    (p.isOpenMap _ (O.isOpen.preimage ((pullback.snd f g).fiberι y).continuous))
    (V.isOpen.preimage (f.fiberι (g y)).continuous) ⟨p w₀, trivial, w₀, by simpa [hw₀] using h₀, rfl⟩
    ⟨x₀, trivial, by simpa [hx₀] using hx⟩
  refine ⟨_, hw, ((pullback.snd f g).range_fiberι y).le ⟨w, rfl⟩, ?_⟩
  rw [← hp]; exact hV

theorem irr_union {X I : Type} [TopologicalSpace X] (S : Set X) (U : I → Set X) (i₀ : I) (hU : ∀ i, IsOpen (U i))
    (hI : ∀ i, IsPreirreducible (S ∩ U i)) (hc : ∀ x ∈ S, ∃ i, x ∈ U i) (hm : ∀ i, (S ∩ U i ∩ U i₀).Nonempty) :
    IsIrreducible S := by
  refine ⟨(hm i₀).mono fun x hx => hx.1.1, ?_⟩
  have hs : S ⊆ closure (S ∩ U i₀) := fun x hx => by
    obtain ⟨i, hi⟩ := hc x hx
    exact closure_mono (show S ∩ U i ∩ U i₀ ⊆ S ∩ U i₀ from fun y hy => ⟨hy.1.1, hy.2⟩)
      (subset_closure_inter_of_isPreirreducible_of_isOpen (hI i) (hU i₀) (hm i) ⟨hx, hi⟩)
  have e : closure S = closure (S ∩ U i₀) :=
    subset_antisymm (closure_minimal hs isClosed_closure) (closure_mono Set.inter_subset_left)
  rw [← isPreirreducible_iff_closure, e]
  exact (hI i₀).closure

theorem defAt_of_le {P : Model R A'} {N G : Model R A} {f : A' ⟶ A} {z : P.Y.left} (h : DefAt P N f z) (hl : N.Le G) :
    DefAt P G f z := by
  obtain ⟨U, φ, hz, h1, h2⟩ := h
  obtain ⟨g, -, hg⟩ := hl
  refine ⟨U, φ ≫ g.left, hz, ?_, ?_⟩
  · rw [Category.assoc, Over.w g, h1]
  · rw [← Category.assoc, h2, ← hg]; simp only [Category.assoc]

section
variable [GrpObj A] [IsCommMonObj A]

theorem transl_one : (transl (1 : 𝟙_ (Over (Sp K)) ⟶ A)).hom = 𝟙 A := by
  simp [transl]

theorem law_split (a : 𝟙_ (Over (Sp K)) ⟶ A) :
    lift (fst A A ≫ (transl a).hom) (shear A false ≫ snd A A) ≫ μ[A] = snd A A ≫ (transl a).hom := by
  change (fst A A ≫ (transl a).hom) * (shear A false ≫ snd A A) = _
  simp only [transl, shear, lift_snd, MonObj.comp_mul, Category.comp_id, ← Category.assoc,
    toUnit_unique (fst A A ≫ toUnit A) (toUnit _), toUnit_unique (snd A A ≫ toUnit A) (toUnit _)]
  group

set_option backward.isDefEq.respectTransparency false in

theorem le_of_law [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] {M G : Model R A} (hM : Strict M)
    (m : M.Y ⊗ M.Y ⟶ G.Y) (hm : (M.prod M).j ≫ m.left = (μ[A]).left ≫ G.j) (a : 𝟙_ (Over (Sp K)) ⟶ A)
    (ha : GenIso M M (transl a).hom) (hc : Compat (M.twist (transl a)) G) : (M.twist (transl a)).Le G := by
  obtain ⟨W, g, h, hg, hh, eg, eh, hcl⟩ := hc
  have hsurj : Function.Surjective g.left := by
    intro y
    by_cases hy : y ∈ M.sp
    swap
    · obtain ⟨x, rfl⟩ := mem_range_j (M.twist (transl a)) y hy
      exact ⟨W.j x, by rw [← Scheme.Hom.comp_apply, eg]⟩
    obtain ⟨z₀, hz₀, O, σ, hO, hσ, -⟩ := (hM.2 false y hy).2
    obtain ⟨x, hx, V, τ, hV, hτ, -⟩ := ha
    have hy' : M.Y.hom (pullback.snd M.Y.hom M.Y.hom z₀) = IsLocalRing.closedPoint R := by
      have : M.Y.hom ((snd M.Y M.Y).left z₀) = IsLocalRing.closedPoint R := by rw [hz₀]; exact hy
      exact this
    obtain ⟨z, hzO, hz, hzV⟩ := exists_move M.Y.hom M.Y.hom O z₀ hO V
      (by rw [hy']; exact hM.1.1.2) x hV (by rw [hy']; exact hx)
    let Ω : (M.prod M).Y.left.Opens := O ⊓ (fst M.Y M.Y).left ⁻¹ᵁ V
    let U : Over (Sp R) := Over.mk (Ω.ι ≫ (M.Y ⊗ M.Y).hom)
    let i : U ⟶ M.Y ⊗ M.Y := Over.homMk Ω.ι rfl
    let a₁ : Ω.toScheme ⟶ V.toScheme := (fst M.Y M.Y).left.resLE V Ω inf_le_right
    have e₁ : a₁ ≫ V.ι = Ω.ι ≫ (fst M.Y M.Y).left := Scheme.Hom.resLE_comp_ι _ _
    let a₂ : Ω.toScheme ⟶ O.toScheme := Scheme.homOfLE _ inf_le_left
    have e₂ : a₂ ≫ O.ι = Ω.ι := Scheme.homOfLE_ι _ _
    let φ₁ : U ⟶ M.Y := Over.homMk (a₁ ≫ τ) (by
      change (a₁ ≫ τ) ≫ M.Y.hom = Ω.ι ≫ (M.Y ⊗ M.Y).hom
      rw [Category.assoc, hτ.1, ← Category.assoc, e₁, Category.assoc, Over.w])
    let φ₂ : U ⟶ M.Y ⊗ M.Y := Over.homMk (a₂ ≫ σ) (by
      change (a₂ ≫ σ) ≫ (M.prod M).Y.hom = Ω.ι ≫ (M.prod M).Y.hom
      rw [Category.assoc, hσ.1, ← Category.assoc, e₂])
    let t := (M.prod M).j ∣_ Ω
    let w := ((M.prod M).j ⁻¹ᵁ Ω).ι
    have et : t ≫ Ω.ι = w ≫ (M.prod M).j := morphismRestrict_ι _ _
    have c₁ : (t ≫ a₁) ≫ τ = (w ≫ (fst A A).left) ≫ (transl a).hom.left ≫ M.j :=
      ext_apply hτ _ _ (by
        rw [Category.assoc, e₁, ← Category.assoc, et, Category.assoc, Category.assoc]
        exact congrArg (w ≫ ·) (prod_j_fst M M))
    have c₂ : (t ≫ a₂) ≫ σ = w ≫ (shear A false).left ≫ (M.prod M).j :=
      ext_apply hσ _ _ (by rw [Category.assoc, e₂, et])
    have c₃ : t ≫ (lift φ₁ (φ₂ ≫ snd M.Y M.Y)).left =
        w ≫ (lift (fst A A ≫ (transl a).hom) (shear A false ≫ snd A A)).left ≫ (M.prod M).j := by
      apply pullback.hom_ext
      · change (t ≫ _) ≫ (fst M.Y M.Y).left = (w ≫ _) ≫ (fst M.Y M.Y).left
        rw [Category.assoc, ← Over.comp_left, lift_fst, Category.assoc, Category.assoc]
        erw [prod_j_fst M M]
        rw [← Over.comp_left_assoc, lift_fst]
        simp only [Category.assoc, Over.comp_left] at c₁ ⊢
        exact c₁
      · change (t ≫ _) ≫ (snd M.Y M.Y).left = (w ≫ _) ≫ (snd M.Y M.Y).left
        rw [Category.assoc, ← Over.comp_left, lift_snd, Category.assoc, Category.assoc]
        erw [prod_j_snd M M]
        rw [← Over.comp_left_assoc, lift_snd]
        have := congrArg (· ≫ (snd M.Y M.Y).left) c₂
        simp only [Category.assoc] at this
        erw [prod_j_snd M M] at this
        simp only [Category.assoc, Over.comp_left]
        exact this
    obtain ⟨v, hv, -⟩ := mem_of_closed g h (i ≫ snd M.Y M.Y) (lift φ₁ (φ₂ ≫ snd M.Y M.Y) ≫ m) t
      (dense_res (M.prod M) Ω) (w ≫ (snd A A).left ≫ (transl a).hom.left ≫ W.j)
      (by
        simp only [Category.assoc]
        rw [eg, twist_j, ← prod_j_snd M M, ← Category.assoc, ← et, Category.assoc]
        rfl)
      (by
        simp only [Category.assoc]
        rw [eh, Over.comp_left, ← Category.assoc, c₃]
        simp only [Category.assoc]
        erw [hm]
        rw [← Over.comp_left_assoc, law_split, Over.comp_left_assoc])
      ⟨z, hzO, hzV⟩
    exact ⟨v, hv.trans (hz.trans hz₀)⟩
  have : Surjective g.left := ⟨hsurj⟩
  have : IsIso g.left := (isIso_iff_isOpenImmersion_and_surjective _).2 ⟨hg, this⟩
  have : IsIso ((Over.forget _).map g) := this
  have : IsIso g := isIso_of_reflects_iso g (Over.forget _)
  have e : g.left ≫ (inv g ≫ h).left = h.left := by rw [← Over.comp_left, IsIso.hom_inv_id_assoc]
  refine ⟨inv g ≫ h, ?_, ?_⟩
  · rw [← IsIso.eq_inv_comp] at e
    rw [e]; infer_instance
  · rw [← eg, Category.assoc, e, eh]
end

theorem sp_inter {M G : Model R A} [IsLocalRing R] (g : M.Y ⟶ G.Y) : G.sp ∩ Set.range g.left = g.left '' M.sp := by
  have e : ∀ x, G.Y.hom (g.left x) = M.Y.hom x := fun x => by rw [← Scheme.Hom.comp_apply, Over.w]
  ext y
  constructor
  · rintro ⟨hy, x, rfl⟩
    exact ⟨x, (e x).symm.trans hy, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨(e x).trans hx, x, rfl⟩

set_option backward.isDefEq.respectTransparency false in

theorem meet [IsDomain R] [IsLocalRing R] [IsFractionRing R K] {M G : Model R A} (f : A ≅ A) (hf : GenIso M M f.hom)
    (g : (M.twist f).Y ⟶ G.Y) (hg : (M.twist f).j ≫ g.left = G.j) (g₀ : M.Y ⟶ G.Y) (hg₀ : M.j ≫ g₀.left = G.j) :
    (G.sp ∩ Set.range g.left ∩ Set.range g₀.left).Nonempty := by
  obtain ⟨x, hx, V, τ, hV, hτ, -⟩ := hf
  have := G.sep
  have : IsClosedImmersion (lift (𝟙 G.Y) (𝟙 G.Y)).left := by
    have : (lift (𝟙 G.Y) (𝟙 G.Y)).left = pullback.diagonal G.Y.hom := by
      apply pullback.hom_ext
      · change (lift (𝟙 G.Y) (𝟙 G.Y) ≫ fst _ _).left = _
        simp
      · change (lift (𝟙 G.Y) (𝟙 G.Y) ≫ snd _ _).left = _
        simp
    rw [this]; infer_instance
  let U : Over (Sp R) := Over.mk (V.ι ≫ M.Y.hom)
  let i : U ⟶ (M.twist f).Y := Over.homMk V.ι rfl
  let φ : U ⟶ M.Y := Over.homMk τ hτ.1
  obtain ⟨v, h1, h2⟩ := mem_of_closed (𝟙 G.Y) (𝟙 G.Y) (i ≫ g) (φ ≫ g₀) (M.j ∣_ V) (dense_res M V)
    ((M.j ⁻¹ᵁ V).ι ≫ f.hom.left ≫ G.j)
    (by
      change M.j ∣_ V ≫ V.ι ≫ g.left = _ ≫ 𝟙 _
      rw [Category.comp_id, ← Category.assoc, morphismRestrict_ι, ← hg, ← Category.assoc f.hom.left, twist_j,
        Category.assoc])
    (by
      change M.j ∣_ V ≫ τ ≫ g₀.left = _ ≫ 𝟙 _
      rw [Category.comp_id, ← Category.assoc, hτ.2, ← hg₀]
      simp only [Category.assoc]) ⟨x, hV⟩
  refine ⟨g.left x, ?_, τ ⟨x, hV⟩, h2.symm.trans h1⟩
  rw [sp_inter]
  exact ⟨x, hx, rfl⟩

end GlobalTheory.SS.FinUnion

namespace GlobalTheory.SS
open FinUnion

theorem exists_union_translates : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K], SH R K → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ M : Model R A, Strict M → ∃ G : Model R A, G.Irr ∧ (∀ a : (𝟙_ (Over (Sp K)) ⟶ A), GenIso M M (transl a).hom → (M.twist (transl a)).Le G) ∧ (∀ y : G.Y.left, ∃ (a : (𝟙_ (Over (Sp K)) ⟶ A)) (g : M.Y ⟶ G.Y), GenIso M M (transl a).hom ∧ IsOpenImmersion g.left ∧ (M.twist (transl a)).j ≫ g.left = G.j ∧ y ∈ Set.range g.left) ∧ ∀ z, DefAt (M.prod M) G (μ[A]) z := by
  intro R K _ _ _ _ _ hS A _ _ hA M hM
  obtain ⟨_, -, -, _⟩ := id hS
  choose a ha U φ hU hφ using GlobalTheory.T.modelGroupLaw_definedAt_translate R K hS A hA M hM
  have := (M.prod M).qc
  have : CompactSpace (M.prod M).Y.left := QuasiCompact.compactSpace_of_compactSpace (M.prod M).Y.hom
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover (fun z => (U z : Set (M.prod M).Y.left))
    (fun z => (U z).isOpen) (fun z _ => Set.mem_iUnion.2 ⟨z, hU z⟩)
  let b : Fin (T.card + 1) → (𝟙_ (Over (Sp K)) ⟶ A) := Fin.cons 1 fun i => a (T.equivFin.symm i)
  have hb : ∀ i, GenIso M M (transl (b i)).hom := by
    intro i
    refine Fin.cases ?_ (fun i => ha _) i
    change GenIso M M (transl 1).hom
    rw [transl_one]
    obtain ⟨y, hy⟩ := hM.1.1.1
    exact ⟨y, hy, isoAt_id M y⟩
  obtain ⟨G, hle, hcov, hcomp⟩ := GlobalTheory.T.exists_glue_finitely_many_compatible_smoothModels R K A T.card (fun i => M.twist (transl (b i)))
    fun i j => GlobalTheory.T.strictModel_translates_twist_compatible R K hS A hA M hM _ _ (hb i) (hb j)
  have hdef : ∀ z, DefAt (M.prod M) G (μ[A]) z := by
    intro z
    obtain ⟨z', hz', hz⟩ := Set.mem_iUnion₂.1 (hT (Set.mem_univ z))
    refine defAt_of_le ?_ (hle (T.equivFin ⟨z', hz'⟩).succ)
    have : b (T.equivFin ⟨z', hz'⟩).succ = a z' := by simp [b]
    rw [this]
    exact ⟨U z', φ z', hz, hφ z'⟩
  obtain ⟨m, hm, -⟩ := GlobalTheory.T.existsUnique_model_extension_of_definedAtPoints R K _ _ _ _ _ hdef
  refine ⟨G, ?_, fun c hc => le_of_law hM m hm c hc (hcomp _ fun i => GlobalTheory.T.strictModel_translates_twist_compatible R K hS A hA M hM _ _ hc (hb i)),
    fun y => ?_, hdef⟩
  · obtain ⟨g₀, o₀, e₀⟩ := hle 0
    have e₁ : M.j ≫ g₀.left = G.j := by
      have := twist_j M (transl (1 : 𝟙_ (Over (Sp K)) ⟶ A))
      rw [transl_one, Over.id_left, Category.id_comp] at this
      rw [← this]; exact e₀
    refine irr_union (I := {p : Σ i, ((M.twist (transl (b i))).Y ⟶ G.Y) //
      IsOpenImmersion p.2.left ∧ (M.twist (transl (b p.1))).j ≫ p.2.left = G.j}) G.sp
      (fun p => Set.range p.1.2.left) ⟨⟨0, g₀⟩, o₀, e₀⟩ (fun p => ?_) (fun p => ?_) (fun y _ => ?_)
      (fun p => meet _ (hb p.1.1) p.1.2 p.2.2 g₀ e₁)
    · have := p.2.1
      exact p.1.2.left.isOpenEmbedding.isOpen_range
    · rw [sp_inter]
      exact hM.1.1.2.image _ p.1.2.left.continuous.continuousOn
    · obtain ⟨i, g, h1, h2, h3⟩ := hcov y
      exact ⟨⟨⟨i, g⟩, h1, h2⟩, h3⟩
  · obtain ⟨i, g, h1, h2, h3⟩ := hcov y
    exact ⟨b i, g, hb i, h1, h2, h3⟩

end GlobalTheory.SS
end
