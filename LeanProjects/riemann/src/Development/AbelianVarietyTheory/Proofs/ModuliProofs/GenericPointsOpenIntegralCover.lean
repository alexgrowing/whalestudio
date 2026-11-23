import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsIsoStalkMapOfFlatOfSurjectiveOnStalks
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.TopAmpExists
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasFramesOfAmpFrames
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSectionPowerTransportCartesianSquareStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TransitionFramesPushOpenImmersionImageStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasFramesDisjointUnionCechDataStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAmpleCechLineBundleDisjointUnionPushforwardStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasTransitionCompatibleFramesOfNoCompleteDVRPoinStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PulledSectionsFormBasisIdOfPulledSectionsFormBasStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CardPulledSectionsFormBasisEqPowDimStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CardBasisPolarisationPowerZeroEqOneStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AbelianLocusIsOpenOfOpenImmersionCoverStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FibresSplitOfOpenImmersionCoverStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasFibrewiseThetaOfOpenImmersionCoverStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverOfIsComplOpenImmersionsStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsCompleteDVRPointGenericPointStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAbelianTripleGlueTwoOpenImmersionsStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum

noncomputable section

namespace GlobalTheory.ModelSum

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem range_desc {X Y Z : Scheme.{0}} (f : X ⟶ Z) (g : Y ⟶ Z) :
    Set.range (coprod.desc f g) = Set.range f ∪ Set.range g := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨x | x, rfl⟩ := (coprodMk _ _).surjective x
    · exact .inl ⟨x, by rw [coprodMk_inl, ← Scheme.Hom.comp_apply, coprod.inl_desc]⟩
    · exact .inr ⟨x, by rw [coprodMk_inr, ← Scheme.Hom.comp_apply, coprod.inr_desc]⟩
  · rintro (⟨x, rfl⟩ | ⟨x, rfl⟩)
    · exact ⟨(coprod.inl : X ⟶ X ⨿ Y) x, by rw [← Scheme.Hom.comp_apply, coprod.inl_desc]⟩
    · exact ⟨(coprod.inr : Y ⟶ X ⨿ Y) x, by rw [← Scheme.Hom.comp_apply, coprod.inr_desc]⟩

theorem isOpenImmersion_desc {X Y Z : Scheme.{0}} (f : X ⟶ Z) (g : Y ⟶ Z) [IsOpenImmersion f] [IsOpenImmersion g]
    (h : Disjoint (Set.range f) (Set.range g)) : IsOpenImmersion (coprod.desc f g) := by
  let α : ∀ i : ULift.{0} WalkingPair, (i.1.casesOn X Y : Scheme.{0}) ⟶ Z := fun i => match i with
    | ⟨.left⟩ => f
    | ⟨.right⟩ => g
  have : ∀ i, IsOpenImmersion (α i) := by rintro ⟨_ | _⟩ <;> assumption
  have h₁ : IsOpenImmersion (Sigma.desc α) := isOpenImmersion_sigmaDesc _ α (by
    rintro ⟨_ | _⟩ ⟨_ | _⟩ hij
    exacts [(hij rfl).elim, h, h.symm, (hij rfl).elim])
  have e : (coprodIsoSigma X Y).inv ≫ coprod.desc f g = Sigma.desc α := by
    refine Sigma.hom_ext _ _ ?_
    rintro ⟨_ | _⟩
    · rw [← Category.assoc, ι_left_coprodIsoSigma_inv, coprod.inl_desc, Sigma.ι_desc]
    · rw [← Category.assoc, ι_right_coprodIsoSigma_inv, coprod.inr_desc, Sigma.ι_desc]
  rw [(Iso.inv_comp_eq _).1 e]
  infer_instance

theorem isOpenImmersion_map {X Y X' Y' : Scheme.{0}} (f : X ⟶ X') (g : Y ⟶ Y') [IsOpenImmersion f] [IsOpenImmersion g] :
    IsOpenImmersion (coprod.map f g) := by
  have e : coprod.map f g = coprod.desc (f ≫ coprod.inl) (g ≫ coprod.inr) := by ext <;> simp
  rw [e]
  refine isOpenImmersion_desc _ _ (Set.disjoint_left.2 ?_)
  rintro _ ⟨x, rfl⟩ ⟨y, hy⟩
  exact inr_ne_inl _ _ (f x) (g y) hy

theorem isDominant_map {X Y X' Y' : Scheme.{0}} (f : X ⟶ X') (g : Y ⟶ Y') [IsDominant f] [IsDominant g] :
    IsDominant (coprod.map f g) := by
  refine ⟨fun z => ?_⟩
  obtain ⟨x | x, rfl⟩ := (coprodMk _ _).surjective z
  · rw [coprodMk_inl]
    refine closure_mono ?_ (image_closure_subset_closure_image (coprod.inl : X' ⟶ X' ⨿ Y').continuous
      ⟨x, f.denseRange x, rfl⟩)
    rintro _ ⟨_, ⟨y, rfl⟩, rfl⟩
    exact ⟨(coprod.inl : X ⟶ X ⨿ Y) y, by rw [← Scheme.Hom.comp_apply, coprod.inl_map, Scheme.Hom.comp_apply]⟩
  · rw [coprodMk_inr]
    refine closure_mono ?_ (image_closure_subset_closure_image (coprod.inr : Y' ⟶ X' ⨿ Y').continuous
      ⟨x, g.denseRange x, rfl⟩)
    rintro _ ⟨_, ⟨y, rfl⟩, rfl⟩
    exact ⟨(coprod.inr : Y ⟶ X ⨿ Y) y, by rw [← Scheme.Hom.comp_apply, coprod.inr_map, Scheme.Hom.comp_apply]⟩

theorem mem_inl_or_inr {X Y : Scheme.{0}} (z : (X ⨿ Y : Scheme.{0})) :
    z ∈ Set.range (coprod.inl : X ⟶ X ⨿ Y) ∨ z ∈ Set.range (coprod.inr : Y ⟶ X ⨿ Y) :=
  (isCompl_range_inl_inr X Y).sup_eq_top.ge (Set.mem_univ z)

theorem isNormalScheme_coprod {X Y : Scheme.{0}} (hX : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X) (hY : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Y) :
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (X ⨿ Y) := by
  have key : ∀ {A : Scheme.{0}} (f : A ⟶ X ⨿ Y) [IsOpenImmersion f], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme A → ∀ a,
      IsDomain ((X ⨿ Y).presheaf.stalk (f a)) ∧ IsIntegrallyClosed ((X ⨿ Y).presheaf.stalk (f a)) := by
    intro A f _ hA a
    obtain ⟨h₁, h₂⟩ := hA a
    let e := (asIso (f.stalkMap a)).commRingCatIsoToRingEquiv
    exact ⟨e.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv e.symm⟩
  intro z
  obtain ⟨x, rfl⟩ | ⟨x, rfl⟩ := mem_inl_or_inr z
  exacts [key _ hX x, key _ hY x]

theorem isReduced_of_isNormalScheme {X : Scheme.{0}} (hX : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X) : IsReduced X :=
  have := fun x => (hX x).1
  isReduced_of_isReduced_stalk X

theorem noetherianSpace_of_isProjOver {O : Type} [CommRing O] [IsNoetherianRing O] {Z : Scheme.{0}} {s : Z ⟶ Sp O}
    (h : IsProjOver s) : TopologicalSpace.NoetherianSpace Z := by
  obtain ⟨N, i, hi, rfl⟩ := h
  have : IsProper (PSpace.str O N) := isProper_str O N
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian (i ≫ PSpace.str O N)
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace (i ≫ PSpace.str O N)
  have : IsNoetherian Z := {}
  infer_instance

theorem exists_pull {S S' : Scheme.{0}} (f : S' ⟶ S) (t : SAB H S) : ∃ t' : SAB H S', Nonempty (SABMap t' t f) := by
  obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull f t
  exact ⟨_, ⟨m⟩⟩

section
variable {S S' S'' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {t'' : SAB H S''}

theorem map_comp {f : S' ⟶ S} {g : S'' ⟶ S'} {k : S'' ⟶ S} (m' : SABMap t'' t' g) (m : SABMap t' t f)
    (h : g ≫ f = k) : Nonempty (SABMap t'' t k) := by
  subst h
  exact ⟨(ObjMaps.exists_sab_comp m m').choose⟩

theorem map_cancel {f : S' ⟶ S} {g : S'' ⟶ S'} {k : S'' ⟶ S} (n : SABMap t'' t k) (m : SABMap t' t f)
    (h : g ≫ f = k) : Nonempty (SABMap t'' t' g) := by
  subst h
  exact ⟨(ObjMaps.exists_sab_cancel m n).choose⟩

theorem proper_of_map {f : S' ⟶ S} (m : SABMap t' t f) (h : IsProper t.G.hom) : IsProper t'.G.hom :=
  MorphismProperty.of_isPullback (P := @IsProper) m.cart.1 h

theorem lbIso_of_map {f : S' ⟶ S} (m : SABMap t' t f) : LBIso t'.PP.L (t.PP.L.pull m.φ) := by
  obtain ⟨w, g, -⟩ := m.lin
  exact ⟨w, g⟩

theorem range_subset_abLocus {f : S' ⟶ S} (m : SABMap t' t f) (h : IsProper t'.G.hom) : Set.range f ⊆ abLocus t.G := by
  rintro _ ⟨x, rfl⟩
  exact (abLocus_pullback abLocusOne t.semi m.cart.1 x).2 fun _ _ _ _ _ => inferInstance

theorem genericPoints_subset_abLocus {f : S' ⟶ S} [IsDominant f] [TopologicalSpace.NoetherianSpace S']
    (m : SABMap t' t f) (h : IsProper t'.G.hom) : genericPoints S ⊆ abLocus t.G :=
  (genericPoints_subset_range_of_isDominant f).trans (range_subset_abLocus m h)

end

def HasModel {O : Type} [CommRing O] {M : Scheme.{0}} (sM : M ⟶ Sp O) (tM : SAB H M) (m n : ℕ) (r s : ℤ) : Prop :=
  ∃ C : ZOn sM tM m, C.amp.n = n ∧ C.amp.r = r ∧ C.amp.s = s

variable {O : Type} [CommRing O] {M : Scheme.{0}} {sM : M ⟶ Sp O} {tM : SAB H M} {m n : ℕ} {r s : ℤ}

theorem hasModel_of_maps {Y Z : Scheme.{0}} (a : Y ⟶ M) [IsOpenImmersion a] [IsDominant a] (j : Y ⟶ Z)
    [IsOpenImmersion j] [IsDominant j] (z : Z ⟶ Sp O) (h₁ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z) (h₂ : IsProjOver z) (h₃ : Flat z)
    (t : SAB H Z) (h₄ : IsQProjOver (t.G.hom ≫ z)) (h₅ : Models.Good t) (h : j ≫ z = a ≫ sM) {tY : SAB H Y}
    (m₁ : SABMap tY tM a) (m₂ : SABMap tY t j) (A : LN.AmpFrames t.G t.PP.L (m ^ 2)) :
    HasModel sM tM m A.n A.r A.s := by
  obtain ⟨tW, ⟨k⟩⟩ := exists_pull a.isoOpensRange.inv tY
  obtain ⟨k₁⟩ := map_comp k m₁ a.isoOpensRange_inv_comp
  obtain ⟨k₂⟩ := map_comp k m₂ rfl
  exact ⟨⟨Z, z, h₁, h₂, h₃, t, h₄, h₅, a.opensRange, a.denseRange, a.isoOpensRange.inv ≫ j, inferInstance, inferInstance,
    by rw [Category.assoc, h, ← Category.assoc, a.isoOpensRange_inv_comp], tW, k₁, k₂, A⟩, rfl, rfl, rfl⟩

theorem isDominant_ι {X : Scheme.{0}} {W : X.Opens} (h : Dense (W : Set X)) : IsDominant W.ι :=
  ⟨by rwa [DenseRange, Scheme.Opens.range_ι]⟩

theorem HasModel.shrink (h : HasModel sM tM m n r s) {V : Scheme.{0}} (i : V ⟶ M) [IsOpenImmersion i] [IsDominant i]
    {tV : SAB H V} (k : SABMap tV tM i) : HasModel (i ≫ sM) tV m n r s := by
  obtain ⟨C, rfl, rfl, rfl⟩ := h
  have := isDominant_ι C.dense
  have := C.j_open
  have := C.j_dom
  have : IsDominant (pullback.fst i C.W.ι) := isDominant_pullback_fst_of_isOpenMap _ _ i.isOpenEmbedding.isOpenMap
  have : IsDominant (pullback.snd i C.W.ι) := by
    have := isDominant_pullback_fst_of_isOpenMap i C.W.ι C.W.ι.isOpenEmbedding.isOpenMap
    rw [← pullbackSymmetry_hom_comp_fst]; infer_instance
  obtain ⟨tY, ⟨p⟩⟩ := exists_pull (pullback.snd i C.W.ι) C.tW
  obtain ⟨p₁⟩ := map_comp p C.m₁ rfl
  obtain ⟨p₂⟩ := map_cancel p₁ k pullback.condition
  obtain ⟨p₃⟩ := map_comp p C.m₂ rfl
  exact hasModel_of_maps (pullback.fst i C.W.ι) (pullback.snd i C.W.ι ≫ C.j) C.s C.normal C.proj C.flat C.t C.qproj C.good
    (by rw [Category.assoc, C.j_over, pullback.condition_assoc]) p₂ p₃ C.amp

theorem HasModel.grow {V : Scheme.{0}} (i : V ⟶ M) [IsOpenImmersion i] [IsDominant i]
    {tV : SAB H V} (k : SABMap tV tM i) (h : HasModel (i ≫ sM) tV m n r s) : HasModel sM tM m n r s := by
  obtain ⟨C, rfl, rfl, rfl⟩ := h
  have := isDominant_ι C.dense
  have := C.j_open
  have := C.j_dom
  obtain ⟨p⟩ := map_comp C.m₁ k rfl
  exact hasModel_of_maps (C.W.ι ≫ i) C.j C.s C.normal C.proj C.flat C.t C.qproj C.good
    (by rw [Category.assoc, C.j_over]) p C.m₂ C.amp

theorem hasModel_of_isEmpty [IsEmpty M] : HasModel sM tM m n r s := by
  have hp : ∀ {X : Scheme.{0}} [IsEmpty X] (f : X ⟶ Sp O), IsProjOver f := fun {X} _ f =>
    ProjSpace.isProjOver_of_disjoint_cover f (fun i : Empty => i.elim) (Subsingleton.elim _ _)
      (fun i => i.elim) fun i => i.elim
  have : IsEmpty tM.G.left := ⟨fun x => isEmptyElim (tM.G.hom x)⟩
  obtain ⟨k, -⟩ := ObjMaps.exists_sab_id tM
  obtain ⟨A, -, rfl, rfl, rfl⟩ := exists_ampFrames (G := tM.G) (L := tM.PP.L) (N := m ^ 2)
    (A := ⟨PEmpty, fun i => i.elim, fun i => i.elim⟩) (n := n) (r := r) (s := s)
    ⟨Subsingleton.elim _ _, fun i => i.elim, fun i => i.elim⟩ (fun z => isEmptyElim z)
    ⟨fun i => i.elim, fun i => i.elim, fun i => i.elim, fun i => i.elim⟩
  refine hasModel_of_maps (𝟙 M) (𝟙 M) sM (fun x => isEmptyElim x) (hp _) inferInstance tM ?_
    ⟨⟨⊤, Subsingleton.elim _ _, ?_⟩, fun x => isEmptyElim x, fun x => isEmptyElim x⟩ rfl k k A
  · obtain ⟨N, i, hi, e⟩ := hp (tM.G.hom ≫ sM)
    exact ⟨N, i, inferInstance, inferInstance, e⟩
  · have : IsEmpty (⊤ : M.Opens).toScheme := ⟨fun x => isEmptyElim x.1⟩
    infer_instance

theorem good_of_two {Z Z₁ Z₂ : Scheme.{0}} {f₁ : Z₁ ⟶ Z} {f₂ : Z₂ ⟶ Z} [IsOpenImmersion f₁] [IsOpenImmersion f₂]
    {t : SAB H Z} {t₁ : SAB H Z₁} {t₂ : SAB H Z₂} (n₁ : SABMap t₁ t f₁) (n₂ : SABMap t₂ t f₂)
    (h : ∀ z, z ∈ Set.range f₁ ∨ z ∈ Set.range f₂) (g₁ : Models.Good t₁) (g₂ : Models.Good t₂) : Models.Good t := by
  let Y : Bool → Scheme.{0} := fun b => match b with | true => Z₁ | false => Z₂
  let f : ∀ b, Y b ⟶ Z := fun b => match b with | true => f₁ | false => f₂
  let u : ∀ b, SAB H (Y b) := fun b => match b with | true => t₁ | false => t₂
  let k : ∀ b, SABMap (u b) t (f b) := fun b => match b with | true => n₁ | false => n₂
  have ho : ∀ b, IsOpenImmersion (f b) := by rintro (_ | _) <;> assumption
  have hc : ∀ z, ∃ b, z ∈ Set.range (f b) := fun z => (h z).elim (fun h => ⟨true, h⟩) fun h => ⟨false, h⟩
  have hg : ∀ b, Models.Good (u b) := by rintro (_ | _) <;> assumption
  exact ⟨GlobalTheory.T.abelianLocus_isOpen_of_openImmersion_cover E H Z t _ Y f u k ho hc fun b => (hg b).1, GlobalTheory.T.fibresSplit_of_openImmersion_cover E H Z t _ Y f u k ho hc fun b => (hg b).2.1,
    GlobalTheory.T.hasFibrewiseTheta_of_openImmersion_cover E H Z t _ Y f u k ho hc fun b => (hg b).2.2⟩

theorem qproj_of_two {Z Z₁ Z₂ : Scheme.{0}} {f₁ : Z₁ ⟶ Z} {f₂ : Z₂ ⟶ Z} [IsOpenImmersion f₁] [IsOpenImmersion f₂]
    {t : SAB H Z} {t₁ : SAB H Z₁} {t₂ : SAB H Z₂} (n₁ : SABMap t₁ t f₁) (n₂ : SABMap t₂ t f₂)
    (h : IsCompl (Set.range f₁) (Set.range f₂)) (z : Z ⟶ Sp O) (g₁ : IsQProjOver (t₁.G.hom ≫ f₁ ≫ z))
    (g₂ : IsQProjOver (t₂.G.hom ≫ f₂ ≫ z)) : IsQProjOver (t.G.hom ≫ z) := by
  have key : ∀ {Y : Scheme.{0}} {f : Y ⟶ Z} {u : SAB H Y} (k : SABMap u t f),
      Set.range k.φ = t.G.hom ⁻¹' Set.range f := fun {Y f u} k => by
    rw [← Scheme.Pullback.range_fst, SABMap.φ, ← k.cart.1.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp,
      Set.range_comp, k.cart.1.isoPullback.hom.surjective.range_eq, Set.image_univ]
  refine GlobalTheory.T.isQProjOver_of_isCompl_openImmersions O _ _ _ n₁.φ n₂.φ _ (MorphismProperty.of_isPullback (P := @IsOpenImmersion) n₁.cart.1.flip ‹_›)
    (MorphismProperty.of_isPullback (P := @IsOpenImmersion) n₂.cart.1.flip ‹_›) ?_ ?_ ?_
  · rw [key, key]
    exact h.map (CompleteLatticeHom.setPreimage t.G.hom)
  · rwa [← Category.assoc, n₁.cart.1.w, Category.assoc]
  · rwa [← Category.assoc, n₂.cart.1.w, Category.assoc]

theorem amp_of_two {Z Z₁ Z₂ : Scheme.{0}} {f₁ : Z₁ ⟶ Z} {f₂ : Z₂ ⟶ Z} [IsOpenImmersion f₁] [IsOpenImmersion f₂]
    {t : SAB H Z} {t₁ : SAB H Z₁} {t₂ : SAB H Z₂} (n₁ : SABMap t₁ t f₁) (n₂ : SABMap t₂ t f₂)
    (h : IsCompl (Set.range f₁) (Set.range f₂)) {N : ℕ} (A₁ : LN.AmpFrames t₁.G t₁.PP.L N)
    (A₂ : LN.AmpFrames t₂.G t₂.PP.L N) (hn : A₂.n = A₁.n) (hr : A₂.r = A₁.r) (hs : A₂.s = A₁.s) :
    ∃ A : LN.AmpFrames t.G t.PP.L N, A.n = A₁.n ∧ A.r = A₁.r ∧ A.s = A₁.s := by
  have key : ∀ {Y : Scheme.{0}} {f : Y ⟶ Z} [IsOpenImmersion f] {u : SAB H Y} (k : SABMap u t f)
      (A : LN.AmpFrames u.G u.PP.L N), HasFrames t.G t.PP.L N (pushLB f A.A) A.n A.r A.s := fun {Y f _ u} k A =>
    GlobalTheory.T.transitionFrames_push_openImmersion_image _ _ _ _ f k.φ _ _ t.PP.isLB u.PP.isLB k.cart.1 (lbIso_of_map k)
      (fun x hx => (abLocus_pullback abLocusOne t.semi k.cart.1 x).1 hx) N _ _ _ _ (hasFrames_of_ampFrames A)
  have h₂ := key n₂ A₂
  rw [hn, hr, hs] at h₂
  obtain ⟨a, b⟩ := GlobalTheory.T.isAmpleCechLineBundle_disjointUnion_pushforward Z Z₁ Z₂ f₁ f₂ A₁.A A₂.A h A₁.isLB A₂.isLB A₁.ample A₂.ample
  obtain ⟨A, -, e⟩ := exists_ampFrames a b (GlobalTheory.T.hasFrames_disjointUnionCechData Z _ _ N _ _ _ _ _ (fun i j => le_bot_iff.1 (by
    rintro _ ⟨⟨x, -, rfl⟩, y, -, e⟩
    exact (Set.disjoint_left.1 h.disjoint ⟨x, rfl⟩ ⟨y, e⟩).elim)) (key n₁ A₁) h₂)
  exact ⟨A, e⟩

theorem HasModel.sum [IsNoetherianRing O] [IsReduced M] (hp : IsProper tM.G.hom) {V₁ V₂ : Scheme.{0}} (i₁ : V₁ ⟶ M)
    (i₂ : V₂ ⟶ M) [IsOpenImmersion i₁] [IsOpenImmersion i₂] (hd : Disjoint (Set.range i₁) (Set.range i₂))
    (hu : Dense (Set.range i₁ ∪ Set.range i₂)) {t₁ : SAB H V₁} {t₂ : SAB H V₂} (k₁ : SABMap t₁ tM i₁)
    (k₂ : SABMap t₂ tM i₂) (h₁ : HasModel (i₁ ≫ sM) t₁ m n r s) (h₂ : HasModel (i₂ ≫ sM) t₂ m n r s) :
    HasModel sM tM m n r s := by
  obtain ⟨C₁, rfl, rfl, rfl⟩ := h₁
  obtain ⟨C₂, hn, hr, hs⟩ := h₂
  have := isDominant_ι C₁.dense
  have := C₁.j_open
  have := C₁.j_dom
  have := isDominant_ι C₂.dense
  have := C₂.j_open
  have := C₂.j_dom
  have := C₁.flat
  have := C₂.flat
  have o₀ := isOpenImmersion_desc i₁ i₂ hd
  have d₀ : IsDominant (coprod.desc i₁ i₂) := ⟨by rwa [DenseRange, range_desc]⟩
  have o₁ := isOpenImmersion_map C₁.W.ι C₂.W.ι
  have d₁ := isDominant_map C₁.W.ι C₂.W.ι
  let a := coprod.map C₁.W.ι C₂.W.ι ≫ coprod.desc i₁ i₂
  have o₂ := isOpenImmersion_map C₁.j (𝟙 C₂.W.toScheme)
  have d₂ := isDominant_map C₁.j (𝟙 C₂.W.toScheme)
  have o₃ := isOpenImmersion_map (𝟙 C₁.Z) C₂.j
  have d₃ := isDominant_map (𝟙 C₁.Z) C₂.j
  have hZ := isNormalScheme_coprod C₁.normal C₂.normal
  have hP := ProjSpace.isProjOver_coprodDesc C₁.proj C₂.proj
  have := noetherianSpace_of_isProjOver hP
  have := isReduced_of_isNormalScheme hZ
  have : TopologicalSpace.NoetherianSpace (C₁.W.toScheme ⨿ C₂.W.toScheme : Scheme.{0}) :=
    (coprod.map C₁.j (𝟙 C₂.W.toScheme) ≫ coprod.map (𝟙 C₁.Z) C₂.j).isOpenEmbedding.isInducing.noetherianSpace
  have : TopologicalSpace.NoetherianSpace C₁.W.toScheme :=
    (coprod.inl : _ ⟶ C₁.W.toScheme ⨿ C₂.W.toScheme).isOpenEmbedding.isInducing.noetherianSpace
  have : TopologicalSpace.NoetherianSpace C₂.W.toScheme :=
    (coprod.inr : _ ⟶ C₁.W.toScheme ⨿ C₂.W.toScheme).isOpenEmbedding.isInducing.noetherianSpace
  obtain ⟨tY, ⟨p⟩⟩ := exists_pull a tM
  obtain ⟨q₁⟩ := map_comp C₁.m₁ k₁ rfl
  obtain ⟨q₂⟩ := map_comp C₂.m₁ k₂ rfl
  obtain ⟨p₁⟩ := map_cancel (g := coprod.inl) q₁ p (by rw [coprod.inl_map_assoc, coprod.inl_desc])
  obtain ⟨p₂⟩ := map_cancel (g := coprod.inr) q₂ p (by rw [coprod.inr_map_assoc, coprod.inr_desc])
  have pY := proper_of_map p hp
  obtain ⟨t', ⟨u₀⟩, ⟨u₁⟩⟩ := GlobalTheory.T.exists_abelianTriple_glue_two_open_immersions E H _ _ _ _ (coprod.map C₁.j (𝟙 C₂.W.toScheme)) coprod.inl coprod.inl C₁.j _ _ _
    p₁ C₁.m₂ o₂ inferInstance (isPullback_inl_inl_coprodMap _ _).flip (fun x => by
      obtain h | ⟨y, rfl⟩ := mem_inl_or_inr x
      · exact .inr h
      · exact .inl ⟨(coprod.inr : _ ⟶ C₁.W.toScheme ⨿ C₂.W.toScheme) y, by
          rw [← Scheme.Hom.comp_apply, coprod.inr_map, Category.id_comp]⟩)
    ⟨isReduced_of_isOpenImmersion a, fun _ _ _ _ _ _ _ => inferInstance⟩
    ⟨isReduced_of_isNormalScheme C₁.normal, genericPoints_subset_abLocus C₁.m₂ (proper_of_map q₁ hp)⟩
  obtain ⟨v₂⟩ := map_comp (k := coprod.inr) p₂ u₀ (by simp)
  obtain ⟨t, ⟨w₀⟩, ⟨w₂⟩⟩ := GlobalTheory.T.exists_abelianTriple_glue_two_open_immersions E H _ _ _ _ (coprod.map (𝟙 C₁.Z) C₂.j) coprod.inr coprod.inr C₂.j _ _ _
    v₂ C₂.m₂ o₃ inferInstance (isPullback_inr_inr_coprodMap _ _).flip (fun x => by
      obtain ⟨y, rfl⟩ | h := mem_inl_or_inr x
      · exact .inl ⟨(coprod.inl : _ ⟶ C₁.Z ⨿ C₂.W.toScheme) y, by
          rw [← Scheme.Hom.comp_apply, coprod.inl_map, Category.id_comp]⟩
      · exact .inr h)
    ⟨isReduced_of_isOpenImmersion (coprod.map (𝟙 C₁.Z) C₂.j), genericPoints_subset_abLocus u₀ pY⟩
    ⟨isReduced_of_isNormalScheme C₂.normal, genericPoints_subset_abLocus C₂.m₂ (proper_of_map q₂ hp)⟩
  obtain ⟨w₁⟩ := map_comp (k := coprod.inl) u₁ w₀ (by simp)
  obtain ⟨w⟩ := map_comp u₀ w₀ rfl
  obtain ⟨A, e₁, e₂, e₃⟩ := amp_of_two w₁ w₂ (isCompl_range_inl_inr _ _) C₁.amp C₂.amp hn hr hs
  rw [← e₁, ← e₂, ← e₃]
  refine hasModel_of_maps a _ (coprod.desc C₁.s C₂.s) hZ hP ?_ t
    (qproj_of_two w₁ w₂ (isCompl_range_inl_inr _ _) _ (by rw [coprod.inl_desc]; exact C₁.qproj)
      (by rw [coprod.inr_desc]; exact C₂.qproj))
    (good_of_two w₁ w₂ mem_inl_or_inr C₁.good C₂.good) ?_ p w A
  · have : IsZariskiLocalAtSource @Flat := HasRingHomProperty.instIsZariskiLocalAtSource
    refine IsZariskiLocalAtSource.of_openCover (P := @Flat) (coprodOpenCover.{0, 0} C₁.Z C₂.Z) ?_
    rintro (_ | _)
    · exact (coprod.inl_desc C₁.s C₂.s).symm ▸ C₁.flat
    · exact (coprod.inr_desc C₁.s C₂.s).symm ▸ C₂.flat
  · refine coprod.hom_ext ?_ ?_
    · simp only [a, Category.assoc, coprod.inl_map_assoc, coprod.inl_desc, coprod.inl_desc_assoc, Category.id_comp,
        C₁.j_over]
    · simp only [a, Category.assoc, coprod.inr_map_assoc, coprod.inr_desc, coprod.inr_desc_assoc, Category.id_comp,
        C₂.j_over]

theorem hasModel_sup [IsNoetherianRing O] [IsReduced M] (hp : IsProper tM.G.hom) {I : Type} (V : I → M.Opens)
    (hd : ∀ i j, i ≠ j → Disjoint (V i) (V j))
    (h : ∀ i (t : SAB H (V i).toScheme), SABMap t tM (V i).ι → HasModel ((V i).ι ≫ sM) t m n r s) (S : Finset I) :
    ∀ t : SAB H (S.sup V).toScheme, SABMap t tM (S.sup V).ι → HasModel ((S.sup V).ι ≫ sM) t m n r s := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro t _
    have : IsEmpty ((∅ : Finset I).sup V).toScheme := ⟨fun x => x.2⟩
    exact hasModel_of_isEmpty
  | insert a S ha ih =>
    intro t k
    have l₁ : V a ≤ (insert a S).sup V := Finset.le_sup (Finset.mem_insert_self a S)
    have l₂ : S.sup V ≤ (insert a S).sup V := Finset.sup_mono (Finset.subset_insert a S)
    have hD : Disjoint (V a) (S.sup V) := Finset.disjoint_sup_right.2 fun j hj => hd a j fun e => ha (e ▸ hj)
    obtain ⟨t₁, ⟨k₁⟩⟩ := exists_pull (M.homOfLE l₁) t
    obtain ⟨t₂, ⟨k₂⟩⟩ := exists_pull (M.homOfLE l₂) t
    obtain ⟨q₁⟩ := map_comp k₁ k (M.homOfLE_ι l₁)
    obtain ⟨q₂⟩ := map_comp k₂ k (M.homOfLE_ι l₂)
    refine HasModel.sum (proper_of_map k hp) (M.homOfLE l₁) (M.homOfLE l₂) (Set.disjoint_left.2 ?_) (fun x => ?_) k₁ k₂
      (by rw [Scheme.homOfLE_ι_assoc]; exact h a t₁ q₁) (by rw [Scheme.homOfLE_ι_assoc]; exact ih t₂ q₂)
    · rintro _ ⟨x, rfl⟩ ⟨y, e⟩
      have e' : y.1 = x.1 := (Scheme.homOfLE_apply l₂ y).symm.trans ((congrArg Subtype.val e).trans (Scheme.homOfLE_apply l₁ x))
      exact hD.le_bot (⟨x.2, e' ▸ y.2⟩ : x.1 ∈ V a ⊓ S.sup V)
    · refine subset_closure ?_
      obtain hx | hx : x.1 ∈ V a ∨ x.1 ∈ S.sup V := (Finset.sup_insert (s := S) (f := V) (b := a)).le x.2
      · exact .inl ⟨⟨x.1, hx⟩, Subtype.ext (by simp)⟩
      · exact .inr ⟨⟨x.1, hx⟩, Subtype.ext (by simp)⟩

theorem rank_eq (hL : Out.Laws) (hL' : Out.Laws2) (hp : IsProper tM.G.hom) (hA : Out.RelAmple tM.G tM.PP.L)
    (hK : Out.KTriv tM.G tM.PP.L) {g : ℕ} (hg : SmoothOfRelativeDimension g tM.G.hom) {R : Type} [CommRing R]
    [IsLocalRing R] {y : Sp R ⟶ M} {t' : SAB H (Sp R)} (k : SABMap t' tM y) {Z : Scheme.{0}} {t : SAB H Z}
    {χ : Sp R ⟶ Z} (k' : SABMap t' t χ) {N : ℕ} {T : Over Z} (h : Over.mk χ ⟶ T)
    (b : Fin n → LB.Sec (Out.LPow t.G t.PP.L (N : ℤ) T)) (hb : LN.BasisAlong t.G t.PP.L N h b) : n = max 1 (N ^ g) := by
  obtain ⟨b', hb'⟩ := GlobalTheory.T.pulledSectionsFormBasis_id_of_pulledSectionsFormBasis Z _ _ N n _ _ h b t.PP.isLB hb
  obtain ⟨e, he⟩ := GlobalTheory.T.exists_sectionPower_transport_cartesian_square Z _ t.G t'.G χ k'.φ _ _ t.PP.isLB t'.PP.isLB k'.cart.1 (lbIso_of_map k') N
  let e₀ := e (Over.mk (𝟙 (Sp R))) (Over.mk χ) (Iso.refl _) rfl
  have hb₀ : LN.BasisAlong t'.G t'.PP.L N (𝟙 (Over.mk (𝟙 (Sp R)))) (fun i => e₀.symm (b' i)) := fun σ => by
    have key : ∀ c, LN.Lin t'.G t'.PP.L N (𝟙 (Over.mk (𝟙 (Sp R)))) (fun i => e₀.symm (b' i)) c σ ↔
        LN.Lin t.G t.PP.L N (𝟙 (Over.mk χ)) b' c (e₀ σ) := fun c => by
      have := he _ _ _ _ (Iso.refl _) (Iso.refl _) rfl rfl (𝟙 (Over.mk (𝟙 (Sp R)))) (𝟙 (Over.mk χ)) rfl n
        (fun i => e₀.symm (b' i)) c σ
      refine this.trans ?_
      rw [show (fun i => e _ _ (Iso.refl _) rfl (e₀.symm (b' i))) = b' from funext fun i => e₀.apply_symm_apply _]
    simp only [key]
    exact hb' _
  have := t'.semi.smooth
  have := t'.semi.geomConnected
  obtain ⟨w, gw, -⟩ := k.lin
  obtain ⟨U, hU, hc, -⟩ := exists_isAffineOpen_mem_and_subset (X := M) (U := ⊤)
    (x := y (IsLocalRing.closedPoint R)) trivial
  have hy : ∀ x, y x ∈ U := fun x =>
    (congrArg (fun V => x ∈ V) (Scheme.preimage_eq_top_of_closedPoint_mem y hc)).mpr trivial
  have am := relAmple_pull k.cart.1 tM.PP.isLB t'.PP.isLB ((isGen_iff w).1 gw) U hU hy hA
  have kt := kTriv_pull k.cart tM.PP.isLB t'.PP.isLB ((isGen_iff w).1 gw) hK
  obtain ⟨-, ws, gs', -⟩ := t'.sym
  let P : Out.PolAV (Sp R) :=
    { A := t'.G, g := g, L := t'.PP.L, isLB := t'.PP.isLB, ample := am, ktriv := kt
      smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback k.cart.1 hg
      isAb := ⟨inferInstance, inferInstance, proper_of_map k hp, ‹_›⟩
      rigid := ⟨t'.PP.rig, t'.PP.rigGen⟩
      sym := fun _ => ⟨⊤, trivial, gen_of_iso ((isGen_iff ws).1 gs') _⟩ }
  obtain rfl | hN := Nat.eq_zero_or_pos N
  · rw [GlobalTheory.T.card_basis_polarisation_power_zero_eq_one hL.globalFns R P n _ hb₀, max_eq_left (pow_le_one₀ le_rfl zero_le_one)]
  · rw [GlobalTheory.T.card_pulledSectionsFormBasis_eq_pow_dim hL hL' R P N n _ hN hb₀, max_eq_right (Nat.one_le_pow _ _ hN)]

theorem hasModel_rank (hL : Out.Laws) (hL' : Out.Laws2) (hp : IsProper tM.G.hom) (hA : Out.RelAmple tM.G tM.PP.L)
    (hK : Out.KTriv tM.G tM.PP.L) {g : ℕ} (hg : SmoothOfRelativeDimension g tM.G.hom) {V : Scheme.{0}} {i : V ⟶ M}
    {tV : SAB H V} (k : SABMap tV tM i) {sV : V ⟶ Sp O} (C : ZOn sV tV m) [IsIntegral C.Z]
    (A : LN.AmpFrames C.t.G C.t.PP.L (m ^ 2)) : HasModel sV tV m (max 1 ((m ^ 2) ^ g)) A.r A.s := by
  suffices h : HasFrames C.t.G C.t.PP.L (m ^ 2) A.A (max 1 ((m ^ 2) ^ g)) A.r A.s by
    obtain ⟨A', -, e⟩ := exists_ampFrames A.isLB A.ample h
    exact ⟨{ C with amp := A' }, e⟩
  by_cases hT : ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], LN.CDvr W → IsEmpty (Sp W ⟶ C.Z)
  · exact GlobalTheory.T.hasTransitionCompatibleFrames_of_no_completeDVR_points _ _ _ _ _ _ _ _ _ (le_max_left _ _) hT (hasFrames_of_ampFrames A)
  push Not at hT
  obtain ⟨W, _, _, _, hW, ⟨χ₀⟩⟩ := hT
  have := hW.2.2
  obtain ⟨R, _, _, _, hR, χ, hχ⟩ := GlobalTheory.T.exists_completeDVR_point_genericPoint C.Z W χ₀
  have := C.j_open
  have := C.j_dom
  have hj : Set.range χ ⊆ Set.range C.j := by
    rintro _ ⟨y, rfl⟩
    rw [hχ]
    exact ((genericPoint_spec C.Z).mem_open_set_iff C.j.isOpenEmbedding.isOpen_range).2
      (by rw [Set.univ_inter]; exact C.j.denseRange.nonempty_iff.2 inferInstance |>.elim fun x => ⟨_, x, rfl⟩)
  obtain ⟨a, ha⟩ := exists_chart A.isLB (genericPoint C.Z)
  have hU : Set.range χ ⊆ Set.range (A.A.U a).ι := by
    rintro _ ⟨y, rfl⟩
    rw [hχ, Scheme.Opens.range_ι]
    exact ha
  obtain ⟨t', ⟨p⟩⟩ := exists_pull (IsOpenImmersion.lift C.j χ hj) C.tW
  obtain ⟨q⟩ := map_comp C.m₁ k rfl
  obtain ⟨p₁⟩ := map_comp p q rfl
  obtain ⟨p₂⟩ := map_comp (k := IsOpenImmersion.lift (A.A.U a).ι χ hU ≫ (A.A.U a).ι) p C.m₂
    (by rw [IsOpenImmersion.lift_fac, IsOpenImmersion.lift_fac])
  have hb := (A.trait a R hR (IsOpenImmersion.lift (A.A.U a).ι χ hU) (by
    rintro _ ⟨y, rfl⟩
    exact range_subset_abLocus p₂ (proper_of_map p₁ hp) ⟨_, rfl⟩)).2
  rw [← rank_eq hL hL' hp hA hK hg p₁ p₂ _ _ hb]
  exact hasFrames_of_ampFrames A

end GlobalTheory.ModelSum

namespace GlobalTheory

open ModelSum ZM in

theorem Models.nonempty_zOn_of_components : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (O : Type) [CommRing O] [IsNoetherianRing O] (MM : Scheme.{0}) (sM : MM ⟶ Sp O) (tM : SAB H MM) (m : ℕ), IsReduced MM → LocallyOfFiniteType sM → QuasiCompact sM → (∀ ξ ∈ genericPoints MM, ∃ (V : Scheme.{0}) (i : V ⟶ MM) (tV : SAB H V) (_ : SABMap tV tM i) (C : ZOn (i ≫ sM) tV m), IsOpenImmersion i ∧ ξ ∈ Set.range i ∧ IsIntegral V ∧ IsIntegral C.Z ∧ C.amp.s = 1 ∧ ∀ r : ℤ, C.amp.r ≤ r → ∃ A : GlobalTheory.LN.AmpFrames C.t.G C.t.PP.L (m ^ 2), A.r = r ∧ A.s = 1) → (∃ g, SmoothOfRelativeDimension g tM.G.hom) → Out.Laws → Out.Laws2 → IsProper tM.G.hom → Out.RelAmple tM.G tM.PP.L → Out.KTriv tM.G tM.PP.L → Nonempty (ZOn sM tM m) := by
  intro E _ _ _ H O _ _ M sM tM m hr hf hq h ⟨g, hg⟩ hL hL' hp hA hK
  have : IsLocallyNoetherian M := LocallyOfFiniteType.isLocallyNoetherian sM
  have : CompactSpace M := QuasiCompact.compactSpace_of_compactSpace sM
  have : IsNoetherian M := {}
  have hfin : (genericPoints M).Finite := genericPoints.finite TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
  have : Fintype (genericPoints M) := hfin.fintype
  choose V i tV k C ho hm hV hZ hs hC using fun ξ : genericPoints M => h ξ.1 ξ.2
  obtain ⟨r, hb⟩ := (Set.finite_range fun ξ => (C ξ).amp.r).bddAbove
  have gen : ∀ ξ x, ξ.1 ⤳ i ξ x := fun ξ x => by
    obtain ⟨v, hv⟩ := hm ξ
    have e : i ξ (genericPoint (V ξ)) = ξ.1 := eq_of_specializes_of_mem_genericPoints ξ.2
      (hv ▸ (genericPoint_specializes v).map (i ξ).continuous)
    exact e ▸ (genericPoint_specializes x).map (i ξ).continuous
  have key := hasModel_sup (sM := sM) (m := m) (n := max 1 ((m ^ 2) ^ g)) (r := r) (s := 1) hp
    (fun ξ => (i ξ).opensRange) (fun ξ ζ hne => disjoint_iff_inf_le.2 (by
      rintro _ ⟨⟨x, rfl⟩, hy⟩
      obtain ⟨c, hc⟩ := (gen ξ x).mem_open (i ζ).opensRange.2 hy
      exact (hne (Subtype.ext (eq_of_specializes_of_mem_genericPoints ξ.2 (hc ▸ gen ζ c)).symm)).elim))
    (fun ξ t q => by
      obtain ⟨A, rfl, e⟩ := hC ξ r (hb ⟨ξ, rfl⟩)
      obtain ⟨q'⟩ := map_cancel q (k ξ) (i ξ).isoOpensRange_inv_comp
      have := (hasModel_rank hL hL' hp hA hK hg (k ξ) (C ξ) A).shrink (i ξ).isoOpensRange.inv q'
      rwa [← Category.assoc, (i ξ).isoOpensRange_inv_comp, e] at this) Finset.univ
  obtain ⟨t, ⟨q⟩⟩ := exists_pull (Finset.univ.sup fun ξ => (i ξ).opensRange : M.Opens).ι tM
  have := isDominant_ι (W := Finset.univ.sup fun ξ => (i ξ).opensRange)
    ((dense_iff_closure_eq.2 (genericPoints.closure (α := M))).mono fun ξ hξ =>
      Finset.le_sup (f := fun ξ => (i ξ).opensRange) (Finset.mem_univ ⟨ξ, hξ⟩) (hm ⟨ξ, hξ⟩))
  exact ⟨(HasModel.grow _ q (key t q)).choose⟩

end GlobalTheory

end
