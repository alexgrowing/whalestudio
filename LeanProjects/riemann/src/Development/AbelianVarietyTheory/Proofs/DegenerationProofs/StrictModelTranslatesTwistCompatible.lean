import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompletionPointClosedPointMemOfSmooth
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsIntegralOfIsAbelianSchemeField
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TranslationBySection
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsOpenImmersionOfSections
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
namespace GlobalTheory.SS.Translates

theorem val_eq {T X X₁ X₂ O₁ O₂ Y S : Scheme.{0}} (d : T ⟶ X) {z : X} (hz : z ∈ closure (Set.range d))
    (u₁ : X ⟶ X₁) (u₂ : X ⟶ X₂) (i₁ : O₁ ⟶ X₁) (i₂ : O₂ ⟶ X₂) [IsOpenImmersion i₁] [IsOpenImmersion i₂]
    (p : O₁ ⟶ Y) (q : O₂ ⟶ Y) (π : Y ⟶ S) [IsSeparated π] (ρ₁ : X₁ ⟶ S) (ρ₂ : X₂ ⟶ S)
    (hp : p ≫ π = i₁ ≫ ρ₁) (hq : q ≫ π = i₂ ≫ ρ₂) (hu : u₁ ≫ ρ₁ = u₂ ≫ ρ₂)
    (h : ∀ (T' : Scheme.{0}) (a : T' ⟶ T) (t₁ : T' ⟶ O₁) (t₂ : T' ⟶ O₂), t₁ ≫ i₁ = a ≫ d ≫ u₁ →
      t₂ ≫ i₂ = a ≫ d ≫ u₂ → t₁ ≫ p = t₂ ≫ q)
    {o₁ : O₁} {o₂ : O₂} (h₁ : i₁ o₁ = u₁ z) (h₂ : i₂ o₂ = u₂ z) : p o₁ = q o₂ := by
  let O : X.Opens := u₁ ⁻¹ᵁ i₁.opensRange ⊓ u₂ ⁻¹ᵁ i₂.opensRange
  have r₁ : Set.range (O.ι ≫ u₁) ⊆ Set.range i₁ := by
    rintro _ ⟨x, rfl⟩; exact x.2.1
  have r₂ : Set.range (O.ι ≫ u₂) ⊆ Set.range i₂ := by
    rintro _ ⟨x, rfl⟩; exact x.2.2
  let l₁ := IsOpenImmersion.lift i₁ (O.ι ≫ u₁) r₁
  let l₂ := IsOpenImmersion.lift i₂ (O.ι ≫ u₂) r₂
  have e₁ : l₁ ≫ i₁ = O.ι ≫ u₁ := IsOpenImmersion.lift_fac _ _ _
  have e₂ : l₂ ≫ i₂ = O.ι ≫ u₂ := IsOpenImmersion.lift_fac _ _ _
  let o : O.toScheme := ⟨z, ⟨o₁, h₁⟩, ⟨o₂, h₂⟩⟩
  have f₁ : l₁ o = o₁ := i₁.isOpenEmbedding.injective (by
    rw [← Scheme.Hom.comp_apply, e₁, h₁]; rfl)
  have f₂ : l₂ o = o₂ := i₂.isOpenEmbedding.injective (by
    rw [← Scheme.Hom.comp_apply, e₂, h₂]; rfl)
  let P : Over.mk (O.ι ≫ u₁ ≫ ρ₁) ⟶ Over.mk π := Over.homMk (l₁ ≫ p) (by
    simp [hp, reassoc_of% e₁])
  let Q : Over.mk (O.ι ≫ u₁ ≫ ρ₁) ⟶ Over.mk π := Over.homMk (l₂ ≫ q) (by
    simp [hq, reassoc_of% e₂, hu])
  have : IsSeparated (Over.mk π).hom := ‹_›
  have hc : IsClosed (Set.range (equalizer.ι P Q).left) := (equalizer.ι P Q).left.isClosedEmbedding.isClosed_range
  have ho : o ∈ closure (Set.range (pullback.fst O.ι d)) := by
    rw [Scheme.Pullback.range_fst, ← O.ι.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage O.ι.continuous]
    exact hz
  let t : Over.mk (pullback.fst O.ι d ≫ O.ι ≫ u₁ ≫ ρ₁) ⟶ Over.mk (O.ι ≫ u₁ ≫ ρ₁) := Over.homMk (pullback.fst O.ι d)
  have ht : t ≫ P = t ≫ Q := by
    ext1
    have := h _ (pullback.snd O.ι d) (pullback.fst O.ι d ≫ l₁) (pullback.fst O.ι d ≫ l₂)
      (by rw [Category.assoc, e₁, pullback.condition_assoc]) (by rw [Category.assoc, e₂, pullback.condition_assoc])
    simpa [t, P, Q] using this
  have hs : Set.range (pullback.fst O.ι d) ⊆ Set.range (equalizer.ι P Q).left := by
    rintro _ ⟨x, rfl⟩
    exact ⟨(equalizer.lift t ht).left x, congr(($(equalizer.lift_ι t ht)).left x)⟩
  obtain ⟨e, he⟩ := hc.closure_subset_iff.2 hs ho
  have := congr(($(equalizer.condition P Q)).left e)
  rw [← f₁, ← f₂, ← he]
  exact this

variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K] {A A' A'' : Over (Sp K)}

def Ext (M : Model R A) (N : Model R A') (f : A ⟶ A') {X : Scheme.{0}} (i : X ⟶ M.Y.left) (g : X ⟶ N.Y.left) : Prop :=
  g ≫ N.Y.hom = i ≫ M.Y.hom ∧
    ∀ (T : Scheme.{0}) (t : T ⟶ X) (a : T ⟶ A.left), t ≫ i = a ≫ M.j → t ≫ g = a ≫ f.left ≫ N.j

theorem extends_iff {M : Model R A} {N : Model R A'} {f : A ⟶ A'} {U : M.Y.left.Opens} {g : U.toScheme ⟶ N.Y.left} :
    Extends M N f U g ↔ Ext M N f U.ι g := by
  refine and_congr_right fun _ => ⟨fun h T t a e => ?_, fun h => h _ _ _ (morphismRestrict_ι _ _)⟩
  have hp := isPullback_morphismRestrict M.j U
  rw [← hp.lift_fst t a e, Category.assoc, h, hp.lift_snd_assoc]

theorem isoAt_iff {M : Model R A} {N : Model R A'} {f : A ⟶ A'} {y : M.Y.left} :
    IsoAt M N f y ↔ ∃ (X : Scheme.{0}) (i : X ⟶ M.Y.left) (g : X ⟶ N.Y.left) (o : X),
      IsOpenImmersion i ∧ IsOpenImmersion g ∧ Ext M N f i g ∧ i o = y := by
  constructor
  · rintro ⟨U, g, hy, he, hg⟩
    exact ⟨U, U.ι, g, ⟨y, hy⟩, inferInstance, hg, extends_iff.1 he, rfl⟩
  · rintro ⟨X, i, g, o, hi, hg, he, rfl⟩
    refine ⟨i.opensRange, i.isoOpensRange.inv ≫ g, ⟨o, rfl⟩, extends_iff.2 ⟨?_, fun T t a e => ?_⟩, inferInstance⟩
    · rw [Category.assoc, he.1, Scheme.Hom.isoOpensRange_inv_comp_assoc]
    · rw [← Category.assoc]
      exact he.2 _ _ _ (by rw [Category.assoc, Scheme.Hom.isoOpensRange_inv_comp, e])

theorem isPullback_j (M : Model R A) : IsPullback M.j A.hom M.Y.hom (spMap (algebraMap R K)) := by
  refine IsPullback.of_iso_pullback ⟨M.j_hom⟩ ((Over.forget _).mapIso M.e.symm) rfl ?_
  exact Over.w M.e.inv

theorem Ext.comp {M : Model R A} {N : Model R A'} {P : Model R A''} {f : A ⟶ A'} {f' : A' ⟶ A''}
    {X X' : Scheme.{0}} {i : X ⟶ M.Y.left} {g : X ⟶ N.Y.left} {i' : X' ⟶ N.Y.left} {g' : X' ⟶ P.Y.left}
    (h : Ext M N f i g) (h' : Ext N P f' i' g') :
    Ext M P (f ≫ f') (pullback.fst g i' ≫ i) (pullback.snd g i' ≫ g') := by
  refine ⟨by rw [Category.assoc, h'.1, ← pullback.condition_assoc, h.1, Category.assoc], fun T t a e => ?_⟩
  have h1 := h.2 T (t ≫ pullback.fst g i') a (by rw [Category.assoc, e])
  have h2 := h'.2 T (t ≫ pullback.snd g i') (a ≫ f.left)
    (by rw [Category.assoc, ← pullback.condition, ← Category.assoc, h1, Category.assoc])
  simpa using h2

theorem Ext.div {M : Model R A} {N : Model R A'} {P : Model R A''} {u : A ⟶ A'} {f' : A' ≅ A''}
    {X X' : Scheme.{0}} {i : X ⟶ M.Y.left} {g : X ⟶ P.Y.left} {i' : X' ⟶ N.Y.left} {g' : X' ⟶ P.Y.left}
    (h : Ext M P (u ≫ f'.hom) i g) (h' : Ext N P f'.hom i' g') :
    Ext M N u (pullback.fst g g' ≫ i) (pullback.snd g g' ≫ i') := by
  refine ⟨by rw [Category.assoc, ← h'.1, ← pullback.condition_assoc, h.1, Category.assoc], fun T t a e => ?_⟩
  have h1 := h.2 T (t ≫ pullback.fst g g') a (by rw [Category.assoc, e])
  have h0 : (t ≫ pullback.snd g g' ≫ i') ≫ N.Y.hom = (a ≫ A.hom) ≫ spMap (algebraMap R K) := by
    simp only [Category.assoc]
    rw [← h'.1, ← pullback.condition_assoc, h.1, ← M.j_hom, ← reassoc_of% e]
  let b := (isPullback_j N).lift _ _ h0
  have b1 : b ≫ N.j = t ≫ pullback.snd g g' ≫ i' := IsPullback.lift_fst _ _ _ _
  have b2 : b ≫ A'.hom = a ≫ A.hom := IsPullback.lift_snd _ _ _ _
  have h2 := h'.2 T (t ≫ pullback.snd g g') b (by rw [b1, Category.assoc])
  have h3 : b ≫ f'.hom.left = (a ≫ u.left) ≫ f'.hom.left := by
    apply (isPullback_j P).hom_ext
    · rw [Category.assoc, ← h2, Category.assoc, ← pullback.condition, ← Category.assoc, h1]; simp
    · simp [b2]
  have : IsIso f'.hom.left := inferInstanceAs (IsIso ((Over.forget _).map f'.hom))
  rw [← b1, (cancel_mono _).1 h3, Category.assoc]

theorem isoAt_div {M : Model R A} {N : Model R A'} {P : Model R A''} {u : A ⟶ A'} {f' : A' ≅ A''}
    {X X' : Scheme.{0}} {i : X ⟶ M.Y.left} {g : X ⟶ P.Y.left} {i' : X' ⟶ N.Y.left} {g' : X' ⟶ P.Y.left}
    [IsOpenImmersion i] [IsOpenImmersion g] [IsOpenImmersion i'] [IsOpenImmersion g']
    (h : Ext M P (u ≫ f'.hom) i g) (h' : Ext N P f'.hom i' g') {o : X} {o' : X'} (e : g o = g' o') :
    IsoAt M N u (i o) := by
  obtain ⟨p, hp, -⟩ := Scheme.Pullback.exists_preimage_pullback o o' e
  exact isoAt_iff.2 ⟨_, _, _, p, inferInstance, inferInstance, h.div h', by rw [Scheme.Hom.comp_apply, hp]⟩

theorem dense_j [IsDomain R] [IsFractionRing R K] (M : Model R A) : Dense (Set.range M.j) := by
  have := M.smooth
  have h1 : Set.range M.j = M.Y.hom ⁻¹' Set.range (spMap (algebraMap R K)) := by
    rw [← Scheme.Pullback.range_fst, Model.j, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
    have : IsIso M.e.inv.left := inferInstanceAs (IsIso ((Over.forget _).map M.e.inv))
    rw [M.e.inv.left.surjective.range_eq, Set.image_univ]
  rw [h1]
  refine Dense.preimage ?_ M.Y.hom.isOpenMap
  have : DenseRange (PrimeSpectrum.comap (algebraMap R K)) :=
    (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2 (by
      rw [(RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R K)]; exact bot_le)
  exact this

theorem Ext.mem_sp [IsLocalRing R] {M : Model R A} {N : Model R A'} {f : A ⟶ A'}
    {X : Scheme.{0}} {i : X ⟶ M.Y.left} {g : X ⟶ N.Y.left} (h : Ext M N f i g) (o : X) :
    i o ∈ M.sp ↔ g o ∈ N.sp := by
  have e : N.Y.hom (g o) = M.Y.hom (i o) := congr($(h.1) o)
  simp only [Model.sp, Set.mem_setOf_eq, e]

theorem exists_meet [IsLocalRing R] {N : Model R A} (hN : N.Irr) {X X' : Scheme.{0}} (g : X ⟶ N.Y.left) (g' : X' ⟶ N.Y.left)
    [IsOpenImmersion g] [IsOpenImmersion g'] {o : X} {o' : X'} (h : g o ∈ N.sp) (h' : g' o' ∈ N.sp) :
    ∃ p p', g p ∈ N.sp ∧ g p = g' p' := by
  obtain ⟨y, hy, ⟨p, rfl⟩, p', hp'⟩ := hN.isPreirreducible _ _ g.isOpenEmbedding.isOpen_range
    g'.isOpenEmbedding.isOpen_range ⟨_, h, o, rfl⟩ ⟨_, h', o', rfl⟩
  exact ⟨p, p', hy, hp'.symm⟩

theorem exists_section_fibre [IsDomain R] [IsLocalRing R] (hR : SH R K) (M : Model R A)
    (y : ↥(pullback M.Y.hom (spMap (IsLocalRing.residue R)))) (hy : IsClosed {y}) :
    ∃ s : 𝟙_ (Over (Sp R)) ⟶ M.Y, s.left (IsLocalRing.closedPoint R) = pullback.fst M.Y.hom (spMap (IsLocalRing.residue R)) y := by
  obtain ⟨-, h2, h3, -⟩ := hR
  have := M.smooth
  let x₀ := pointOfClosedPoint (pullback.snd M.Y.hom (spMap (IsLocalRing.residue R))) y hy
  obtain ⟨⟨s, hs⟩, e⟩ := reducePoint_residue_surjective M.Y.hom R (𝟙 _)
    ⟨x₀ ≫ pullback.fst _ _, by
      rw [Category.assoc, pullback.condition, pointOfClosedPoint_comp_assoc, Category.comp_id]⟩
  have e' : spMap (IsLocalRing.residue R) ≫ s = x₀ ≫ pullback.fst _ _ := congrArg Subtype.val e
  refine ⟨Over.homMk s hs, ?_⟩
  have e2 : s (PrimeSpectrum.comap (IsLocalRing.residue R) (IsLocalRing.closedPoint (IsLocalRing.ResidueField R))) =
      pullback.fst M.Y.hom (spMap (IsLocalRing.residue R)) (x₀ (IsLocalRing.closedPoint (IsLocalRing.ResidueField R))) :=
    congr($e' (IsLocalRing.closedPoint (IsLocalRing.ResidueField R)))
  rw [IsLocalRing.comap_closedPoint] at e2
  exact e2.trans (congrArg _ (pointOfClosedPoint_apply _ y hy _))

theorem exists_section_closed [IsDomain R] [IsLocalRing R] (hR : SH R K) (M : Model R A) {z : M.Y.left}
    (hz : z ∈ M.sp) (hc : IsClosed {z}) :
    ∃ s : 𝟙_ (Over (Sp R)) ⟶ M.Y, s.left (IsLocalRing.closedPoint R) = z := by
  have : IsClosedImmersion (spMap (IsLocalRing.residue R)) := .spec_of_surjective _ IsLocalRing.residue_surjective
  obtain ⟨y, rfl⟩ : z ∈ Set.range (pullback.fst M.Y.hom (spMap (IsLocalRing.residue R))) := by
    rw [range_fst_residue]; exact hz
  refine exists_section_fibre hR M y ?_
  have := hc.preimage (pullback.fst M.Y.hom (spMap (IsLocalRing.residue R))).continuous
  rwa [← Set.image_singleton, Set.preimage_image_eq _
    (pullback.fst M.Y.hom (spMap (IsLocalRing.residue R))).isClosedEmbedding.injective] at this

theorem exists_section_open [IsDomain R] [IsLocalRing R] (hR : SH R K) (M : Model R A) {U : Set M.Y.left}
    (hU : IsOpen U) (hz : (M.sp ∩ U).Nonempty) :
    ∃ s : 𝟙_ (Over (Sp R)) ⟶ M.Y, s.left (IsLocalRing.closedPoint R) ∈ U := by
  have := M.smooth
  obtain ⟨z, hz, hzU⟩ := hz
  obtain ⟨y, rfl⟩ : z ∈ Set.range (pullback.fst M.Y.hom (spMap (IsLocalRing.residue R))) := by
    rw [range_fst_residue]; exact hz
  have : JacobsonSpace ↥(pullback M.Y.hom (spMap (IsLocalRing.residue R))) :=
    LocallyOfFiniteType.jacobsonSpace (pullback.snd M.Y.hom (spMap (IsLocalRing.residue R)))
  obtain ⟨c, hc, hc'⟩ := nonempty_inter_closedPoints
    (Z := pullback.fst M.Y.hom (spMap (IsLocalRing.residue R)) ⁻¹' U) ⟨y, hzU⟩
    (hU.preimage (pullback.fst M.Y.hom (spMap (IsLocalRing.residue R))).continuous).isLocallyClosed
  obtain ⟨s, hs⟩ := exists_section_fibre hR M c hc'
  exact ⟨s, hs ▸ hc⟩

theorem j_comm (M : Model R A) (N : Model R A') (f : A ⟶ A') (g : M.Y ⟶ N.Y)
    (h : M.e.inv ≫ (Over.pullback (spMap (algebraMap R K))).map g = f ≫ N.e.inv) : M.j ≫ g.left = f.left ≫ N.j := by
  have h2 := congrArg (fun q => q.left ≫ pullback.fst N.Y.hom (spMap (algebraMap R K))) h
  have h4 : ((Over.pullback (spMap (algebraMap R K))).map g).left ≫ pullback.fst N.Y.hom (spMap (algebraMap R K))
      = pullback.fst M.Y.hom (spMap (algebraMap R K)) ≫ g.left := pullback.lift_fst _ _ _
  simp only [Over.comp_left, Category.assoc] at h2
  unfold Model.j
  rw [Category.assoc]
  exact (congrArg (fun q => M.e.inv.left ≫ q) h4).symm.trans h2

def pj (M : Model R A) (N : Model R A') : (A ⊗ A').left ⟶ (M.Y ⊗ N.Y).left := (M.prod N).j

theorem pj_fst (M : Model R A) (N : Model R A') :
    pj M N ≫ (fst M.Y N.Y).left = (fst A A').left ≫ M.j :=
  j_comm (M.prod N) M (fst A A') (fst M.Y N.Y) (by simp [Model.prod])

theorem pj_snd (M : Model R A) (N : Model R A') :
    pj M N ≫ (snd M.Y N.Y).left = (snd A A').left ≫ N.j :=
  j_comm (M.prod N) N (snd A A') (snd M.Y N.Y) (by simp [Model.prod])

theorem j_lift (M : Model R A) (u v : M.Y ⟶ M.Y) (u' v' : A ⟶ A) (hu : M.j ≫ u.left = u'.left ≫ M.j)
    (hv : M.j ≫ v.left = v'.left ≫ M.j) : M.j ≫ (lift u v).left = (lift u' v').left ≫ pj M M := by
  have h1 : (M.j ≫ (lift u v).left) ≫ (fst M.Y M.Y).left = ((lift u' v').left ≫ pj M M) ≫ (fst M.Y M.Y).left := by
    rw [Category.assoc, Category.assoc, ← Over.comp_left, lift_fst, hu, pj_fst, ← Category.assoc, ← Over.comp_left, lift_fst]
  have h2 : (M.j ≫ (lift u v).left) ≫ (snd M.Y M.Y).left = ((lift u' v').left ≫ pj M M) ≫ (snd M.Y M.Y).left := by
    rw [Category.assoc, Category.assoc, ← Over.comp_left, lift_snd, hv, pj_snd, ← Category.assoc, ← Over.comp_left, lift_snd]
  exact pullback.hom_ext h1 h2

theorem j_const (M : Model R A) (s : 𝟙_ (Over (Sp R)) ⟶ M.Y) (a : 𝟙_ (Over (Sp K)) ⟶ A)
    (h : a.left ≫ M.j = spMap (algebraMap R K) ≫ s.left) :
    M.j ≫ (toUnit M.Y ≫ s).left = (toUnit A ≫ a).left ≫ M.j := by
  show M.j ≫ M.Y.hom ≫ s.left = (A.hom ≫ a.left) ≫ M.j
  rw [Category.assoc, h, ← Category.assoc, M.j_hom, Category.assoc]

theorem slice_val [IsDomain R] [IsFractionRing R K] (M : Model R A) (σ : M.Y ⟶ M.Y ⊗ M.Y) (σ' : A ⟶ A ⊗ A)
    (hσ : M.j ≫ σ.left = σ'.left ≫ pj M M) (F : A ⊗ A ⟶ A ⊗ A) {f : A ⟶ A} (hf : σ' ≫ F ≫ snd A A = f)
    {X X' : Scheme.{0}} {i g : X ⟶ M.Y.left} {I G : X' ⟶ (M.Y ⊗ M.Y).left} [IsOpenImmersion i] [IsOpenImmersion I]
    (h : Ext M M f i g) (h' : Ext (M.prod M) (M.prod M) F I G) {o : X} {o' : X'} (e : I o' = σ.left (i o)) :
    g o = (snd M.Y M.Y).left (G o') := by
  have := M.sep
  have h1 : G ≫ (M.Y ⊗ M.Y).hom = I ≫ (M.Y ⊗ M.Y).hom := h'.1
  have h2 : ∀ (T : Scheme.{0}) (t : T ⟶ X') (a : T ⟶ (A ⊗ A).left), t ≫ I = a ≫ pj M M →
    t ≫ G = a ≫ F.left ≫ pj M M := h'.2
  refine val_eq M.j (dense_j M (i o)) (𝟙 _) σ.left i I g (G ≫ (snd M.Y M.Y).left) M.Y.hom M.Y.hom (M.Y ⊗ M.Y).hom
    h.1 ?_ ?_ ?_ rfl e
  · rw [Category.assoc, ← h1, Over.w]
  · rw [Category.id_comp, Over.w]
  · intro T a t₁ t₂ e₁ e₂
    rw [h.2 T t₁ a (by simpa using e₁), ← Category.assoc t₂, h2 T t₂ (a ≫ σ'.left) (by rw [e₂, hσ, Category.assoc]), ← hf]
    simp only [Category.assoc, Over.comp_left, pj_snd]

theorem exists_right_slice (M : Model R A) (s : 𝟙_ (Over (Sp R)) ⟶ M.Y) (c : Sp R) (z : (M.Y ⊗ M.Y).left)
    (hz : (snd M.Y M.Y).left z = s.left c) :
    ∃ w, (lift (𝟙 M.Y) (toUnit M.Y ≫ s)).left w = z ∧ M.Y.hom w = c := by
  have h1 : (lift (𝟙 M.Y) (toUnit M.Y ≫ s)).left ≫ pullback.fst M.Y.hom M.Y.hom = 𝟙 _ :=
    congr(($(lift_fst (𝟙 M.Y) (toUnit M.Y ≫ s))).left)
  have h2 : (lift (𝟙 M.Y) (toUnit M.Y ≫ s)).left ≫ pullback.snd M.Y.hom M.Y.hom = M.Y.hom ≫ s.left :=
    congr(($(lift_snd (𝟙 M.Y) (toUnit M.Y ≫ s))).left)
  have h3 : s.left ≫ M.Y.hom = 𝟙 (Sp R) := Over.w s
  have hp : IsPullback (lift (𝟙 M.Y) (toUnit M.Y ≫ s)).left M.Y.hom (pullback.snd M.Y.hom M.Y.hom) s.left := by
    refine IsPullback.of_right ?_ h2 (IsPullback.of_hasPullback M.Y.hom M.Y.hom)
    rw [h1, h3]
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  obtain ⟨p, hp1, hp2⟩ := Scheme.Pullback.exists_preimage_pullback (f := pullback.snd M.Y.hom M.Y.hom) (g := s.left) z c hz
  refine ⟨hp.isoPullback.inv p, ?_, ?_⟩
  · rw [← Scheme.Hom.comp_apply, hp.isoPullback_inv_fst, hp1]
  · rw [← Scheme.Hom.comp_apply, hp.isoPullback_inv_snd, hp2]

theorem slice_swap (M : Model R A) (s s' : 𝟙_ (Over (Sp R)) ⟶ M.Y) (c : Sp R) :
    (lift (𝟙 M.Y) (toUnit M.Y ≫ s')).left (s.left c) = (lift (toUnit M.Y ≫ s) (𝟙 M.Y)).left (s'.left c) := by
  have : s ≫ lift (𝟙 M.Y) (toUnit M.Y ≫ s') = s' ≫ lift (toUnit M.Y ≫ s) (𝟙 M.Y) := by
    ext1 <;> simp [← Category.assoc, toUnit_unique (_ ≫ toUnit M.Y) (𝟙 _)]
  exact congr(($this).left c)

section Group
variable [GrpObj A] [IsCommMonObj A]

theorem comp_transl_hom {Z : Over (Sp K)} (f : Z ⟶ A) (a : 𝟙_ (Over (Sp K)) ⟶ A) :
    f ≫ (transl a).hom = (toUnit Z ≫ a) * f := by
  simp [transl, MonObj.comp_mul, ← Category.assoc, toUnit_unique (_ ≫ toUnit A) (toUnit Z)]

theorem transl_comm (a b : 𝟙_ (Over (Sp K)) ⟶ A) :
    (transl a).hom ≫ (transl b).hom = (transl b).hom ≫ (transl a).hom := by
  rw [comp_transl_hom, comp_transl_hom]
  exact mul_left_comm _ _ _

theorem left_shear (a : 𝟙_ (Over (Sp K)) ⟶ A) :
    lift (toUnit A ≫ a) (𝟙 A) ≫ shear A true ≫ snd A A = (transl a).hom := by
  simp [shear, transl, MonObj.comp_mul]

theorem right_shear (a : 𝟙_ (Over (Sp K)) ⟶ A) :
    lift (𝟙 A) (toUnit A ≫ a) ≫ shear A true ≫ snd A A = (transl a).hom := by
  simp only [shear, transl, MonObj.comp_mul, lift_snd, lift_fst]
  exact mul_comm _ _

theorem exists_shear_at [IsLocalRing R] {M : Model R A} (hM : Strict M) (s : 𝟙_ (Over (Sp R)) ⟶ M.Y) :
    ∃ (X : Scheme.{0}) (I G : X ⟶ (M.Y ⊗ M.Y).left) (o : X) (w : M.Y.left), IsOpenImmersion I ∧ IsOpenImmersion G ∧
      Ext (M.prod M) (M.prod M) (shear A true) I G ∧ w ∈ M.sp ∧ I o = (lift (𝟙 M.Y) (toUnit M.Y ≫ s)).left w := by
  have h3 : s.left ≫ M.Y.hom = 𝟙 (Sp R) := Over.w s
  obtain ⟨z, hz, h⟩ := (hM.2 true (s.left (IsLocalRing.closedPoint R)) congr($h3 (IsLocalRing.closedPoint R))).2
  obtain ⟨X, I, G, o, hI, hG, he, ho⟩ := isoAt_iff.1 h
  obtain ⟨w, hw, hw'⟩ := exists_right_slice M s _ z hz
  exact ⟨X, I, G, o, w, hI, hG, he, hw', ho.trans hw.symm⟩

theorem exists_translation [IsDomain R] [IsLocalRing R] (hR : SH R K) (hA : IsAbelianScheme A) {M : Model R A}
    (hM : Strict M) (s s' : 𝟙_ (Over (Sp R)) ⟶ M.Y) {W : Scheme.{0}} (k : W ⟶ M.Y.left) [IsOpenImmersion k]
    {q : W} (hq : k q ∈ M.sp) :
    ∃ (c : 𝟙_ (Over (Sp K)) ⟶ A) (X : Scheme.{0}) (i g : X ⟶ M.Y.left) (o : X) (q' : W),
      IsOpenImmersion i ∧ IsOpenImmersion g ∧ Ext M M (transl c).hom i g ∧
      i o = s.left (IsLocalRing.closedPoint R) ∧ g o = k q' ∧
      IsoAt M M (transl c).hom (s'.left (IsLocalRing.closedPoint R)) := by
  have := hR.2.2.2
  have hirr : M.Irr := hM.1.1
  obtain ⟨a, ha, ⟨y, hy, hy'⟩, -⟩ := GlobalTheory.SS.SectionTranslation.translation_by_section R K hR A hA M hM s
  obtain ⟨X₀, i₀, g₀, o₀, hi₀, hg₀, e₀, rfl⟩ := isoAt_iff.1 hy'
  obtain ⟨p, p', hp, hp'⟩ := exists_meet hirr g₀ k ((e₀.mem_sp _).1 hy) hq
  obtain ⟨X₁, I₁, G₁, o₁, w₁, hI₁, hG₁, e₁, hw₁, ho₁⟩ := exists_shear_at hM s
  obtain ⟨X₂, I₂, G₂, o₂, w₂, hI₂, hG₂, e₂, hw₂, ho₂⟩ := exists_shear_at hM s'
  let U₀ : Set M.Y.left := i₀ '' (g₀ ⁻¹' Set.range k)
  let U₁ : Set M.Y.left := (lift (𝟙 M.Y) (toUnit M.Y ≫ s)).left ⁻¹' Set.range I₁
  let U₂ : Set M.Y.left := (lift (𝟙 M.Y) (toUnit M.Y ≫ s')).left ⁻¹' Set.range I₂
  have hU₀ : IsOpen U₀ := i₀.isOpenEmbedding.isOpenMap _ (k.isOpenEmbedding.isOpen_range.preimage g₀.continuous)
  have hU₁ : IsOpen U₁ := I₁.isOpenEmbedding.isOpen_range.preimage (Scheme.Hom.continuous _)
  have hU₂ : IsOpen U₂ := I₂.isOpenEmbedding.isOpen_range.preimage (Scheme.Hom.continuous _)
  have hne : (M.sp ∩ (U₀ ∩ (U₁ ∩ U₂))).Nonempty :=
    hirr.isPreirreducible _ _ hU₀ (hU₁.inter hU₂) ⟨i₀ p, (e₀.mem_sp _).2 hp, p, ⟨p', hp'.symm⟩, rfl⟩
      (hirr.isPreirreducible _ _ hU₁ hU₂ ⟨w₁, hw₁, o₁, ho₁⟩ ⟨w₂, hw₂, o₂, ho₂⟩)
  obtain ⟨t, ⟨r, ⟨q', hq'⟩, hr⟩, ⟨n₁, hn₁⟩, n₂, hn₂⟩ := exists_section_open hR M (hU₀.inter (hU₁.inter hU₂)) hne
  obtain ⟨c, hc, -, hc'⟩ := GlobalTheory.SS.SectionTranslation.translation_by_section R K hR A hA M hM t
  have m₁ := hn₁.trans (slice_swap M t s _)
  have m₂ := hn₂.trans (slice_swap M t s' _)
  have k₁ : IsoAt M M (transl c).hom (s.left (IsLocalRing.closedPoint R)) :=
    hc' _ true (isoAt_iff.2 ⟨X₁, I₁, G₁, n₁, hI₁, hG₁, e₁, m₁⟩)
  have k₂ : IsoAt M M (transl c).hom (s'.left (IsLocalRing.closedPoint R)) :=
    hc' _ true (isoAt_iff.2 ⟨X₂, I₂, G₂, n₂, hI₂, hG₂, e₂, m₂⟩)
  obtain ⟨X, i, g, o, hi, hg, e, ho⟩ := isoAt_iff.1 k₁
  refine ⟨c, X, i, g, o, q', hi, hg, e, ho, ?_, k₂⟩
  have v₁ := slice_val M _ _ (j_lift M _ (𝟙 _) _ (𝟙 _) (j_const M t c hc) (by simp)) _ (left_shear c) e e₁
    (m₁.trans (congrArg _ ho.symm))
  have v₂ := slice_val M _ _ (j_lift M (𝟙 _) _ (𝟙 _) _ (by simp) (j_const M s a ha)) _ (right_shear a) e₀ e₁
    (hn₁.trans (congrArg _ hr.symm))
  exact v₁.trans (v₂.symm.trans hq'.symm)

end Group

theorem twist_j (M : Model R A) (f : A ≅ A') : (M.twist f).j = f.inv.left ≫ M.j := by
  simp [Model.twist, Model.j]

end GlobalTheory.SS.Translates

namespace GlobalTheory.SS
open Translates

theorem compat_twist_transl : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K], SH R K → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ M : Model R A, Strict M → ∀ a b : (𝟙_ (Over (Sp K)) ⟶ A), GenIso M M (transl a).hom → GenIso M M (transl b).hom → Compat (M.twist (transl a)) (M.twist (transl b)) := by
  intro R K _ _ _ _ _ hR A _ _ hA M hM a b ⟨xa, hxa, ha⟩ ⟨xb, hxb, hb⟩
  have := GlobalTheory.isIntegral_of_isAbelianScheme_field K A hA
  have := M.sep
  have hirr : M.Irr := hM.1.1
  let u : A ⟶ A := (transl a).hom ≫ (transl b).inv
  obtain ⟨Xa, ia, ga, oa, hia, hga, ea, rfl⟩ := isoAt_iff.1 ha
  obtain ⟨Xb, ib, gb, ob, hib, hgb, eb, rfl⟩ := isoAt_iff.1 hb
  obtain ⟨p, p', hp, hp'⟩ := exists_meet hirr ga gb ((ea.mem_sp _).1 hxa) ((eb.mem_sp _).1 hxb)
  have hu : IsoAt M M u (ia p) := isoAt_div (f' := transl b) (by simpa [u] using ea) eb hp'
  obtain ⟨W, k, h, q, hk, hh, eu, hq⟩ := isoAt_iff.1 hu
  have hw : ((transl a).inv.left ≫ M.j) ≫ M.Y.hom = ((transl b).inv.left ≫ M.j) ≫ M.Y.hom := by
    simp only [Category.assoc, M.j_hom, Over.w_assoc]
  let d : A.left ⟶ (M.Y ⊗ M.Y).left := pullback.lift _ _ hw
  have d1 : d ≫ (fst M.Y M.Y).left = (transl a).inv.left ≫ M.j := pullback.lift_fst _ _ _
  have d2 : d ≫ (snd M.Y M.Y).left = (transl b).inv.left ≫ M.j := pullback.lift_snd _ _ _
  refine GlobalTheory.SS.compat_of_isoAt_closure R K hR A _ _ d (d1.trans (twist_j M _).symm) (d2.trans (twist_j M _).symm) ?_
  intro (z : (M.Y ⊗ M.Y).left) hz hc hs
  obtain ⟨s, hs'⟩ := exists_section_closed hR (M.prod M) (z := z) hs hc
  have hs'' : (show 𝟙_ (Over (Sp R)) ⟶ M.Y ⊗ M.Y from s).left (IsLocalRing.closedPoint R) = z := hs'
  obtain ⟨c, X, i, g, o, q', hi, hg, e, ho, hgo, h₂⟩ := exists_translation hR hA hM
    ((show 𝟙_ (Over (Sp R)) ⟶ M.Y ⊗ M.Y from s) ≫ fst M.Y M.Y) ((show 𝟙_ (Over (Sp R)) ⟶ M.Y ⊗ M.Y from s) ≫ snd M.Y M.Y)
    k (q := q) (hq ▸ (ea.mem_sp _).2 hp)
  obtain ⟨X', i', g', o', hi', hg', e', ho'⟩ := isoAt_iff.1 h₂
  have ho1 : i o = (fst M.Y M.Y).left z := by rw [ho, ← hs'']; rfl
  have ho2 : i' o' = (snd M.Y M.Y).left z := by rw [ho', ← hs'']; rfl
  obtain ⟨r, hr, -⟩ := Scheme.Pullback.exists_preimage_pullback o q' hgo
  have hcu : (transl c).hom ≫ u = u ≫ (transl c).hom := by
    have : (transl c).hom ≫ (transl b).inv = (transl b).inv ≫ (transl c).hom := by
      rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp, transl_comm]
    simp only [u]
    rw [← Category.assoc, transl_comm, Category.assoc, this, Category.assoc]
  have E := e.comp eu
  rw [hcu] at E
  have hr' : (pullback.fst g k ≫ i) r = (fst M.Y M.Y).left z := by rw [Scheme.Hom.comp_apply, hr, ho1]
  have hv : (pullback.snd g k ≫ h) r = g' o' := by
    refine val_eq d hz (fst M.Y M.Y).left (snd M.Y M.Y).left (pullback.fst g k ≫ i) i' _ _ M.Y.hom M.Y.hom M.Y.hom
      E.1 e'.1 (by rw [Over.w, Over.w]) ?_ hr' ho2
    intro T x t₁ t₂ e₁ e₂
    rw [E.2 T t₁ (x ≫ (transl a).inv.left) (by rw [e₁, d1, Category.assoc]),
      e'.2 T t₂ (x ≫ (transl b).inv.left) (by rw [e₂, d2, Category.assoc])]
    have : (transl a).inv ≫ u ≫ (transl c).hom = (transl b).inv ≫ (transl c).hom := by simp [u]
    have h3 : (transl a).inv.left ≫ (u ≫ (transl c).hom).left = (transl b).inv.left ≫ (transl c).hom.left :=
      congr(($this).left)
    rw [Category.assoc x, Category.assoc x, reassoc_of% h3]
  have hfin := isoAt_div (f' := transl c) E e' hv
  rw [hr'] at hfin
  obtain ⟨Z, l, m, n, hl, hm, en, hn⟩ := isoAt_iff.1 hfin
  refine isoAt_iff.2 ⟨Z, l, m, n, hl, hm, ⟨en.1, fun T t x ex => ?_⟩, hn⟩
  have ex' : t ≫ l = (x ≫ (transl a).inv.left) ≫ M.j := by
    rw [Category.assoc, ← twist_j]; exact ex
  have : (transl a).inv ≫ u = (transl b).inv := by simp [u]
  have h3 : (transl a).inv.left ≫ u.left = (transl b).inv.left := congr(($this).left)
  refine (en.2 T t _ ex').trans ?_
  rw [Category.assoc, reassoc_of% h3, ← twist_j]
  exact congrArg _ (Category.id_comp _).symm

end GlobalTheory.SS
end
