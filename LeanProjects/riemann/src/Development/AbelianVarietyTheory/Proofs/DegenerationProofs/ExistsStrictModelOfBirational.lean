import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.GeometricallyIntegralOfIsIntegralOfIsAlgClosed
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModelMapGenericallyOpenImmersionCalculusStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ProdIrrAndWeakNeronStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.EqOnPoints
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

noncomputable section
namespace GlobalTheory.SS.StrictLaw

theorem fibre_preirr {P X Y S : Scheme.{0}} {p : P ⟶ X} {q : P ⟶ Y} {g : X ⟶ S} {f : Y ⟶ S}
    (h : IsPullback p q g f) (x : X)
    [hg : GeometricallyIrreducible (f.fiberToSpecResidueField (g x))] :
    IsPreirreducible (p ⁻¹' {x}) := by
  have h1 : IsPullback (p.fiberι x) (p.fiberToSpecResidueField x) p (X.fromSpecResidueField x) :=
    IsPullback.of_hasPullback _ _
  have h2 : IsPullback (f.fiberι (g x)) (f.fiberToSpecResidueField (g x)) f
      (S.fromSpecResidueField (g x)) := IsPullback.of_hasPullback _ _
  have h3 := h1.paste_horiz h.flip
  rw [← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField] at h3
  have h4 := IsPullback.of_right' h3 h2
  have h5 : IrreducibleSpace (p.fiber x) :=
    hg.geometrically_irreducibleSpace _ _ _ h4
  rw [← Scheme.Hom.range_fiberι, ← Set.image_univ]
  exact (PreirreducibleSpace.isPreirreducible_univ).image _ (p.fiberι x).continuous.continuousOn

theorem apply_eq_of_dominant {W X Y Z : Scheme.{0}} {a b : X ⟶ Y} (s : Y ⟶ Z) [IsSeparated s]
    (hs : a ≫ s = b ≫ s) (i : W ⟶ X) [IsDominant i] (hi : i ≫ a = i ≫ b) (x : X) : a x = b x := by
  first
  | (rename_i h_7 h_10; revert W X Y Z a b s h_7 hs i h_10 hi x; exact @_root_.GlobalTheory.EqualityOnPoints.eq_on_points)
  | exact @_root_.GlobalTheory.EqualityOnPoints.eq_on_points
  | exact _root_.GlobalTheory.EqualityOnPoints.eq_on_points
  | (apply _root_.GlobalTheory.EqualityOnPoints.eq_on_points <;> assumption)
  | (intros; apply _root_.GlobalTheory.EqualityOnPoints.eq_on_points <;> assumption)
  | (intros; apply @_root_.GlobalTheory.EqualityOnPoints.eq_on_points <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.EqualityOnPoints.eq_on_points ..)

variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K] {A A' : Over (Sp K)}

theorem extends_comp {M : Model R A} {N : Model R A'} {f : A ⟶ A'} {U : M.Y.left.Opens}
    {g : U.toScheme ⟶ N.Y.left} (h : Extends M N f U g) {T : Scheme.{0}} (t : T ⟶ A.left)
    (u : T ⟶ U.toScheme) (e : t ≫ M.j = u ≫ U.ι) : u ≫ g = t ≫ f.left ≫ N.j := by
  have hp := isPullback_morphismRestrict M.j U
  rw [← hp.lift_fst u t e.symm, Category.assoc, h.2, ← Category.assoc, hp.lift_snd]

theorem pullback_map_fst {X Y : Over (Sp R)} (g : X ⟶ Y) :
    ((Over.pullback (spMap (algebraMap R K))).map g).left ≫ pullback.fst Y.hom (spMap (algebraMap R K))
      = pullback.fst X.hom (spMap (algebraMap R K)) ≫ g.left := by
  exact pullback.lift_fst _ _ _

def pr₁ (M : Model R A) (N : Model R A') : (M.prod N).Y ⟶ M.Y := fst M.Y N.Y

def pr₂ (M : Model R A) (N : Model R A') : (M.prod N).Y ⟶ N.Y := snd M.Y N.Y

theorem prod_j_fst (M : Model R A) (N : Model R A') :
    (M.prod N).j ≫ (pr₁ M N).left = (fst A A').left ≫ M.j := by
  have : (M.prod N).e.inv ≫ (Over.pullback (spMap (algebraMap R K))).map (fst M.Y N.Y) = fst A A' ≫ M.e.inv := by
    simp [Model.prod]
  have h := congrArg (fun t => t.left ≫ pullback.fst M.Y.hom (spMap (algebraMap R K))) this
  simp only [Over.comp_left, Category.assoc] at h
  exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (pullback_map_fst _).symm).trans h)

theorem prod_j_snd (M : Model R A) (N : Model R A') :
    (M.prod N).j ≫ (pr₂ M N).left = (snd A A').left ≫ N.j := by
  have : (M.prod N).e.inv ≫ (Over.pullback (spMap (algebraMap R K))).map (snd M.Y N.Y) = snd A A' ≫ N.e.inv := by
    simp [Model.prod]
  have h := congrArg (fun t => t.left ≫ pullback.fst N.Y.hom (spMap (algebraMap R K))) this
  simp only [Over.comp_left, Category.assoc] at h
  exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (pullback_map_fst _).symm).trans h)

theorem isPullback_j (M : Model R A) :
    IsPullback M.j A.hom M.Y.hom (spMap (algebraMap R K)) := by
  refine (IsPullback.of_hasPullback M.Y.hom (spMap (algebraMap R K))).of_iso
    ((Over.forget _).mapIso M.e) (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ (by simp) (by simp)
  · have : M.e.hom.left ≫ M.e.inv.left = 𝟙 _ := by rw [← Over.comp_left]; simp
    show _ ≫ 𝟙 _ = M.e.hom.left ≫ M.e.inv.left ≫ _
    rw [← Category.assoc, this]; simp
  · exact (Category.comp_id _).trans (Over.w M.e.hom).symm

theorem isDominant_j [IsDomain R] [IsFractionRing R K] (M : Model R A) : IsDominant M.j := by
  have := M.smooth
  have hd : DenseRange (spMap (algebraMap R K)) := by
    show DenseRange (PrimeSpectrum.comap (algebraMap R K))
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
      (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R K)]
    exact bot_le
  refine ⟨(hd.preimage M.Y.hom.isOpenMap).mono ?_⟩
  rintro y ⟨s, hs⟩
  obtain ⟨a, ha, -⟩ := Scheme.exists_preimage_of_isPullback (isPullback_j M) y s hs.symm
  exact ⟨a, ha⟩

theorem j_notMem_sp [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] (M : Model R A)
    (a : A.left) : M.j a ∉ M.sp := by
  intro h
  have h1 : M.Y.hom (M.j a) = spMap (algebraMap R K) (A.hom a) := by
    rw [← Scheme.Hom.comp_apply, M.j_hom, Scheme.Hom.comp_apply]
  have h2 : spMap (algebraMap R K) (A.hom a) = IsLocalRing.closedPoint R := h1.symm.trans h
  have h3 := congrArg PrimeSpectrum.asIdeal h2
  apply IsDiscreteValuationRing.not_a_field R
  refine h3.symm.trans ?_
  show Ideal.comap (algebraMap R K) (PrimeSpectrum.asIdeal (A.hom a)) = ⊥
  rw [@Ideal.eq_bot_of_prime K _ (PrimeSpectrum.asIdeal (R := K) (A.hom a))
    (PrimeSpectrum.isPrime (R := K) (A.hom a))]
  exact (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R K)

theorem exists_restrict [IsNoetherianRing R] (M : Model R A) (V : M.Y.left.Opens)
    (hV : Set.range M.j ⊆ V) :
    ∃ (N : Model R A) (g : N.Y ⟶ M.Y), IsOpenImmersion g.left ∧ N.j ≫ g.left = M.j ∧
      Set.range g.left = V := by
  have := M.smooth
  have := M.sep
  have := M.qc
  have : IsLocallyNoetherian M.Y.left := LocallyOfFiniteType.isLocallyNoetherian M.Y.hom
  let j' : A.left ⟶ V.toScheme := IsOpenImmersion.lift V.ι M.j (by simpa using hV)
  have hj : j' ≫ V.ι = M.j := IsOpenImmersion.lift_fac _ _ _
  have h1 : IsPullback j' (𝟙 _) V.ι M.j := IsPullback.of_vert_isIso_mono ⟨by simp [hj]⟩
  have h2 := (h1.flip.paste_horiz (isPullback_j M).flip).flip
  rw [Category.id_comp] at h2
  refine ⟨⟨Over.mk (V.ι ≫ M.Y.hom), (Over.isoMk h2.isoPullback h2.isoPullback_hom_snd).symm,
    inferInstanceAs (Smooth (V.ι ≫ M.Y.hom)), inferInstanceAs (IsSeparated (V.ι ≫ M.Y.hom)),
    inferInstanceAs (QuasiCompact (V.ι ≫ M.Y.hom))⟩, Over.homMk V.ι rfl,
    (inferInstance : IsOpenImmersion V.ι), ?_, Scheme.Opens.range_ι V⟩
  exact (congrArg (· ≫ V.ι) h2.isoPullback_hom_fst).trans hj

theorem isoAt_of_open {M N : Model R A} {M' N' : Model R A'} {f : A ⟶ A'}
    (i : N.Y.left ⟶ M.Y.left) (i' : N'.Y.left ⟶ M'.Y.left) [IsOpenImmersion i] [IsOpenImmersion i']
    (hi : i ≫ M.Y.hom = N.Y.hom) (hi' : i' ≫ M'.Y.hom = N'.Y.hom)
    (hj : N.j ≫ i = M.j) (hj' : N'.j ≫ i' = M'.j)
    {U : M.Y.left.Opens} {g : U.toScheme ⟶ M'.Y.left} [IsOpenImmersion g] (h : Extends M M' f U g)
    (z : N.Y.left) (u : U.toScheme) (hu : U.ι u = i z) (hg : g u ∈ Set.range i') :
    IsoAt N N' f z := by
  let W : N.Y.left.Opens := i ⁻¹ᵁ (U.ι ''ᵁ (g ⁻¹ᵁ i'.opensRange))
  have h1 : Set.range (W.ι ≫ i) ⊆ Set.range U.ι := by
    rintro _ ⟨w, rfl⟩
    obtain ⟨v, -, hv⟩ := w.2
    exact ⟨v, hv⟩
  let l := IsOpenImmersion.lift U.ι (W.ι ≫ i) h1
  have hl : l ≫ U.ι = W.ι ≫ i := IsOpenImmersion.lift_fac _ _ _
  have h2 : Set.range (l ≫ g) ⊆ Set.range i' := by
    rintro _ ⟨w, rfl⟩
    obtain ⟨v, hv', hv⟩ := w.2
    have : U.ι (l w) = U.ι v := by
      rw [← Scheme.Hom.comp_apply, hl]; exact hv.symm
    rw [Scheme.Hom.comp_apply, U.ι.isOpenEmbedding.injective this]
    exact hv'
  let m := IsOpenImmersion.lift i' (l ≫ g) h2
  have hm : m ≫ i' = l ≫ g := IsOpenImmersion.lift_fac _ _ _
  refine ⟨W, m, ⟨u, hg, hu⟩, ⟨?_, ?_⟩, inferInstance⟩
  · rw [← hi', ← hi, ← Category.assoc, hm, Category.assoc, h.1, ← Category.assoc, hl, Category.assoc]
  · rw [← cancel_mono i', Category.assoc, hm, ← Category.assoc,
      extends_comp h (N.j ⁻¹ᵁ W).ι _ (by rw [Category.assoc, hl, ← hj, morphismRestrict_ι_assoc])]
    simp only [Category.assoc, hj']

theorem geomIrr [IsLocalRing R] [IsAlgClosed (IsLocalRing.ResidueField R)] (M : Model R A)
    (hM : M.Irr) (s : Sp R) (hs : s = IsLocalRing.closedPoint R) :
    GeometricallyIrreducible (M.Y.hom.fiberToSpecResidueField s) := by
  have := M.smooth
  have h0 : s.asIdeal = IsLocalRing.maximalIdeal R := by rw [hs]; rfl
  have h0' : s.asIdeal.IsMaximal := h0 ▸ IsLocalRing.maximalIdeal.isMaximal R
  have h1 : IsAlgClosed s.asIdeal.ResidueField :=
    IsAlgClosed.of_ringEquiv (IsLocalRing.ResidueField R) _
      ((Ideal.quotEquivOfEq h0.symm).trans
        (RingEquiv.ofBijective _ (Ideal.bijective_algebraMap_quotient_residueField _)))
  have h2 : IsAlgClosed ((Sp R).residueField s) :=
    IsAlgClosed.of_ringEquiv s.asIdeal.ResidueField _
      (Scheme.Spec.residueFieldIso (CommRingCat.of R) s).commRingCatIsoToRingEquiv.symm
  have h3 : IrreducibleSpace (M.Y.hom.fiber s) := by
    have : IrreducibleSpace (M.Y.hom ⁻¹' {s} : Set _) :=
      Subtype.irreducibleSpace (hs ▸ hM)
    exact (M.Y.hom.fiberHomeo _).irreducibleSpace_iff.2 this
  have h4 : LocallyOfFiniteType (M.Y.hom.fiberToSpecResidueField s) :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd _ _))
  exact @geometricallyIrreducible_of_isAlgClosed _ _ h2 _ _ h4 h3

theorem exists_pt {P U Y : Type*} [TopologicalSpace P] [TopologicalSpace U] (p : P → Y) (x : Y)
    (hF : IsPreirreducible (p ⁻¹' {x})) (i g : U → P) (hi : Continuous i) (hg : IsOpenMap g)
    (h : ∀ u, p (g u) = p (i u)) (W O : Set P) (hW : IsOpen W) (hO : IsOpen O)
    (hWi : W ⊆ Set.range i) (h1 : (p ⁻¹' {x} ∩ W).Nonempty) (h2 : (p ⁻¹' {x} ∩ O).Nonempty) :
    ∃ u, i u ∈ W ∧ p (i u) = x ∧ g u ∈ O := by
  obtain ⟨w, hw, hwW⟩ := h1
  obtain ⟨u, rfl⟩ := hWi hwW
  obtain ⟨_, hz, ⟨v, hv, rfl⟩, hzO⟩ := hF _ _ (hg _ (hW.preimage hi)) hO
    ⟨g u, (h u).trans hw, u, hwW, rfl⟩ h2
  exact ⟨v, hv, (h v).symm.trans hz, hzO⟩

theorem ext_pt [IsDomain R] [IsFractionRing R K] {B B' : Over (Sp K)} {M : Model R A}
    {N : Model R B} {N' : Model R B'} {Q : Model R A'} {f : A ⟶ B} {f' : A ⟶ B'}
    {U U' : M.Y.left.Opens} {g : U.toScheme ⟶ N.Y.left} {g' : U'.toScheme ⟶ N'.Y.left}
    (h : Extends M N f U g) (h' : Extends M N' f' U' g') (p : N.Y ⟶ Q.Y) (p' : N'.Y ⟶ Q.Y)
    (e : f.left ≫ N.j ≫ p.left = f'.left ≫ N'.j ≫ p'.left)
    (u : U.toScheme) (u' : U'.toScheme) (hu : U.ι u = U'.ι u') :
    p.left (g u) = p'.left (g' u') := by
  have := Q.sep
  have := isDominant_j M
  let W := U ⊓ U'
  let a : W.toScheme ⟶ U.toScheme := M.Y.left.homOfLE inf_le_left
  let a' : W.toScheme ⟶ U'.toScheme := M.Y.left.homOfLE inf_le_right
  have ha : a ≫ U.ι = W.ι := Scheme.homOfLE_ι _ _
  have ha' : a' ≫ U'.ι = W.ι := Scheme.homOfLE_ι _ _
  have hd : IsDominant (M.j ∣_ W) := IsZariskiLocalAtTarget.restrict this W
  have hw : U.ι u ∈ W := ⟨u.2, hu ▸ u'.2⟩
  obtain ⟨w, hw⟩ : ∃ w : W.toScheme, W.ι w = U.ι u := ⟨⟨_, hw⟩, rfl⟩
  have key := apply_eq_of_dominant (a := a ≫ g ≫ p.left) (b := a' ≫ g' ≫ p'.left) Q.Y.hom
    (by simp only [Category.assoc, Over.w, h.1, h'.1, reassoc_of% ha, reassoc_of% ha'])
    (M.j ∣_ W) (by
      have e1 := extends_comp h (M.j ⁻¹ᵁ W).ι (M.j ∣_ W ≫ a)
        (by rw [Category.assoc, ha, morphismRestrict_ι])
      have e2 := extends_comp h' (M.j ⁻¹ᵁ W).ι (M.j ∣_ W ≫ a')
        (by rw [Category.assoc, ha', morphismRestrict_ι])
      rw [Category.assoc] at e1 e2
      rw [reassoc_of% e1, reassoc_of% e2, e]) w
  have b1 : a w = u := U.ι.isOpenEmbedding.injective (by
    rw [← Scheme.Hom.comp_apply, ha, hw])
  have b2 : a' w = u' := U'.ι.isOpenEmbedding.injective (by
    rw [← Scheme.Hom.comp_apply, ha', ← hu, hw])
  simpa only [Scheme.Hom.comp_apply, b1, b2] using key

def Good (M : Model R A) (f : A ⊗ A ⟶ A ⊗ A) (V : Set M.Y.left) (z : (M.prod M).Y.left) : Prop :=
  ∃ (U : (M.prod M).Y.left.Opens) (g : U.toScheme ⟶ (M.prod M).Y.left) (u : U.toScheme),
    Extends (M.prod M) (M.prod M) f U g ∧ IsOpenImmersion g ∧ U.ι u = z ∧
    (pr₁ M M).left z ∈ V ∧ (pr₂ M M).left z ∈ V ∧
    (pr₁ M M).left (g u) ∈ V ∧ (pr₂ M M).left (g u) ∈ V

theorem isPullback_prod (M : Model R A) (N : Model R A') :
    IsPullback (pr₁ M N).left (pr₂ M N).left M.Y.hom N.Y.hom := IsPullback.of_hasPullback _ _

section
variable [IsDomain R] [IsLocalRing R] [IsFractionRing R K]
  [IsAlgClosed (IsLocalRing.ResidueField R)]

theorem fst_case (M : Model R A) (hM : M.Irr) (f : A ⊗ A ⟶ A ⊗ A) (hf : f ≫ fst A A = fst A A)
    (h : GenIso (M.prod M) (M.prod M) f) :
    ∃ T : Set M.Y.left, IsOpen T ∧ (M.sp ∩ T).Nonempty ∧ ∀ V : Set M.Y.left, IsOpen V →
      ∀ x ∈ M.sp, x ∈ T → x ∈ V → ∃ z, (pr₁ M M).left z = x ∧ Good M f V z := by
  obtain ⟨y, hy, U, g, hyU, he, hg⟩ := h
  have := M.smooth
  have hp := isPullback_prod M M
  have ho : UniversallyOpen (pr₁ M M).left :=
    MorphismProperty.of_isPullback hp.flip inferInstance
  refine ⟨(pr₁ M M).left '' U, (pr₁ M M).left.isOpenMap _ U.2, ⟨_, hy, y, hyU, rfl⟩, ?_⟩
  rintro V hV x hx ⟨w, hwU, hw⟩ hxV
  have := geomIrr M hM (M.Y.hom x) hx
  have hF := fibre_preirr hp x
  have hc : ∀ u, (pr₁ M M).left (g u) = (pr₁ M M).left (U.ι u) := fun u =>
    ext_pt (Q := M) he (extends_id _ U) (pr₁ M M) (pr₁ M M) (by
      rw [prod_j_fst, ← Category.assoc, ← Over.comp_left, hf]; simp) u u rfl
  have hO : IsOpen ((pr₂ M M).left ⁻¹' V) := hV.preimage (pr₂ M M).left.continuous
  obtain ⟨d, hd, hd'⟩ := Scheme.exists_preimage_of_isPullback hp x x rfl
  have hd2 : ((pr₁ M M).left ⁻¹' {x} ∩ (pr₂ M M).left ⁻¹' V).Nonempty :=
    ⟨d, hd, show (pr₂ M M).left d ∈ V from hd' ▸ hxV⟩
  obtain ⟨u, hu, hux, hgu⟩ := exists_pt (pr₁ M M).left x hF U.ι g U.ι.continuous
    g.isOpenEmbedding.isOpenMap hc (U ∩ (pr₂ M M).left ⁻¹' V) _ (U.2.inter hO) hO
    (fun z hz => ⟨⟨z, hz.1⟩, rfl⟩) (hF _ _ U.2 hO ⟨w, hw, hwU⟩ hd2) hd2
  exact ⟨_, hux, U, g, u, he, hg, rfl, hux ▸ hxV, hu.2, ((hc u).trans hux) ▸ hxV, hgu⟩

theorem snd_case (M : Model R A) (hM : M.Irr) (hMM : (M.prod M).Irr) (f f' : A ⊗ A ⟶ A ⊗ A)
    (hf : f ≫ fst A A = fst A A) (hf' : f' ≫ snd A A = snd A A)
    (hff : f ≫ snd A A = f' ≫ fst A A)
    (h : GenIso (M.prod M) (M.prod M) f) (h' : GenIso (M.prod M) (M.prod M) f') :
    ∃ T : Set M.Y.left, IsOpen T ∧ (M.sp ∩ T).Nonempty ∧ ∀ V : Set M.Y.left, IsOpen V →
      ∀ x ∈ M.sp, x ∈ T → x ∈ V → ∃ z, (pr₂ M M).left z = x ∧ Good M f V z := by
  obtain ⟨y, hy, U, g, hyU, he, hg⟩ := h
  obtain ⟨y', hy', U', g', hyU', he', hg'⟩ := h'
  have := M.smooth
  have hp := (isPullback_prod M M).flip
  have ho : UniversallyOpen (pr₂ M M).left :=
    MorphismProperty.of_isPullback hp.flip inferInstance
  obtain ⟨y₀, hy₀, hy₀U⟩ := hMM.2 _ _ U.2 U'.2 ⟨y, hy, hyU⟩ ⟨y', hy', hyU'⟩
  have hUU : IsOpen ((U : Set (M.prod M).Y.left) ∩ U') := U.2.inter U'.2
  refine ⟨(pr₂ M M).left '' (U ∩ U'), (pr₂ M M).left.isOpenMap _ hUU,
    ⟨_, ?_, y₀, hy₀U, rfl⟩, ?_⟩
  · show M.Y.hom _ = _
    rw [← Scheme.Hom.comp_apply, Over.w]
    exact hy₀
  rintro V hV x hx ⟨w, hwU, hw⟩ hxV
  have := geomIrr M hM (M.Y.hom x) hx
  have hF := fibre_preirr hp x
  have hc : ∀ u, (pr₁ M M).left (g u) = (pr₁ M M).left (U.ι u) := fun u =>
    ext_pt (Q := M) he (extends_id _ U) (pr₁ M M) (pr₁ M M) (by
      rw [prod_j_fst, ← Category.assoc, ← Over.comp_left, hf]; simp) u u rfl
  have hc' : ∀ u, (pr₂ M M).left (g' u) = (pr₂ M M).left (U'.ι u) := fun u =>
    ext_pt (Q := M) he' (extends_id _ U') (pr₂ M M) (pr₂ M M) (by
      rw [prod_j_snd, ← Category.assoc, ← Over.comp_left, hf']; simp) u u rfl
  have hO : IsOpen ((pr₁ M M).left ⁻¹' V) := hV.preimage (pr₁ M M).left.continuous
  obtain ⟨d, hd, hd'⟩ := Scheme.exists_preimage_of_isPullback hp x x rfl
  have hd2 : ((pr₂ M M).left ⁻¹' {x} ∩ (pr₁ M M).left ⁻¹' V).Nonempty :=
    ⟨d, hd, show (pr₁ M M).left d ∈ V from hd' ▸ hxV⟩
  obtain ⟨u', hu, hux, hgu⟩ := exists_pt (pr₂ M M).left x hF U'.ι g' U'.ι.continuous
    g'.isOpenEmbedding.isOpenMap hc' ((U ∩ U') ∩ (pr₁ M M).left ⁻¹' V) _ (hUU.inter hO) hO
    (fun z hz => ⟨⟨z, hz.1.2⟩, rfl⟩) (hF _ _ hUU hO ⟨w, hw, hwU⟩ hd2) hd2
  let u : U.toScheme := ⟨U'.ι u', hu.1.1⟩
  have huu : U.ι u = U'.ι u' := rfl
  have hc'' : (pr₂ M M).left (g u) = (pr₁ M M).left (g' u') :=
    ext_pt (Q := M) he he' (pr₂ M M) (pr₁ M M) (by
      rw [prod_j_fst, prod_j_snd, ← Category.assoc, ← Over.comp_left, hff, Over.comp_left,
        Category.assoc]) u u' huu
  exact ⟨_, hux, U, g, u, he, hg, huu, hu.2, hux ▸ hxV, (hc u) ▸ hu.2, hc'' ▸ hgu⟩
end

theorem good_isoAt {M N : Model R A} (i : N.Y ⟶ M.Y) [IsOpenImmersion i.left]
    (hj : N.j ≫ i.left = M.j) {f : A ⊗ A ⟶ A ⊗ A} {z : (M.prod M).Y.left}
    (h : Good M f (Set.range i.left) z) :
    ∃ w : (N.prod N).Y.left, i.left ((pr₁ N N).left w) = (pr₁ M M).left z ∧
      i.left ((pr₂ N N).left w) = (pr₂ M M).left z ∧
      IsoAt (N.prod N) (N.prod N) f w := by
  obtain ⟨U, g, u, he, hg, hu, h1, h2, h3, h4⟩ := h
  let ii : (N.prod N).Y ⟶ (M.prod M).Y := i ⊗ₘ i
  have e1 : ii.left ≫ (pr₁ M M).left = (pr₁ N N).left ≫ i.left := by
    exact congrArg (fun t => t.left) (tensorHom_fst i i)
  have e2 : ii.left ≫ (pr₂ M M).left = (pr₂ N N).left ≫ i.left := by
    exact congrArg (fun t => t.left) (tensorHom_snd i i)
  have e : ii.left = pullback.map N.Y.hom N.Y.hom M.Y.hom M.Y.hom i.left i.left (𝟙 _)
      (by simp) (by simp) := by
    apply pullback.hom_ext
    · exact e1.trans (pullback.lift_fst _ _ _).symm
    · exact e2.trans (pullback.lift_snd _ _ _).symm
  have ho : IsOpenImmersion ii.left := by
    rw [e]
    exact MorphismProperty.pullbackMap (P := @IsOpenImmersion) ‹_› ‹_› (Over.w i).symm (Over.w i).symm
  have hr : ∀ t, (pr₁ M M).left t ∈ Set.range i.left → (pr₂ M M).left t ∈ Set.range i.left →
      t ∈ Set.range ii.left := by
    intro t ht ht'
    rw [e]
    exact (Scheme.Pullback.range_map _ _ _ _ _ _ _ _ _).ge ⟨ht, ht'⟩
  have hj' : (N.prod N).j ≫ ii.left = (M.prod M).j := by
    apply (isPullback_prod M M).hom_ext
    · rw [prod_j_fst, ← hj, ← Category.assoc, ← prod_j_fst N N, Category.assoc, Category.assoc]
      exact congrArg (_ ≫ ·) e1
    · rw [prod_j_snd, ← hj, ← Category.assoc, ← prod_j_snd N N, Category.assoc, Category.assoc]
      exact congrArg (_ ≫ ·) e2
  obtain ⟨w, hw⟩ := hr z h1 h2
  refine ⟨w, ?_, ?_, @isoAt_of_open R _ K _ _ _ _ (M.prod M) (N.prod N) (M.prod M) (N.prod N) f
    ii.left ii.left ho ho (Over.w _) (Over.w _) hj' hj' U g hg he w u
    (hu.trans hw.symm) (hr _ h3 h4)⟩
  · rw [← hw, ← Scheme.Hom.comp_apply, ← e1, Scheme.Hom.comp_apply]
  · rw [← hw, ← Scheme.Hom.comp_apply, ← e2, Scheme.Hom.comp_apply]

theorem shear_fst [GrpObj A] (b : Bool) : shear A b ≫ fst A A = fst A A := by
  cases b <;> simp [shear]

def coshear (A : Over (Sp K)) [GrpObj A] : Bool → (A ⊗ A ⟶ A ⊗ A)
  | true => (β_ A A).hom ≫ shear A true ≫ (β_ A A).hom
  | false => (ι[A] ⊗ₘ 𝟙 A) ≫ (β_ A A).hom ≫ shear A true ≫ (β_ A A).hom

theorem coshear_snd [GrpObj A] (b : Bool) : coshear A b ≫ snd A A = snd A A := by
  cases b <;> simp [coshear, shear]

theorem shear_snd [GrpObj A] [IsCommMonObj A] (b : Bool) :
    shear A b ≫ snd A A = coshear A b ≫ fst A A := by
  cases b
  · simp only [coshear, shear, Category.assoc, braiding_hom_fst, lift_snd, MonObj.comp_mul,
      braiding_hom_snd, tensorHom_fst, tensorHom_snd, Category.comp_id]
    rw [mul_comm]; rfl
  · simp only [coshear, shear, Category.assoc, braiding_hom_fst, lift_snd, MonObj.comp_mul,
      braiding_hom_snd]
    rw [mul_comm]

end GlobalTheory.SS.StrictLaw

namespace GlobalTheory.SS
open StrictLaw

theorem exists_strict_le : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K], SH R K → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ M : Model R A, BirLaw M → ∃ N : Model R A, Strict N ∧ N.Le M := by
  intro R K _ _ _ _ _ hSH A _ _ _ M ⟨hM, hs, hι⟩
  obtain ⟨gLe, gComp, gIso, gProd, gBr⟩ := GlobalTheory.T.modelMapGenericallyOpenImmersion_calculus R K hSH
  have hMM := (GlobalTheory.T.prod_irr_and_weakNeron' R K hSH A A).1 M M hM hM
  obtain ⟨hdvr, -, hac, hfr⟩ := hSH
  have hβ := (gBr A A A M M M hM hM hM).2
  have ht : GenIso (M.prod M) (M.prod M) (coshear A true) :=
    gComp _ _ _ _ _ _ _ _ hMM hβ (gComp _ _ _ _ _ _ _ _ hMM (hs true) hβ)
  have hco : ∀ b, GenIso (M.prod M) (M.prod M) (coshear A b) := by
    intro b
    cases b
    · exact gComp _ _ _ _ _ _ _ _ hMM
        (gProd _ _ _ _ _ _ _ _ _ _ hι (gLe A M M hM M.le_refl)) ht
    · exact ht
  choose T hT hTne hTx using fun b => fst_case M hM (shear A b) (shear_fst b) (hs b)
  choose T' hT' hTne' hTx' using fun b => snd_case M hM hMM (shear A b) (coshear A b)
    (shear_fst b) (coshear_snd b) (shear_snd b) (hs b) (hco b)
  have hcl : IsClosed M.sp :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal (IsLocalRing.closedPoint R)).2
      (IsLocalRing.maximalIdeal.isMaximal R) |>.preimage M.Y.hom.continuous
  let W : Set M.Y.left := (T true ∩ T false) ∩ (T' true ∩ T' false)
  have hW : IsOpen W := ((hT _).inter (hT _)).inter ((hT' _).inter (hT' _))
  have hWne : (M.sp ∩ W).Nonempty :=
    hM.2 _ _ ((hT _).inter (hT _)) ((hT' _).inter (hT' _))
      (hM.2 _ _ (hT _) (hT _) (hTne _) (hTne _)) (hM.2 _ _ (hT' _) (hT' _) (hTne' _) (hTne' _))
  let V : M.Y.left.Opens := ⟨M.spᶜ ∪ W, hcl.isOpen_compl.union hW⟩
  obtain ⟨N, i, hi, hj, hr⟩ := exists_restrict M V (by
    rintro _ ⟨a, rfl⟩; exact Or.inl (j_notMem_sp M a))
  have hsp : N.sp = i.left ⁻¹' M.sp := by
    ext x
    show N.Y.hom x = _ ↔ M.Y.hom (i.left x) = _
    rw [← Scheme.Hom.comp_apply, Over.w]
  have hinj := i.left.isOpenEmbedding.injective
  have hN : N.Irr := by
    obtain ⟨x, hx, hxW⟩ := hWne
    obtain ⟨x, rfl⟩ : x ∈ Set.range i.left := hr ▸ Or.inr hxW
    unfold Model.Irr
    rw [hsp]
    exact ⟨⟨x, hx⟩, hM.2.preimage i.left.isOpenEmbedding⟩
  have hLe : N.Le M := ⟨i, hi, hj⟩
  have key : ∀ b, ∀ x ∈ N.sp,
      (∃ z, (pr₁ N N).left z = x ∧ IsoAt (N.prod N) (N.prod N) (shear A b) z) ∧
      ∃ z, (pr₂ N N).left z = x ∧ IsoAt (N.prod N) (N.prod N) (shear A b) z := by
    intro b x hx
    rw [hsp] at hx
    have hxV : i.left x ∈ (V : Set M.Y.left) := hr ▸ ⟨x, rfl⟩
    have hxW : i.left x ∈ W := hxV.resolve_left (fun h => h hx)
    have h1 : i.left x ∈ T b := by cases b; exacts [hxW.1.2, hxW.1.1]
    have h2 : i.left x ∈ T' b := by cases b; exacts [hxW.2.2, hxW.2.1]
    obtain ⟨z, hz, hg⟩ := hTx b _ i.left.isOpenEmbedding.isOpen_range _ hx h1 ⟨x, rfl⟩
    obtain ⟨z', hz', hg'⟩ := hTx' b _ i.left.isOpenEmbedding.isOpen_range _ hx h2 ⟨x, rfl⟩
    obtain ⟨w, hw, -, hw2⟩ := good_isoAt i hj hg
    obtain ⟨w', -, hw', hw2'⟩ := good_isoAt i hj hg'
    exact ⟨⟨w, hinj (hw.trans hz), hw2⟩, w', hinj (hw'.trans hz'), hw2'⟩
  refine ⟨N, ⟨⟨hN, fun b => ?_, ?_⟩, key⟩, hLe⟩
  · obtain ⟨x, hx⟩ := hN.1
    obtain ⟨z, hz, hz'⟩ := (key b x hx).1
    refine ⟨z, ?_, hz'⟩
    show (N.prod N).Y.hom z = _
    rw [← Over.w (pr₁ N N), Scheme.Hom.comp_apply, hz]
    exact hx
  · have h1 := gLe A N M hN hLe
    have h2 := (gIso A A N M (Iso.refl A)).1 h1
    have h3 := gComp _ _ _ _ _ _ _ _ hM h1 (gComp _ _ _ _ _ _ _ _ hM hι h2)
    simpa using h3

end GlobalTheory.SS
end
