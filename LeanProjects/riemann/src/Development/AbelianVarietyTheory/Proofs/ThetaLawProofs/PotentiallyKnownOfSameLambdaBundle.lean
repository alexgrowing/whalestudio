import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.GeomIntSelf
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.AtOfNumberField
import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SqOfCalculus
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyPBRing
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.StalkOfAppLEEq
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.LbIsoDescendsToSubfieldContainingFinset
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsTwoTorsionTranslateSameLambdaBundleStatement
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaFrameValueKnownOfTwoTorsionTranslateStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

namespace GlobalTheory.KeyFam.SameLam
open GlobalTheory.ZM.SiegPull

section Prod

variable {S S' X Y : Scheme.{0}} {A : Over S} [GrpObj A]

def IsProd (A : Over S) [GrpObj A] (u v w : X ⟶ A.left) : Prop :=
  ∃ (s : X ⟶ S) (x y : Over.mk s ⟶ A), x.left = u ∧ y.left = v ∧ (x * y).left = w

theorem isProd_mul {T : Over S} (x y : T ⟶ A) : IsProd A x.left y.left (x * y).left :=
  ⟨T.hom, x, y, rfl, rfl, rfl⟩

theorem exists_isProd (u v : X ⟶ A.left) (h : u ≫ A.hom = v ≫ A.hom) : ∃ w, IsProd A u v w :=
  ⟨_, v ≫ A.hom, Over.homMk u h, Over.homMk v rfl, rfl, rfl, rfl⟩

theorem IsProd.unique {u v w u' v' w' : X ⟶ A.left} (h : IsProd A u v w) (h' : IsProd A u' v' w') (hu : u = u')
    (hv : v = v') : w = w' := by
  obtain ⟨s, x, y, rfl, rfl, rfl⟩ := h
  obtain ⟨s', x', y', rfl, rfl, rfl⟩ := h'
  exact mul_left_congr ((Over.w x).symm.trans ((congrArg (· ≫ A.hom) hu).trans (Over.w x'))) _ _ _ _ hu hv

theorem IsProd.comp {u v w : X ⟶ A.left} (h : IsProd A u v w) (g : Y ⟶ X) : IsProd A (g ≫ u) (g ≫ v) (g ≫ w) := by
  obtain ⟨s, x, y, rfl, rfl, rfl⟩ := h
  let g' : Over.mk (g ≫ s) ⟶ Over.mk s := Over.homMk g rfl
  exact ⟨g ≫ s, g' ≫ x, g' ≫ y, rfl, rfl, by rw [← MonObj.comp_mul]; rfl⟩

theorem IsProd.push {A' : Over S'} [GrpObj A'] {f : S' ⟶ S} {φ : A'.left ⟶ A.left} (hφ : IsGrpPullback A' A f φ)
    {u v w : X ⟶ A'.left} (h : IsProd A' u v w) : IsProd A (u ≫ φ) (v ≫ φ) (w ≫ φ) := by
  obtain ⟨s, x, y, rfl, rfl, rfl⟩ := h
  exact ⟨_, pushPt hφ.1.w x, pushPt hφ.1.w y, rfl, rfl, hφ.2 _ x y _ _ rfl rfl⟩

theorem isProd_transl {Q : Over S} (e : Q ⟶ A) (t : 𝟙_ (Over S) ⟶ A) :
    IsProd A (Q.hom ≫ t.left) e.left (e ≫ ((toUnit A ≫ t) * 𝟙 A)).left := by
  have h := isProd_mul (toUnit Q ≫ t) e
  have hu : (toUnit Q).left = Q.hom := (Category.comp_id _).symm.trans (Over.w (toUnit Q))
  rw [Over.comp_left, hu] at h
  rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc, comp_toUnit]
  exact h

theorem sq_eq_one_iff (t : 𝟙_ (Over S) ⟶ A) : t ^ 2 = 1 ↔ IsProd A t.left t.left (eSec A) := by
  have h1 : (1 : 𝟙_ (Over S) ⟶ A).left = eSec A := by
    rw [Hom.one_def, toUnit_unit, Category.id_comp]; rfl
  rw [pow_two]
  exact ⟨fun h => h1 ▸ h ▸ isProd_mul t t,
    fun h => Over.OverMorphism.ext (((isProd_mul t t).unique h rfl rfl).trans h1.symm)⟩

end Prod

theorem exists_finset_point {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {X : Scheme.{0}} (p : X ⟶ Sp K)
    [LocallyOfFiniteType p] (a : Sp Ω ⟶ X) (ha : a ≫ p = spMap (algebraMap K Ω)) :
    ∃ (s : Finset Ω) (b : Sp (IntermediateField.adjoin K (s : Set Ω)) ⟶ X),
      spMap (algebraMap (IntermediateField.adjoin K (s : Set Ω)) Ω) ≫ b = a := by
  classical
  obtain ⟨A, i, _, t, ht⟩ : ∃ (A : CommRingCat.{0}) (i : Spec A ⟶ X) (_ : IsOpenImmersion i)
      (t : Spec A), i t = a (IsLocalRing.closedPoint Ω) := by
    obtain ⟨n, t, ht⟩ := X.affineCover.exists_eq (a (IsLocalRing.closedPoint Ω))
    exact ⟨_, X.affineCover.f n, X.affineCover.map_prop n, t, ht⟩
  have hr : Set.range a ⊆ Set.range i := by
    rintro _ ⟨u, rfl⟩
    exact ⟨t, ht.trans (congrArg a (Subsingleton.elim _ _))⟩
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (IsOpenImmersion.lift i a hr)
  have hφa : Spec.map φ ≫ i = a := by rw [hφ, IsOpenImmersion.lift_fac]
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (i ≫ p)
  have h₂ : LocallyOfFiniteType (Spec.map ψ) := by rw [hψ]; infer_instance
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at h₂
  have hc : ψ ≫ φ = CommRingCat.ofHom (algebraMap K Ω) :=
    Spec.map_injective (by rw [Spec.map_comp, hψ, ← Category.assoc, hφa, ha])
  let : Algebra K A := ψ.hom.toAlgebra
  obtain ⟨s, hs⟩ : (⊤ : Subalgebra K A).FG := (show Algebra.FiniteType K A from h₂).out
  refine ⟨s.image φ.hom, ?_⟩
  set F := IntermediateField.adjoin K ((s.image φ.hom : Finset Ω) : Set Ω) with hF
  have hm : ∀ x : A, φ.hom x ∈ F := fun x => by
    have hx : x ∈ Algebra.adjoin K (s : Set A) := hs ▸ Algebra.mem_top
    induction hx using Algebra.adjoin_induction with
    | mem x hx => exact IntermediateField.subset_adjoin _ _ (by simpa using ⟨x, hx, rfl⟩)
    | algebraMap q =>
      rw [show φ.hom (algebraMap K A q) = algebraMap K Ω q from congrArg (fun z => z.hom q) hc]
      exact F.algebraMap_mem q
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  refine ⟨Spec.map (CommRingCat.ofHom (φ.hom.codRestrict F hm)) ≫ i, ?_⟩
  rw [← hφa, ← Spec.map_comp_assoc]
  rfl

theorem polPB_of_keyPB {R R' : Type} [CommRing R] [CommRing R'] {x' : KeyIn R'} {x : KeyIn R} {f : R →+* R'}
    (h : KeyPB x' x f) : ∃ φ, PolPB x'.P x.P (spMap f) φ ∧ eSec x'.P.A ≫ φ = spMap f ≫ eSec x.P.A := by
  obtain ⟨φ, he, w, hg, F, hp, hw, -⟩ := h
  exact ⟨φ, ⟨hp, hg, w, hw⟩, he⟩

theorem known_of_keyPB {K F : Type} [Field K] [Field F] {y : KeyIn K} {y' : KeyIn F} {j : K →+* F} (h : KeyPB y' y j)
    (hk : Known K y) : ∀ (e : F →+* ℂ) (x : KeyIn ℂ), KeyPB x y' e → Val x (e (j hk.choose)) :=
  fun e x hx => hk.choose_spec (e.comp j) x (keyPB_trans _ _ _ y y' x j e h hx)

theorem known_of_point (hL : Out.Laws) (hT : ThetaUnifAV) {K F : Type} [Field K] [Field F] (j : K →+* F) (y : KeyIn K)
    (y' : KeyIn F) (φ w : y'.P.A.left ⟶ y.P.A.left) (hφ : IsGrpPullback y'.P.A y.P.A (spMap j) φ)
    (p : Sp F ⟶ y.P.A.left) (hp : p ≫ y.P.A.hom = spMap j) (h₂ : IsProd y.P.A p p (spMap j ≫ eSec y.P.A))
    (hw : IsProd y.P.A (y'.P.A.hom ≫ p) φ w) (hi : LBIso y'.P.L (y.P.L.pull w)) (hk : Known K y) : Known F y' := by
  obtain ⟨z, hz⟩ := exists_keyPB_ring y j
  obtain ⟨χ, hχ, he⟩ := polPB_of_keyPB hz
  obtain ⟨e, hm, hφe⟩ := grpPullback_iso hφ hχ.1
  let t : 𝟙_ (Over (Sp F)) ⟶ z.P.A :=
    Over.homMk (hχ.1.1.lift p (𝟙 _) (hp.trans (Category.id_comp _).symm)) (hχ.1.1.lift_snd _ _ _)
  have ht : t.left ≫ χ = p := hχ.1.1.lift_fst _ _ _
  refine GlobalTheory.T.thetaFrameValueKnown_of_twoTorsion_translate hL hT F z y' e t hm ?_ ?_ ⟨_, known_of_keyPB hz hk⟩
  · have h1 : (1 : 𝟙_ (Over (Sp F)) ⟶ z.P.A).left = eSec z.P.A := by
      rw [Hom.one_def, toUnit_unit, Category.id_comp]; rfl
    rw [pow_two]
    refine Over.OverMorphism.ext (hχ.1.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))
    rw [h1, he]
    exact ((isProd_mul t t).push hχ.1).unique h₂ ht ht
  · have hw' := ((isProd_transl e.hom t).push hχ.1).unique hw (by rw [Category.assoc, ht]) hφe
    have k := lbIso_pull_comp hχ.2.2 (e.hom ≫ ((toUnit z.P.A ≫ t) * 𝟙 z.P.A)).left
    rw [hw'] at k
    exact LBIso.trans y'.P.isLB (pull_isLB y.P.isLB _) (pull_isLB z.P.isLB _) hi k.symm

theorem epi_spMap {k Ω : Type} [Field k] [Field Ω] (σ : k →+* Ω) : Epi (spMap σ) := by
  letI := σ.toAlgebra
  haveI : Flat (spMap σ) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.2 inferInstance
  haveI : Surjective (spMap σ) := ⟨fun p => ⟨IsLocalRing.closedPoint Ω, Subsingleton.elim _ _⟩⟩
  exact Flat.epi_of_flat_of_surjective _

theorem exists_polPB {R R' : Type} [CommRing R] [CommRing R'] (P : Out.PolAV (Sp R)) (f : R →+* R') :
    ∃ (P' : Out.PolAV (Sp R')) (φ : P'.A.left ⟶ P.A.left), PolPB P' P (spMap f) φ := by
  have h := isGrpPullback_pullback P.A (spMap f)
  let φ : ((Over.pullback (spMap f)).obj P.A).left ⟶ P.A.left := pullback.fst P.A.hom (spMap f)
  change IsGrpPullback _ _ _ φ at h
  have hL' := pull_isLB P.isLB φ
  have hw := (isGen_iff _).1 (idIso_isGen hL')
  exact ⟨{ A := (Over.pullback (spMap f)).obj P.A
           isAb := Out.TLinPf.isAb_pullback (spMap f) P.A P.isAb
           g := P.g
           smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h.1 P.smoothDim
           L := P.L.pull φ
           isLB := hL'
           rigid := PolBaseChange.rigidified_pull h P.rigid
           sym := PolBaseChange.sym_pull h P.sym
           ample := relAmple_pull h.1 P.isLB hL' hw ⊤ (isAffineOpen_top _) (fun _ => trivial) P.ample
           ktriv := kTriv_pull h P.isLB hL' hw P.ktriv }, φ, h, rfl, idIso _, idIso_isGen hL'⟩

theorem exists_point (hL : Out.Laws) {K Ω : Type} [Field K] [Field Ω] [IsAlgClosed Ω] (σ : K →+* Ω)
    (Q P : Out.PolAV (Sp K)) (e : P.A ≅ Q.A) [IsMonHom e.hom] (hl : LamIs P.A P.L Q.A (abelian₂ Q.A Q.L) e.hom.left) :
    ∃ (p : Sp Ω ⟶ Q.A.left) (X : Over (Sp Ω)) (ψ : X.left ⟶ P.A.left) (w : X.left ⟶ Q.A.left),
      p ≫ Q.A.hom = spMap σ ∧ IsProd Q.A p p (spMap σ ≫ eSec Q.A) ∧ IsPullback ψ X.hom P.A.hom (spMap σ) ∧
      IsProd Q.A (X.hom ≫ p) (ψ ≫ e.hom.left) w ∧ LBIso (P.L.pull ψ) (Q.L.pull w) := by
  obtain ⟨Q', χ, hχ⟩ := exists_polPB Q σ
  obtain ⟨P', ψ, hψ⟩ := exists_polPB P σ
  obtain ⟨e', hm, he'⟩ := grpPullback_iso
    ((hψ.1.comp (isGrpPullback_of_iso e)).congr (Category.comp_id _) rfl) hχ.1
  have lQ : (abelian₂ Q.A Q.L).IsLB := DVR.linComb_isLB _ Q.isLB _ _
  have hl' : LamIs P'.A P'.L Q'.A (abelian₂ Q'.A Q'.L) e'.hom.left := by
    obtain ⟨φ₂, s₂, i₂⟩ := hχ.lamIs
    obtain ⟨φ₂', s₂', i₂'⟩ := LamIs.comp P'.isLB P.isLB lQ hψ.lamIs hl
    refine ⟨_, isSquare_tensor e'.hom, ?_⟩
    have k₁ := lbIso_pull_comp i₂ (e'.hom ⊗ₘ e'.hom).left
    rw [isSquare_unique (isSquare_comp (isSquare_tensor e'.hom) s₂) s₂' he'] at k₁
    exact LBIso.trans (DVR.linComb_isLB _ P'.isLB _ _) (pull_isLB lQ _)
      (pull_isLB (DVR.linComb_isLB _ Q'.isLB _ _) _) i₂' k₁.symm
  obtain ⟨t, ht, hi⟩ := GlobalTheory.T.exists_twoTorsion_translate_same_lambdaBundle hL Ω Q' P' e' hm hl'
  refine ⟨t.left ≫ χ, P'.A, ψ, (e'.hom ≫ ((toUnit Q'.A ≫ t) * 𝟙 Q'.A)).left ≫ χ, ?_, ?_, hψ.1.1, ?_, ?_⟩
  · rw [Category.assoc, hχ.1.1.w, ← Category.assoc, Over.w t]
    exact Category.id_comp _
  · rw [← PolBaseChange.eSec_comm hχ.1]
    exact ((sq_eq_one_iff t).1 ht).push hχ.1
  · rw [← he', ← Category.assoc]
    exact (isProd_transl e'.hom t).push hχ.1
  · exact LBIso.trans (pull_isLB P.isLB _) P'.isLB (pull_isLB Q.isLB _) hψ.2.2.symm
      (LBIso.trans P'.isLB (pull_isLB Q'.isLB _) (pull_isLB Q.isLB _) hi (lbIso_pull_comp hχ.2.2 _))

theorem lbIso_pull_both {W Y X Z : Scheme.{0}} {L : LB X} {M : LB Z} {a : Y ⟶ X} {b : Y ⟶ Z} (j : W ⟶ Y)
    (hL : L.IsLB) (hM : M.IsLB) :
    LBIso ((L.pull a).pull j) ((M.pull b).pull j) ↔ LBIso (L.pull (j ≫ a)) (M.pull (j ≫ b)) := by
  have k₁ := lbIso_pull_comp (⟨idIso _, idIso_isGen (pull_isLB hL a)⟩ : LBIso (L.pull a) (L.pull a)) j
  have k₂ := lbIso_pull_comp (⟨idIso _, idIso_isGen (pull_isLB hM b)⟩ : LBIso (M.pull b) (M.pull b)) j
  have a₁ := pull_isLB (pull_isLB hL a) j
  have a₂ := pull_isLB (pull_isLB hM b) j
  have b₁ := pull_isLB hL (j ≫ a)
  have b₂ := pull_isLB hM (j ≫ b)
  exact ⟨fun h => LBIso.trans b₁ a₁ b₂ k₁.symm (LBIso.trans a₁ a₂ b₂ h k₂),
    fun h => LBIso.trans a₁ b₁ a₂ k₁ (LBIso.trans b₁ b₂ a₂ h k₂.symm)⟩

theorem potKnown_of_lamIs : Out.Laws → ThetaUnifAV → ∀ (K : Type) [Field K] [NumberField K] (y : KeyIn K) (P : Out.PolAV (Sp K)) (e : P.A ≅ y.P.A), IsMonHom e.hom → LamIs P.A P.L y.P.A (abelian₂ y.P.A y.P.L) e.hom.left → Known K y → PotKnown K P := by
  intro hL hT K _ _ y P e he hl hk
  let Ω := AlgebraicClosure K
  obtain ⟨p, X, ψ, w, hp, h₂, hψ, hw, hi⟩ := exists_point hL (algebraMap K Ω) y.P P e hl
  haveI := y.P.isAb.smooth
  haveI := P.isAb.proper
  obtain ⟨K₁, p₁, hp₁, _⟩ : ∃ (K₁ : IntermediateField K Ω) (p₁ : Sp K₁ ⟶ y.P.A.left),
      spMap (algebraMap K₁ Ω) ≫ p₁ = p ∧ FiniteDimensional K K₁ := by
    obtain ⟨s, p₁, hp₁⟩ := exists_finset_point y.P.A.hom p hp
    exact ⟨_, p₁, hp₁, IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x⟩
  haveI := epi_spMap (algebraMap K₁ Ω)
  have c₁ : spMap (algebraMap K Ω) = spMap (algebraMap K₁ Ω) ≫ spMap (algebraMap K K₁) :=
    spMap_comp (algebraMap K K₁) (algebraMap K₁ Ω)
  have q₁ : p₁ ≫ y.P.A.hom = spMap (algebraMap K K₁) := by
    rw [← cancel_epi (spMap (algebraMap K₁ Ω)), ← Category.assoc, hp₁, hp, c₁]
  have r₁ : IsProd y.P.A p₁ p₁ (spMap (algebraMap K K₁) ≫ eSec y.P.A) := by
    obtain ⟨u, hu⟩ := exists_isProd p₁ p₁ rfl
    rwa [(cancel_epi (spMap (algebraMap K₁ Ω))).1 (((hu.comp _).unique h₂ hp₁ hp₁).trans
      (by rw [c₁, Category.assoc]) : _ ≫ u = _ ≫ spMap (algebraMap K K₁) ≫ eSec y.P.A)] at hu
  let X₁ : Over (Sp K₁) := Over.mk (pullback.snd P.A.hom (spMap (algebraMap K K₁)))
  let ψ₁ : X₁.left ⟶ P.A.left := pullback.fst _ _
  have hψ₁ : IsPullback ψ₁ X₁.hom P.A.hom (spMap (algebraMap K K₁)) := IsPullback.of_hasPullback _ _
  obtain ⟨w₁, hw₁⟩ := exists_isProd (X₁.hom ≫ p₁) (ψ₁ ≫ e.hom.left)
    (by rw [Category.assoc, q₁, Category.assoc, Over.w e.hom, hψ₁.w])
  let π : X.left ⟶ X₁.left := hψ₁.lift ψ (X.hom ≫ spMap (algebraMap K₁ Ω)) (by rw [hψ.w, c₁, Category.assoc])
  have π₁ : π ≫ ψ₁ = ψ := hψ₁.lift_fst _ _ _
  have π₂ : π ≫ X₁.hom = X.hom ≫ spMap (algebraMap K₁ Ω) := hψ₁.lift_snd _ _ _
  have hπ : IsPullback π X.hom X₁.hom (spMap (algebraMap K₁ Ω)) :=
    IsPullback.of_right (by rw [π₁, ← c₁]; exact hψ) π₂ hψ₁
  have πw : π ≫ w₁ = w := (hw₁.comp π).unique hw (by rw [← Category.assoc, π₂, Category.assoc, hp₁])
    (by rw [← Category.assoc, π₁])
  haveI : IsProper X₁.hom := MorphismProperty.of_isPullback (P := @IsProper) hψ₁ inferInstance
  obtain ⟨s', hs'⟩ := lbIso_descends_to_subfield_containing_finset K₁ Ω (algebraMap K₁ Ω) X₁ X π (P.L.pull ψ₁)
    (y.P.L.pull w₁) hπ inferInstance inferInstance (pull_isLB P.isLB _) (pull_isLB y.P.isLB _)
    ((lbIso_pull_both π P.isLB y.P.isLB).2 (by rw [π₁, πw]; exact hi))
  let K₂ := IntermediateField.adjoin K₁ (s' : Set Ω)
  haveI : FiniteDimensional K₁ K₂ :=
    IntermediateField.finiteDimensional_adjoin fun x _ =>
      (Algebra.IsIntegral.isIntegral (R := K) x).tower_top
  haveI : NumberField K₁ := NumberField.of_module_finite K K₁
  haveI : NumberField K₂ := NumberField.of_module_finite K₁ K₂
  let X₂ : Over (Sp K₂) := Over.mk (pullback.snd X₁.hom (spMap (algebraMap K₁ K₂)))
  let χ : X₂.left ⟶ X₁.left := pullback.fst _ _
  have hχ : IsPullback χ X₂.hom X₁.hom (spMap (algebraMap K₁ K₂)) := IsPullback.of_hasPullback _ _
  have i₂ := (lbIso_pull_both χ P.isLB y.P.isLB).1 (hs' K₂ (algebraMap K₁ K₂) (algebraMap K₂ Ω) rfl
    (fun x hx => ⟨⟨x, IntermediateField.subset_adjoin _ _ hx⟩, rfl⟩) X₂ χ hχ)
  refine ⟨K₂, inferInstance, inferInstance, (algebraMap K₁ K₂).comp (algebraMap K K₁), fun F _ j y' φ hφ => ?_⟩
  have c₂ : spMap (j.comp ((algebraMap K₁ K₂).comp (algebraMap K K₁))) =
      (spMap j ≫ spMap (algebraMap K₁ K₂)) ≫ spMap (algebraMap K K₁) := by
    rw [spMap_comp, spMap_comp, Category.assoc]
  let a : y'.P.A.left ⟶ X₁.left := hψ₁.lift φ (y'.P.A.hom ≫ spMap j ≫ spMap (algebraMap K₁ K₂))
    (by rw [hφ.1.1.w, c₂]; simp only [Category.assoc])
  have a₁ : a ≫ ψ₁ = φ := hψ₁.lift_fst _ _ _
  have a₂ : a ≫ X₁.hom = y'.P.A.hom ≫ spMap j ≫ spMap (algebraMap K₁ K₂) := hψ₁.lift_snd _ _ _
  let b : y'.P.A.left ⟶ X₂.left := hχ.lift a (y'.P.A.hom ≫ spMap j) (by rw [a₂, Category.assoc])
  have b₁ : b ≫ χ = a := hχ.lift_fst _ _ _
  have i₃ := (lbIso_pull_both b P.isLB y.P.isLB).1
    (LBIso.chartPull (chartPullPull _ b b rfl) (chartPullPull _ b b rfl) i₂)
  rw [← Category.assoc, ← Category.assoc, b₁, a₁] at i₃
  refine known_of_point hL hT _ y y' (φ ≫ e.hom.left) (a ≫ w₁)
    ((hφ.1.comp (isGrpPullback_of_iso e)).congr (Category.comp_id _) rfl)
    ((spMap j ≫ spMap (algebraMap K₁ K₂)) ≫ p₁) (by rw [Category.assoc, q₁, c₂]) ?_ ?_
    (LBIso.trans y'.P.isLB (pull_isLB P.isLB _) (pull_isLB y.P.isLB _) hφ.2.2 i₃) hk
  · rw [c₂, Category.assoc _ (spMap (algebraMap K K₁))]
    exact r₁.comp _
  · rw [← Category.assoc, ← a₂, ← a₁, Category.assoc, Category.assoc]
    exact hw₁.comp a

end GlobalTheory.KeyFam.SameLam
