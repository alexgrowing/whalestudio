import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnionTranslatesStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniqueModelExtensionOfDefinedAtPoints
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TranslationBySection
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModelMapGenericallyOpenImmersionCalculus
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GrpObjOfDenseOpen
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompletionPointClosedPointMemOfSmooth
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenImmersionSpMapOfIsDiscreteValuationRing
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.GeometricallyIntegralOfIsIntegralOfIsAlgClosed
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GlobalTheory.SS.StrictGrp

section Basic
variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K] {A A' A'' : Over (Sp K)}

theorem isPullback_j (M : Model R A) : IsPullback M.j A.hom M.Y.hom (spMap (algebraMap R K)) := by
  have : IsIso M.e.inv.left := inferInstanceAs (IsIso ((Over.forget _).map M.e.inv))
  have h : IsPullback M.e.inv.left A.hom (pullback.snd M.Y.hom (spMap (algebraMap R K))) (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨(Over.w M.e.inv).trans (Category.comp_id _).symm⟩
  simpa [Model.j] using h.paste_horiz (IsPullback.of_hasPullback M.Y.hom (spMap (algebraMap R K)))

theorem j_comm (M : Model R A) (N : Model R A') (f : A ⟶ A') (g : M.Y ⟶ N.Y)
    (h : M.e.inv ≫ (Over.pullback (spMap (algebraMap R K))).map g = f ≫ N.e.inv) : M.j ≫ g.left = f.left ≫ N.j := by
  have h2 := congrArg (fun q => q.left ≫ pullback.fst N.Y.hom (spMap (algebraMap R K))) h
  have h4 : ((Over.pullback (spMap (algebraMap R K))).map g).left ≫ pullback.fst N.Y.hom (spMap (algebraMap R K))
      = pullback.fst M.Y.hom (spMap (algebraMap R K)) ≫ g.left := pullback.lift_fst _ _ _
  simp only [Over.comp_left, Category.assoc] at h2
  unfold Model.j
  rw [Category.assoc]
  exact (congrArg (fun q => M.e.inv.left ≫ q) h4).symm.trans h2

theorem prod_j_fst (M : Model R A) (N : Model R A') :
    (M.prod N).j ≫ (fst M.Y N.Y).left = (fst A A').left ≫ M.j :=
  j_comm (M.prod N) M (fst A A') (fst M.Y N.Y) (by simp [Model.prod])

theorem prod_j_snd (M : Model R A) (N : Model R A') :
    (M.prod N).j ≫ (snd M.Y N.Y).left = (snd A A').left ≫ N.j :=
  j_comm (M.prod N) N (snd A A') (snd M.Y N.Y) (by simp [Model.prod])

theorem twist_j (M : Model R A) (f : A ≅ A') : (M.twist f).j = f.inv.left ≫ M.j := by
  simp [Model.twist, Model.j]

theorem twist_comm {M : Model R A} {N : Model R A'} {f : A ≅ A'} {g : M.Y.left ⟶ N.Y.left}
    (h : (M.twist f).j ≫ g = N.j) : M.j ≫ g = f.hom.left ≫ N.j := by
  rw [← h, twist_j, Category.assoc, ← Category.assoc f.hom.left, ← Over.comp_left, f.hom_inv_id, Over.id_left,
    Category.id_comp]

theorem prod_comm {B B' : Over (Sp K)} {M : Model R A} {N : Model R A'} {P : Model R B} {Q : Model R B'}
    {f : A ⟶ B} {f' : A' ⟶ B'} {g : M.Y ⟶ P.Y} {g' : N.Y ⟶ Q.Y} (h : M.j ≫ g.left = f.left ≫ P.j)
    (h' : N.j ≫ g'.left = f'.left ≫ Q.j) :
    (M.prod N).j ≫ (g ⊗ₘ g').left = (f ⊗ₘ f').left ≫ (P.prod Q).j := by
  apply Over.tensorObj_ext
  · change (_ ≫ _) ≫ (fst P.Y Q.Y).left = (_ ≫ _) ≫ (fst P.Y Q.Y).left
    rw [Category.assoc, Category.assoc, prod_j_fst, ← Over.comp_left, tensorHom_fst, Over.comp_left,
      ← Category.assoc, prod_j_fst, Category.assoc, h, ← Category.assoc, ← Category.assoc, ← Over.comp_left,
      ← Over.comp_left, tensorHom_fst]
  · change (_ ≫ _) ≫ (snd P.Y Q.Y).left = (_ ≫ _) ≫ (snd P.Y Q.Y).left
    rw [Category.assoc, Category.assoc, prod_j_snd, ← Over.comp_left, tensorHom_snd, Over.comp_left,
      ← Category.assoc, prod_j_snd, Category.assoc, h', ← Category.assoc, ← Category.assoc, ← Over.comp_left,
      ← Over.comp_left, tensorHom_snd]

theorem defAt_of_chart {G : Model R A} {N : Model R A'} {φ : A ⟶ A'} {W V : Scheme.{0}} (w : W ⟶ G.Y.left)
    [IsOpenImmersion w] {v : V ⟶ W} {u : V ⟶ A.left} (hp : IsPullback v u w G.j) (h : W ⟶ N.Y.left)
    (h₁ : h ≫ N.Y.hom = w ≫ G.Y.hom) (h₂ : v ≫ h = u ≫ φ.left ≫ N.j) {y : G.Y.left} (hy : y ∈ Set.range w) :
    DefAt G N φ y := by
  refine ⟨w.opensRange, w.isoOpensRange.inv ≫ h, hy, ?_, ?_⟩
  · rw [Category.assoc, h₁, ← Category.assoc, Scheme.Hom.isoOpensRange_inv_comp]
  · have e : (G.j ∣_ w.opensRange ≫ w.isoOpensRange.inv) ≫ w = (G.j ⁻¹ᵁ w.opensRange).ι ≫ G.j := by
      rw [Category.assoc, Scheme.Hom.isoOpensRange_inv_comp, morphismRestrict_ι]
    rw [← Category.assoc, ← hp.lift_fst _ _ e, Category.assoc, h₂, ← Category.assoc, hp.lift_snd]

theorem isPullback_of_comm {M : Model R A} {G : Model R A'} {f : A ≅ A'} {g : M.Y ⟶ G.Y}
    (h : M.j ≫ g.left = f.hom.left ≫ G.j) : IsPullback M.j f.hom.left g.left G.j := by
  have h₁ := isPullback_j M
  rw [← Over.w f.hom, ← Over.w g] at h₁
  exact IsPullback.of_bot h₁ h (isPullback_j G)

theorem defAt_transport {M : Model R A} {G : Model R A'} {N N' : Model R A''} {f : A ≅ A'} {g : M.Y ⟶ G.Y}
    [IsOpenImmersion g.left] (h : M.j ≫ g.left = f.hom.left ≫ G.j) {ψ : A ⟶ A''} {φ : A' ⟶ A''} {t : A'' ⟶ A''}
    {T : N.Y ⟶ N'.Y} (hT : N.j ≫ T.left = t.left ≫ N'.j) (e : ψ ≫ t = f.hom ≫ φ) {x : M.Y.left}
    (hx : DefAt M N ψ x) : DefAt G N' φ (g.left x) := by
  obtain ⟨U, k, hU, h₁, h₂⟩ := hx
  refine defAt_of_chart (U.ι ≫ g.left) (v := M.j ∣_ U) (u := (M.j ⁻¹ᵁ U).ι ≫ f.hom.left)
    ((isPullback_morphismRestrict M.j U).paste_vert (isPullback_of_comm h)) (k ≫ T.left) ?_ ?_ ⟨⟨x, hU⟩, rfl⟩
  · rw [Category.assoc, Over.w T, h₁, Category.assoc, Over.w g]
  · rw [← Category.assoc, h₂, Category.assoc, Category.assoc, hT, ← Category.assoc ψ.left, ← Over.comp_left, e]
    simp

theorem isOpen_defAt (M : Model R A) (N : Model R A') (f : A ⟶ A') : IsOpen {x | DefAt M N f x} := by
  rw [isOpen_iff_forall_mem_open]
  rintro x ⟨U, g, hx, h⟩
  exact ⟨U, fun y hy => ⟨U, g, hy, h⟩, U.isOpen, hx⟩

variable [IsDomain R]

theorem mem_range_generic [IsDiscreteValuationRing R] [IsFractionRing R K] (p : Sp R)
    (hp : p ≠ IsLocalRing.closedPoint R) : p ∈ Set.range (spMap (algebraMap R K)) := by
  refine ⟨(⊥ : PrimeSpectrum K), PrimeSpectrum.ext ?_⟩
  have h : p.asIdeal = ⊥ := by
    by_contra h
    exact hp (PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal (p.isPrime.isMaximal h)))
  rw [h]
  exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective R K)

theorem defAt_generic [IsDiscreteValuationRing R] [IsFractionRing R K] (M : Model R A) (N : Model R A') (f : A ⟶ A')
    {x : M.Y.left} (hx : x ∉ M.sp) : DefAt M N f x := by
  have := isOpenImmersion_spMap_of_isDiscreteValuationRing R K
  have : IsOpenImmersion M.j := MorphismProperty.of_isPullback (isPullback_j M).flip this
  refine defAt_of_chart M.j (v := 𝟙 _) (u := 𝟙 _) (IsKernelPair.id_of_mono _) (f.left ≫ N.j) ?_ (by simp) ?_
  · rw [Category.assoc, N.j_hom, M.j_hom, ← Category.assoc, Over.w f]
  · obtain ⟨q, hq⟩ := mem_range_generic (K := K) (M.Y.hom x) hx
    obtain ⟨z, hz, -⟩ := Scheme.exists_preimage_of_isPullback (isPullback_j M) x q hq.symm
    exact ⟨z, hz⟩

theorem ext_section [IsFractionRing R K] {Y : Over (Sp R)} [IsSeparated Y.hom] {f g : 𝟙_ (Over (Sp R)) ⟶ Y}
    (h : spMap (algebraMap R K) ≫ f.left = spMap (algebraMap R K) ≫ g.left) : f = g := by
  obtain ⟨_, _⟩ := ExtUnique.spec_fractionRing R K
  exact Over.OverMorphism.ext (ExtUnique.hom_ext_of_dominant Y.hom (by rw [Over.w, Over.w]) _ h)

end Basic

section Transl
variable {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] [IsCommMonObj A]

theorem comp_transl {T : Over (Sp K)} (x : T ⟶ A) (a : 𝟙_ (Over (Sp K)) ⟶ A) :
    x ≫ (transl a).hom = (toUnit T ≫ a) * x := by
  simp [transl, MonObj.comp_mul, ← Category.assoc, toUnit_unique (x ≫ toUnit A) (toUnit T)]

theorem transl_hom (a : 𝟙_ (Over (Sp K)) ⟶ A) : (transl a).hom = (toUnit A ≫ a) * 𝟙 A := rfl

theorem transl_mul (a b : 𝟙_ (Over (Sp K)) ⟶ A) : (transl a).hom ≫ (transl b).hom = (transl (a * b)).hom := by
  rw [comp_transl, transl_hom, transl_hom, MonObj.comp_mul, ← _root_.mul_assoc, _root_.mul_comm (toUnit A ≫ b)]

theorem transl_one : (transl (1 : 𝟙_ (Over (Sp K)) ⟶ A)).hom = 𝟙 A := by
  rw [transl_hom, MonObj.comp_one, _root_.one_mul]

theorem transl_inv (a : 𝟙_ (Over (Sp K)) ⟶ A) : (transl a).inv = (transl a⁻¹).hom := by
  rw [transl_hom, GrpObj.comp_inv]; rfl

theorem pt_transl (a b : 𝟙_ (Over (Sp K)) ⟶ A) : a ≫ (transl b).hom = b * a := by
  rw [comp_transl, toUnit_unit, Category.id_comp]

theorem mul_transl (a b : 𝟙_ (Over (Sp K)) ⟶ A) :
    μ[A] ≫ (transl (a * b)).hom = (tensorIso (transl a) (transl b)).hom ≫ μ[A] := by
  have h : (tensorIso (transl a) (transl b)).hom = lift (fst A A ≫ (transl a).hom) (snd A A ≫ (transl b).hom) := by
    ext <;> simp
  have h' : μ[A] = fst A A * snd A A := by rw [Hom.mul_def, lift_fst_snd, Category.id_comp]
  rw [h, ← Hom.mul_def, comp_transl, comp_transl, comp_transl, h', MonObj.comp_mul, _root_.mul_mul_mul_comm]

theorem inv_transl (a : 𝟙_ (Over (Sp K)) ⟶ A) : ι[A] ≫ (transl a⁻¹).hom = (transl a).hom ≫ ι[A] := by
  have h' : ι[A] = (𝟙 A)⁻¹ := by rw [Hom.inv_def, Category.id_comp]
  rw [← Hom.inv_def, comp_transl, transl_hom, h', GrpObj.comp_inv, mul_inv]

end Transl

section Special
variable {R K : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K] {A : Over (Sp K)}

theorem exists_section (h : SH R K) (M : Model R A) {S : Set M.Y.left} (hS : IsLocallyClosed S)
    (hne : (S ∩ M.sp).Nonempty) : ∃ s : 𝟙_ (Over (Sp R)) ⟶ M.Y, s.left (IsLocalRing.closedPoint R) ∈ S := by
  obtain ⟨-, hH, hk, -⟩ := h
  have := M.smooth
  let r := Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
  obtain ⟨x, hxS, hx⟩ := hne
  obtain ⟨z, rfl⟩ := (range_fst_residue M.Y.hom).ge hx
  have := LocallyOfFiniteType.jacobsonSpace (pullback.snd M.Y.hom r)
  obtain ⟨c, hcS, hc⟩ := nonempty_inter_closedPoints (Z := pullback.fst M.Y.hom r ⁻¹' S) ⟨z, hxS⟩
    (hS.preimage (pullback.fst M.Y.hom r).continuous)
  obtain ⟨⟨s, hs⟩, e⟩ := reducePoint_residue_surjective M.Y.hom R (𝟙 _)
    ⟨pointOfClosedPoint (pullback.snd M.Y.hom r) c hc ≫ pullback.fst M.Y.hom r, by
      rw [Category.assoc, pullback.condition, pointOfClosedPoint_comp_assoc, Category.comp_id]⟩
  refine ⟨Over.homMk s hs, ?_⟩
  have e₁ : r ≫ s = pointOfClosedPoint (pullback.snd M.Y.hom r) c hc ≫ pullback.fst M.Y.hom r := congrArg Subtype.val e
  have e₂ : s (r (IsLocalRing.closedPoint _)) = pullback.fst M.Y.hom r c := by
    rw [← Scheme.Hom.comp_apply, e₁, Scheme.Hom.comp_apply, pointOfClosedPoint_apply]
  have e₃ : r (IsLocalRing.closedPoint _) = IsLocalRing.closedPoint R := IsLocalRing.comap_closedPoint (IsLocalRing.residue R)
  rw [e₃] at e₂
  change s _ ∈ S
  rw [e₂]; exact hcS

theorem connectedSpace_of_factor {X S S' P Z : Scheme.{0}} {f : X ⟶ S} {i : S' ⟶ S} {p : P ⟶ X} {q : P ⟶ S'}
    (hP : IsPullback p q f i) [hq : GeometricallyConnected q] {L : Type} [Field L] (y : Sp L ⟶ S') {a : Z ⟶ X}
    {b : Z ⟶ Sp L} (hZ : IsPullback a b f (y ≫ i)) : ConnectedSpace Z :=
  hq.geometrically_connectedSpace y _ _
    (IsPullback.of_right (by rw [hP.lift_fst]; exact hZ) (hP.lift_snd _ _ (by simpa using hZ.w)) hP)

theorem geometricallyConnected (h : SH R K) (M : Model R A) (hM : M.Irr) [GeometricallyConnected A.hom] :
    GeometricallyConnected M.Y.hom := by
  obtain ⟨hD, -, hk, hF⟩ := h
  have := M.smooth
  refine ⟨fun L _ y Z a b hZ => ?_⟩
  by_cases hy : y (IsLocalRing.closedPoint L) = IsLocalRing.closedPoint R
  · let r := Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
    have hr : IsClosedImmersion r := .spec_of_surjective _ IsLocalRing.residue_surjective
    have : IrreducibleSpace ↥(pullback M.Y.hom r) := by
      have he := (pullback.fst M.Y.hom r).isClosedEmbedding.isEmbedding
      have h₁ : IsIrreducible (Set.range (pullback.fst M.Y.hom r)) := by
        rw [range_fst_residue]; exact hM
      have := Subtype.irreducibleSpace h₁
      exact he.toHomeomorph.irreducibleSpace_iff.2 this
    have h₂ := geometricallyIrreducible_of_isAlgClosed (pullback.snd M.Y.hom r)
    have : GeometricallyConnected (pullback.snd M.Y.hom r) := ⟨fun L _ y Z a b hZ => by
      have : IrreducibleSpace Z := h₂.geometrically_irreducibleSpace y a b hZ
      infer_instance⟩
    obtain ⟨φ, rfl⟩ := Spec.map_surjective y
    have hl : IsLocalHom φ.hom := (IsLocalRing.isLocalHom_iff_comap_closedPoint _).2 hy
    have e : Spec.map φ = spMap (IsLocalRing.ResidueField.lift φ.hom) ≫ r := by
      rw [← Spec.map_comp]; congr 1
    rw [e] at hZ
    exact connectedSpace_of_factor (IsPullback.of_hasPullback _ _) _ hZ
  · have := isOpenImmersion_spMap_of_isDiscreteValuationRing R K
    have hr : Set.range y ⊆ Set.range (spMap (algebraMap R K)) := by
      rintro _ ⟨q, rfl⟩
      rw [Subsingleton.elim q (IsLocalRing.closedPoint L)]
      exact mem_range_generic _ hy
    rw [← IsOpenImmersion.lift_fac _ _ hr] at hZ
    exact connectedSpace_of_factor (isPullback_j M) _ hZ

end Special

theorem isOpenImmersion_tensor {S : Scheme.{0}} {X Y X' Y' : Over S} (f : X ⟶ X') (g : Y ⟶ Y')
    [IsOpenImmersion f.left] [IsOpenImmersion g.left] : IsOpenImmersion (f ⊗ₘ g).left := by
  rw [Over.tensorHom_left]; infer_instance

theorem mem_range_tensor {S : Scheme.{0}} {X Y X' Y' : Over S} (f : X ⟶ X') (g : Y ⟶ Y') (z : (X' ⊗ Y').left)
    (h₁ : (fst X' Y').left z ∈ Set.range f.left) (h₂ : (snd X' Y').left z ∈ Set.range g.left) :
    z ∈ Set.range (f ⊗ₘ g).left := by
  rw [Over.tensorHom_left]
  exact (Scheme.Pullback.range_map _ _ _ _ _ _ _ _ _).ge ⟨h₁, h₂⟩

end GlobalTheory.SS.StrictGrp

open GlobalTheory.SS.StrictGrp in

theorem GlobalTheory.SS.exists_grpObj_of_strict : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K], SH R K → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ M : Model R A, Strict M → ∃ (G : Model R A) (_ : GrpObj G.Y), SmConn G.Y ∧ IsMonHom G.e.hom ∧ ∀ a : (𝟙_ (Over (Sp K)) ⟶ A), GenIso M M (transl a).hom → ∃ s : 𝟙_ (Over (Sp R)) ⟶ G.Y, spMap (algebraMap R K) ≫ s.left = a.left ≫ G.j := by
  intro R K _ _ _ _ _ hSH A _ _ hA M hM
  obtain ⟨G, hGI, hLe, hcov, hmu⟩ := GlobalTheory.T.exists_union_translates' R K hSH A hA M hM
  have hD := hSH.1
  have hF := hSH.2.2.2
  have hMI : M.Irr := hM.1.1
  have hGs := G.smooth
  have hGp := G.sep
  have hext := GlobalTheory.SS.existsUnique_extension_of_forall_defAt R K
  have hsec := GlobalTheory.SS.SectionTranslation.translation_by_section R K hSH A hA M hM
  obtain ⟨-, hcomp, hinv, -⟩ := GlobalTheory.SS.GI.genIso_calculus R K hSH
  let H : (𝟙_ (Over (Sp K)) ⟶ A) → Prop := fun a => GenIso M M (transl a).hom
  have H1 : H 1 := by
    obtain ⟨y, hy⟩ := hMI.nonempty
    exact ⟨y, hy, transl_one (A := A) ▸ isoAt_id M y⟩
  have Hmul : ∀ a b, H a → H b → H (a * b) := fun a b ha hb => by
    have := hcomp _ _ _ M M M _ _ hMI ha hb
    rwa [transl_mul] at this
  have Hinv : ∀ a, H a → H a⁻¹ := fun a ha => by
    have := (hinv _ _ M M (transl a)).1 ha
    rwa [transl_inv] at this
  have hg : ∀ a, H a → ∃ g : M.Y ⟶ G.Y, IsOpenImmersion g.left ∧ M.j ≫ g.left = (transl a).hom.left ≫ G.j :=
    fun a ha => by
      obtain ⟨g, h₁, h₂⟩ := hLe a ha
      exact ⟨g, h₁, twist_comm h₂⟩
  have hc : ∀ y : G.Y.left, ∃ (a : 𝟙_ (Over (Sp K)) ⟶ A) (g : M.Y ⟶ G.Y) (x : M.Y.left), H a ∧
      IsOpenImmersion g.left ∧ M.j ≫ g.left = (transl a).hom.left ≫ G.j ∧ g.left x = y := fun y => by
    obtain ⟨a, g, ha, h₁, h₂, x, hx⟩ := hcov y
    exact ⟨a, g, x, ha, h₁, twist_comm h₂, hx⟩

  have hT : ∀ c, H c → ∃ T : G.Y ⟶ G.Y, G.j ≫ T.left = (transl c).hom.left ≫ G.j := fun c hc' => by
    refine (hext _ _ G G _ fun y => ?_).exists
    obtain ⟨a, g, x, ha, _, h, rfl⟩ := hc y
    obtain ⟨g', -, h'⟩ := hg _ (Hmul a c ha hc')
    exact defAt_transport h h' (by rw [Category.id_comp, transl_mul]) (isoAt_id M x).defAt

  obtain ⟨m, hm⟩ : ∃ m : (G.prod G).Y ⟶ G.Y, (G.prod G).j ≫ m.left = (μ[A]).left ≫ G.j := by
    refine (hext _ _ (G.prod G) G _ fun z => ?_).exists
    obtain ⟨a, g, x, ha, _, h, hx⟩ := hc ((fst G.Y G.Y).left z)
    obtain ⟨b, g', x', hb, _, h', hx'⟩ := hc ((snd G.Y G.Y).left z)
    obtain ⟨w, rfl⟩ := mem_range_tensor g g' z ⟨x, hx⟩ ⟨x', hx'⟩
    obtain ⟨T, hT⟩ := hT _ (Hmul a b ha hb)
    have := isOpenImmersion_tensor g g'
    exact defAt_transport (M := M.prod M) (G := G.prod G) (f := tensorIso (transl a) (transl b)) (g := g ⊗ₘ g')
      (prod_comm h h') hT (mul_transl a b) (hmu w)

  have hmove : ∀ (s : 𝟙_ (Over (Sp R)) ⟶ M.Y) (c a : 𝟙_ (Over (Sp K)) ⟶ A) (g : M.Y ⟶ G.Y),
      c.left ≫ M.j = spMap (algebraMap R K) ≫ s.left → M.j ≫ g.left = (transl a).hom.left ≫ G.j →
      spMap (algebraMap R K) ≫ (s ≫ g).left = (a * c).left ≫ G.j := fun s c a g h₁ h₂ => by
    rw [Over.comp_left, ← Category.assoc, ← h₁, Category.assoc, h₂, ← Category.assoc, ← Over.comp_left, pt_transl]
  have hsecG : ∀ a, H a → ∃ s : 𝟙_ (Over (Sp R)) ⟶ G.Y, spMap (algebraMap R K) ≫ s.left = a.left ≫ G.j :=
    fun a ha => by
      obtain ⟨s, -⟩ := exists_section hSH M isOpen_univ.isLocallyClosed (by simpa using hMI.nonempty)
      obtain ⟨c, h₁, h₂, -⟩ := hsec s
      obtain ⟨g, -, h₃⟩ := hg _ (Hmul _ _ ha (Hinv _ h₂))
      exact ⟨s ≫ g, by rw [hmove s c _ g h₁ h₃, inv_mul_cancel_right]⟩

  obtain ⟨i, hi⟩ : ∃ i : G.Y ⟶ G.Y, G.j ≫ i.left = (ι[A]).left ≫ G.j := by
    refine (hext _ _ G G _ fun y => ?_).exists
    by_contra hy
    have hys : y ∈ G.sp := by_contra fun h => hy (defAt_generic G G _ h)
    obtain ⟨a, g, x, ha, _, h, rfl⟩ := hc y
    have hxs : x ∈ M.sp := by
      have e : G.Y.hom (g.left x) = M.Y.hom x := by rw [← Scheme.Hom.comp_apply, Over.w g]
      exact e.symm.trans hys
    obtain ⟨s, hs⟩ := exists_section hSH M (S := g.left ⁻¹' {y | DefAt G G (ι[A]) y}ᶜ)
      ((isOpen_defAt G G _).isClosed_compl.preimage g.left.continuous).isLocallyClosed ⟨x, hy, hxs⟩
    obtain ⟨x', hx', hx''⟩ := hM.1.2.2
    obtain ⟨u, hu⟩ := exists_section hSH M (isOpen_defAt M M (ι[A])).isLocallyClosed ⟨x', hx''.defAt, hx'⟩
    obtain ⟨c, hc₁, hc₂, -⟩ := hsec s
    obtain ⟨d, hd₁, hd₂, -⟩ := hsec u
    have He := Hmul _ _ (Hmul _ _ ha hc₂) (Hinv _ hd₂)
    obtain ⟨g₁, _, h₁⟩ := hg _ He
    obtain ⟨g₂, -, h₂⟩ := hg _ (Hinv _ He)
    have e : u ≫ g₁ = s ≫ g := ext_section (K := K) (by
      rw [hmove u d _ g₁ hd₁ h₁, hmove s c _ g hc₁ h, inv_mul_cancel_right])
    have e' : g₁.left (u.left (IsLocalRing.closedPoint R)) = g.left (s.left (IsLocalRing.closedPoint R)) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Over.comp_left, ← Over.comp_left, e]
    exact hs (e' ▸ defAt_transport h₁ h₂ (inv_transl _) hu)
  obtain ⟨e, he⟩ := hsecG 1 H1
  have := GlobalTheory.isOpenImmersion_spMap_of_isDiscreteValuationRing R K
  obtain ⟨inst, -, -, -, hcomm, hpb⟩ := GlobalTheory.grpObj_of_dense_open (Sp R) (Sp K) (spMap (algebraMap R K)) G.Y A G.j
    (isPullback_j G) m i e (fun φ₂ h => by
      obtain rfl : φ₂ = (G.prod G).j := by
        apply Over.tensorObj_ext
        · exact h.1.trans (prod_j_fst G G).symm
        · exact h.2.trans (prod_j_snd G G).symm
      exact hm) hi (by simpa [Hom.one_def] using he)
  have := hA.geomConnected
  refine ⟨G, inst, ⟨hcomm, hGs, hGp, G.qc, geometricallyConnected hSH G hGI⟩, ?_, hsecG⟩
  obtain ⟨e', h₁, h₂⟩ := grpPullback_iso (isGrpPullback_pullback G.Y (spMap (algebraMap R K))) hpb
  have e₀ : G.e.hom = e'.hom := by
    apply Over.OverMorphism.ext
    apply (isPullback_j G).hom_ext
    · rw [h₂, Model.j, ← Category.assoc, ← Over.comp_left, G.e.hom_inv_id, Over.id_left, Category.id_comp]
    · rw [Over.w, Over.w]
  rw [e₀]
  exact h₁
end
