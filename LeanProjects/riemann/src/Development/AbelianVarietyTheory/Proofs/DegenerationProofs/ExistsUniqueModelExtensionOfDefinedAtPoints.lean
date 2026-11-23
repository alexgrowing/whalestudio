import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLiftOfSchemeTheoreticallyDominant

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS

section
variable {R K : Type} [CommRing R] [Field K] [Algebra R K] {A A' : Over (Sp K)}

theorem Model.isPullback_j (M : Model R A) :
    IsPullback M.j A.hom M.Y.hom (spMap (algebraMap R K)) := by
  refine IsPullback.of_iso (IsPullback.of_hasPullback M.Y.hom (spMap (algebraMap R K)))
    ((Over.forget _).mapIso M.e) (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ (by simp) (by simp)
  · have : M.e.hom.left ≫ M.e.inv.left = 𝟙 _ := by rw [← Over.comp_left, M.e.hom_inv_id]; rfl
    simp [Model.j, reassoc_of% this]
  · have := Over.w M.e.hom
    simpa using this.symm

theorem Model.quasiCompact_j (M : Model R A) : QuasiCompact M.j :=
  MorphismProperty.of_isPullback M.isPullback_j.flip inferInstance

variable [IsDomain R] [IsFractionRing R K]

theorem Model.mono_j (M : Model R A) : Mono M.j := by
  have : IsPreimmersion (spMap (algebraMap R K)) :=
    IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  have : IsPreimmersion M.j := MorphismProperty.of_isPullback M.isPullback_j.flip this
  infer_instance

theorem Model.dominant_j (M : Model R A) : IsSchemeTheoreticallyDominant M.j := by
  have := schemeTheoreticallyDominant_fractionField R K
  have := M.smooth
  exact IsSchemeTheoreticallyDominant.of_isPullback M.isPullback_j.flip

theorem Model.hom_ext_of_flat (M : Model R A) {P X : Scheme.{0}} (p : P ⟶ M.Y.left) [Flat p]
    (s : X ⟶ Sp R) [IsSeparated s] {a b : P ⟶ X} (hab : a ≫ s = b ≫ s)
    (h : pullback.fst p M.j ≫ a = pullback.fst p M.j ≫ b) : a = b := by
  have := M.dominant_j
  have := M.quasiCompact_j
  have : IsSchemeTheoreticallyDominant (pullback.fst p M.j) :=
    IsSchemeTheoreticallyDominant.of_isPullback (IsPullback.of_hasPullback p M.j).flip
  have : IsSeparated (Over.mk s).hom := ‹_›
  have := over_ext_of_schemeTheoreticallyDominant (Y := Over.mk (a ≫ s)) (X := Over.mk s)
    (pullback.fst p M.j) (a := Over.homMk a rfl) (b := Over.homMk b hab.symm) h
  exact congr(($this).left)

omit [IsDomain R] [IsFractionRing R K] in

theorem Extends.comp_eq {M : Model R A} {N : Model R A'} {f : A ⟶ A'} {U : M.Y.left.Opens}
    {g : U.toScheme ⟶ N.Y.left} (h : Extends M N f U g) {W : Scheme.{0}} (u : W ⟶ U.toScheme)
    (v : W ⟶ A.left) (e : u ≫ U.ι = v ≫ M.j) : u ≫ g = v ≫ f.left ≫ N.j := by
  have P := isPullback_morphismRestrict M.j U
  rw [← P.lift_fst u v e, Category.assoc, h.2, P.lift_snd_assoc]

theorem exists_glue (M : Model R A) (N : Model R A') (f : A ⟶ A') (U : M.Y.left → M.Y.left.Opens)
    (g : ∀ y, (U y).toScheme ⟶ N.Y.left) (hU : ∀ y, y ∈ U y) (hg : ∀ y, Extends M N f (U y) (g y)) :
    ∃ G : M.Y ⟶ N.Y, M.j ≫ G.left = f.left ≫ N.j ∧ ∀ y, (U y).ι ≫ G.left = g y := by
  have := N.sep
  have hc : TopologicalSpace.IsOpenCover U := by
    rw [TopologicalSpace.IsOpenCover, eq_top_iff]
    intro y _
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨y, hU y⟩
  let 𝒰 := M.Y.left.openCoverOfIsOpenCover U hc
  have hgl : ∀ x y, pullback.fst (U x).ι (U y).ι ≫ g x = pullback.snd (U x).ι (U y).ι ≫ g y := by
    intro x y
    refine M.hom_ext_of_flat (pullback.fst (U x).ι (U y).ι ≫ (U x).ι) N.Y.hom ?_ ?_
    · rw [Category.assoc, Category.assoc, (hg x).1, (hg y).1, pullback.condition_assoc]
    · rw [← Category.assoc, ← Category.assoc,
        (hg x).comp_eq _ (pullback.snd _ M.j) (by rw [Category.assoc]; exact pullback.condition),
        (hg y).comp_eq _ (pullback.snd _ M.j)
          (by rw [Category.assoc, ← pullback.condition (f := (U x).ι)]; exact pullback.condition)]
  obtain ⟨G, hG⟩ : ∃ G : M.Y.left ⟶ N.Y.left, ∀ y, (U y).ι ≫ G = g y :=
    ⟨𝒰.glueMorphisms g hgl, fun y => 𝒰.ι_glueMorphisms g hgl y⟩
  refine ⟨Over.homMk G (𝒰.hom_ext _ _ fun y : M.Y.left => ?_), ?_, hG⟩
  · change (U y).ι ≫ G ≫ N.Y.hom = (U y).ι ≫ M.Y.hom
    rw [← Category.assoc, hG, (hg y).1]
  · refine Scheme.Cover.hom_ext (𝒰.pullback₁ M.j) _ _ fun y : M.Y.left => ?_
    change pullback.fst M.j (U y).ι ≫ M.j ≫ G = pullback.fst M.j (U y).ι ≫ f.left ≫ N.j
    rw [pullback.condition_assoc, hG]
    exact (hg y).comp_eq _ _ pullback.condition.symm

theorem ext_unique (M : Model R A) (N : Model R A') {a b : M.Y ⟶ N.Y}
    (h : M.j ≫ a.left = M.j ≫ b.left) : a = b := by
  have := M.dominant_j
  have := N.sep
  exact over_ext_of_schemeTheoreticallyDominant M.j h

end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
variable {R K : Type} [CommRing R] [Field K] [Algebra R K] {A A' : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K)} in
private lemma isPullback_model_j_spMap_algebraMap (M : _root_.GlobalTheory.SS.Model R A) :
    IsPullback M.j A.hom M.Y.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap R K)) := by
  have h := IsPullback.of_hasPullback M.Y.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap R K))
  refine IsPullback.of_iso h ((Over.forget _).mapIso M.e) (Iso.refl _)
    (Iso.refl _) (Iso.refl _) ?_ ?_ (by simp) (by simp)
  · simp [_root_.GlobalTheory.SS.Model.j, ← Over.comp_left_assoc]
  · have := Over.w M.e.hom
    simpa using this.symm

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
variable {R K : Type} [CommRing R] [Field K] [Algebra R K] {A A' : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K)} in
private lemma eq_of_openImmersion_of_eq_on_genericFibre [IsDomain R] [IsFractionRing R K]
    (M : _root_.GlobalTheory.SS.Model R A)
    (N : _root_.GlobalTheory.SS.Model R A') {W : Scheme} (i : W ⟶ M.Y.left)
    [IsOpenImmersion i] (a b : W ⟶ N.Y.left)
    (ha : a ≫ N.Y.hom = i ≫ M.Y.hom)
    (hb : b ≫ N.Y.hom = i ≫ M.Y.hom)
    (h : pullback.snd M.j i ≫ a = pullback.snd M.j i ≫ b) :
    a = b := by
  haveI := M.smooth
  haveI := N.sep
  haveI := _root_.GlobalTheory.schemeTheoreticallyDominant_fractionField R K
  have hP := ((IsPullback.of_hasPullback M.j i).flip.paste_vert
    (isPullback_model_j_spMap_algebraMap M)).flip
  haveI := IsSchemeTheoreticallyDominant.of_isPullback hP
  have := _root_.GlobalTheory.over_ext_of_schemeTheoreticallyDominant (Y := Over.mk (i ≫ M.Y.hom))
    (X := N.Y) (pullback.snd M.j i)
    (a := Over.homMk a ha) (b := Over.homMk b hb) h
  exact congrArg (fun c => c.left) this

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
variable {R K : Type} [CommRing R] [Field K] [Algebra R K] {A A' : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K)} in
private lemma comp_eq_of_extends_of_genericFibre_comm {M : _root_.GlobalTheory.SS.Model R A}
    {N : _root_.GlobalTheory.SS.Model R A'} {f : A ⟶ A'} {U : M.Y.left.Opens}
    {g : (U : Scheme) ⟶ N.Y.left} (hg : _root_.GlobalTheory.SS.Extends M N f U g)
    {T : Scheme} (t : T ⟶ U) (s : T ⟶ A.left) (hts : s ≫ M.j = t ≫ U.ι) :
    t ≫ g = s ≫ f.left ≫ N.j := by
  have hP := isPullback_morphismRestrict M.j U
  have h2 := hg.2
  rw [← hP.lift_fst t s hts.symm, Category.assoc, h2, ← Category.assoc, hP.lift_snd]

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
variable {R K : Type} [CommRing R] [Field K] [Algebra R K] {A A' : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K)} in

theorem _root_.GlobalTheory.SS.existsUnique_extension_of_forall_defAt :
    ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
      [IsFractionRing R K] (A A' : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K)) (M : _root_.GlobalTheory.SS.Model R A)
      (N : _root_.GlobalTheory.SS.Model R A') (f : A ⟶ A'),
      (∀ y, _root_.GlobalTheory.SS.DefAt M N f y) →
        ∃! g : M.Y ⟶ N.Y,
          M.j ≫ g.left = f.left ≫ N.j := by
  intro R K _ _ _ _ _ _ A A' M N f hdef
  choose U g hyU hg using hdef
  have hcov : TopologicalSpace.IsOpenCover U := by
    rw [TopologicalSpace.IsOpenCover, eq_top_iff]
    intro y _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hyU y⟩
  have key : ∀ x y, pullback.fst (U x).ι (U y).ι ≫ g x = pullback.snd (U x).ι (U y).ι ≫ g y := by
    intro x y
    refine eq_of_openImmersion_of_eq_on_genericFibre M N (pullback.fst (U x).ι (U y).ι ≫ (U x).ι)
      _ _ ?_ ?_ ?_
    · simp only [Category.assoc, (hg x).1]
    · simp only [Category.assoc, (hg y).1]
      rw [← Category.assoc, ← pullback.condition, Category.assoc]
    · have e1 := comp_eq_of_extends_of_genericFibre_comm (hg x)
        (pullback.snd M.j (pullback.fst (U x).ι (U y).ι ≫ (U x).ι) ≫
          pullback.fst _ _)
        (pullback.fst _ _) (by rw [Category.assoc]; exact pullback.condition)
      have e2 := comp_eq_of_extends_of_genericFibre_comm (hg y)
        (pullback.snd M.j (pullback.fst (U x).ι (U y).ι ≫ (U x).ι) ≫
          pullback.snd _ _)
        (pullback.fst _ _) (by rw [Category.assoc, ← pullback.condition]; exact pullback.condition)
      simp only [Category.assoc] at e1 e2
      rw [e1, e2]
  let 𝒰 := M.Y.left.openCoverOfIsOpenCover U hcov
  have hcompat : ∀ x y, pullback.fst (𝒰.f x) (𝒰.f y) ≫ g x = pullback.snd (𝒰.f x) (𝒰.f y) ≫ g y :=
    fun x y => key x y
  let G := 𝒰.glueMorphisms g hcompat
  have hG : ∀ y, (U y).ι ≫ G = g y := fun y => 𝒰.ι_glueMorphisms g hcompat y
  have hw : G ≫ N.Y.hom = M.Y.hom := by
    refine 𝒰.hom_ext _ _ fun y => ?_
    change (U y).ι ≫ G ≫ N.Y.hom = (U y).ι ≫ M.Y.hom
    exact (Category.assoc _ _ _).symm.trans ((hG y =≫ _).trans (hg y).1)
  haveI := M.smooth
  haveI := N.sep
  haveI := _root_.GlobalTheory.schemeTheoreticallyDominant_fractionField R K
  haveI := IsSchemeTheoreticallyDominant.of_isPullback (isPullback_model_j_spMap_algebraMap M).flip
  have hex : M.j ≫ G = f.left ≫ N.j := by
    have hcovA : TopologicalSpace.IsOpenCover (fun y => M.j ⁻¹ᵁ U y) := by
      rw [TopologicalSpace.IsOpenCover, eq_top_iff]
      intro a _
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨M.j a, hyU _⟩
    refine (A.left.openCoverOfIsOpenCover _ hcovA).hom_ext _ _ fun y => ?_
    change (M.j ⁻¹ᵁ U y).ι ≫ M.j ≫ G =
      (M.j ⁻¹ᵁ U y).ι ≫ f.left ≫ N.j
    rw [← Category.assoc, ← morphismRestrict_ι, Category.assoc]
    exact (M.j ∣_ U y ≫= hG y).trans (hg y).2
  exact ⟨Over.homMk G hw, hex, fun g' hg' =>
    _root_.GlobalTheory.over_ext_of_schemeTheoreticallyDominant M.j (hg'.trans hex.symm)⟩

end GlobalTheory.SS
