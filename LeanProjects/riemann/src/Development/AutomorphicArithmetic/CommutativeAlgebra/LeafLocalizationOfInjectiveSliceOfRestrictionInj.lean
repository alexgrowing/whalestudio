import Mathlib
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.CompLeft
import Development.EtaleCohomology.KummerTheory.InjSlice
import Development.EtaleCohomology.WeilConjectures.AcycPf
import Development.EtaleCohomology.EtaleSheaves.LeafConsPf
import Development.AutomorphicArithmetic.CommutativeAlgebra.HomAcyclicFreePullbackYonedaOfInjectiveRestricti
import Development.AutomorphicArithmetic.CommutativeAlgebra.NonemptyIsoRelativeEtaleFamilyBaseChange
import Development.AutomorphicArithmetic.CommutativeAlgebra.HomAcyclicOfIsoOfIsZeroOfBiproduct
import Development.AutomorphicArithmetic.CommutativeAlgebra.HomAcyclicMappingConeChainsOfHomAcyclicFree
import Development.AutomorphicArithmetic.CommutativeAlgebra.TotalHomPresheafIsSheafInjectiveOfHomAcyclic
import Development.AutomorphicArithmetic.CommutativeAlgebra.TotalHomComplexIsKInjectiveOfBoundedInjective
import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsCohomologyClassToDerivedHomBijectiveOfKInj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafPropertiesStatement
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex CochainComplex.HomComplex
open LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafGhostCut UpperTheory.Et.Loc

noncomputable section

private theorem rmap_comp' (R : Type) [CommRing R] {U E U' E' U'' E'' : Spc} (f : U ⟶ E) (f' : U' ⟶ E') (f'' : U'' ⟶ E'')
    (u : U' ⟶ U) (e : E' ⟶ E) (u' : U'' ⟶ U') (e' : E'' ⟶ E') (c : f' ≫ e = u ≫ f) (c' : f'' ≫ e' = u' ≫ f') :
    rmap R f' f'' u' e' c' ≫ rmap R f f' u e c =
      rmap R f f'' (u' ≫ u) (e' ≫ e) (by rw [← Category.assoc, c', Category.assoc, c, Category.assoc]) := by
  simp only [rmap, Functor.map_comp]
  exact (mappingCone.map_comp _ _ _ _ _ _ _ _ _).symm

private theorem rmap_congr' (R : Type) [CommRing R] {U E U' E' : Spc} (f : U ⟶ E) (f' : U' ⟶ E')
    {u u₂ : U' ⟶ U} {e e₂ : E' ⟶ E} (c : f' ≫ e = u ≫ f) (c₂ : f' ≫ e₂ = u₂ ≫ f) (hu : u = u₂) (he : e = e₂) :
    rmap R f f' u e c = rmap R f f' u₂ e₂ c₂ := by
  subst hu he
  rfl

private def coneM {B : Scheme.{0}} {G₁ G₂ G₁' G₂' : B.Etale ⥤ Scheme.{0}} {F : G₁ ⟶ G₂} {F' : G₁' ⟶ G₂'}
    (u : G₁' ⟶ G₁) (e : G₂' ⟶ G₂) (w : F' ≫ e = u ≫ F) (q : ℕ) : coneF F' q ⟶ coneF F q where
  app U := rmap (ZMod q) (sch.map (F.app U)) (sch.map (F'.app U)) (sch.map (u.app U)) (sch.map (e.app U))
    (by rw [← Functor.map_comp, ← Functor.map_comp]; exact congrArg sch.map (NatTrans.congr_app w U))
  naturality U V a := by
    have cc : ∀ U, sch.map (F'.app U) ≫ sch.map (e.app U) = sch.map (u.app U) ≫ sch.map (F.app U) := fun U => by
      rw [← Functor.map_comp, ← Functor.map_comp]; exact congrArg sch.map (NatTrans.congr_app w U)
    have c1 : sch.map (F'.app U) ≫ sch.map (G₂'.map a) = sch.map (G₁'.map a) ≫ sch.map (F'.app V) := by
      rw [← Functor.map_comp, ← Functor.map_comp, F'.naturality]
    have c2 : sch.map (F.app U) ≫ sch.map (G₂.map a) = sch.map (G₁.map a) ≫ sch.map (F.app V) := by
      rw [← Functor.map_comp, ← Functor.map_comp, F.naturality]
    exact (rmap_comp' _ _ _ _ _ _ _ _ (cc V) c1).trans ((rmap_congr' _ _ _ _ _
      (by rw [← Functor.map_comp, ← Functor.map_comp, u.naturality])
      (by rw [← Functor.map_comp, ← Functor.map_comp, e.naturality])).trans
      (rmap_comp' _ _ _ _ _ _ _ _ c2 (cc U)).symm)

private theorem pm_y {B Y Y' U V : Scheme.{0}} (p : Y ⟶ B) (g : Y' ⟶ Y) (x : U ⟶ B) (y : V ⟶ B) (a : U ⟶ V)
    (h : x = a ≫ y) (c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈) :
    pullback.map (g ≫ p) x (g ≫ p) y (𝟙 Y') a (𝟙 B) c₁ c₂ ≫ pullback.map (g ≫ p) y p y g (𝟙 V) (𝟙 B) c₃ c₄ =
      pullback.map (g ≫ p) x p x g (𝟙 U) (𝟙 B) c₅ c₆ ≫ pullback.map p x p y (𝟙 Y) a (𝟙 B) c₇ c₈ := by
  apply pullback.hom_ext <;> simp [pullback.map, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc, h]

private theorem pm_w {A₁ A₂ A₃ A₄ W B : Scheme.{0}} (s₁ : A₁ ⟶ B) (s₂ : A₂ ⟶ B) (s₃ : A₃ ⟶ B) (s₄ : A₄ ⟶ B) (ι : W ⟶ B)
    (r : A₁ ⟶ A₂) (m₂ : A₂ ⟶ A₄) (m₁ : A₁ ⟶ A₃) (r' : A₃ ⟶ A₄) (h : r ≫ m₂ = m₁ ≫ r') (c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈) :
    pullback.map s₁ ι s₂ ι r (𝟙 W) (𝟙 B) c₁ c₂ ≫ pullback.map s₂ ι s₄ ι m₂ (𝟙 W) (𝟙 B) c₃ c₄ =
      pullback.map s₁ ι s₃ ι m₁ (𝟙 W) (𝟙 B) c₅ c₆ ≫ pullback.map s₃ ι s₄ ι r' (𝟙 W) (𝟙 B) c₇ c₈ := by
  apply pullback.hom_ext
  · simp [pullback.map, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc, h]
  · simp [pullback.map, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc]

private theorem mY_nat {B Y Y' : Scheme.{0}} (p : Y ⟶ B) (g : Y' ⟶ Y) {U V : B.Etale} (a : U ⟶ V) :
    resY (g ≫ p) a ≫ mY p g V = mY p g U ≫ resY p a :=
  pm_y p g U.hom V.hom a.left (by simpa using a.w.symm) _ _ _ _ _ _ _ _

private theorem bY_nat {B Y : Scheme.{0}} (p : Y ⟶ B) {U V : B.Etale} (a : U ⟶ V) :
    resY p a ≫ toBY p V = toBY p U ≫ a.left :=
  pullback.lift_snd _ _ _

private theorem mW_nat {B Y Y' W : Scheme.{0}} (p : Y ⟶ B) (g : Y' ⟶ Y) (ι : W ⟶ B) {U V : B.Etale} (a : U ⟶ V) :
    resYW (g ≫ p) ι a ≫ mW p g ι V = mW p g ι U ≫ resYW p ι a :=
  pm_w _ _ _ _ ι _ _ _ _ (mY_nat p g a) _ _ _ _ _ _ _ _

private theorem bW_nat {B Y W : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B) {U V : B.Etale} (a : U ⟶ V) :
    resYW p ι a ≫ toBW p ι V = toBW p ι U ≫ resBW ι a :=
  pm_w _ _ _ _ ι _ _ _ _ (bY_nat p a) _ _ _ _ _ _ _ _

private def mYn {B Y Y' : Scheme.{0}} (p : Y ⟶ B) (g : Y' ⟶ Y) : gY (g ≫ p) ⟶ gY p where
  app U := mY p g U
  naturality _ _ a := mY_nat p g a

private def bY {B Y : Scheme.{0}} (p : Y ⟶ B) : gY p ⟶ gB B where
  app U := toBY p U
  naturality _ _ a := bY_nat p a

private def mWn {B Y Y' W : Scheme.{0}} (p : Y ⟶ B) (g : Y' ⟶ Y) (ι : W ⟶ B) : gYW (g ≫ p) ι ⟶ gYW p ι where
  app U := mW p g ι U
  naturality _ _ a := mW_nat p g ι a

private def bW {B Y W : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B) : gYW p ι ⟶ gBW ι where
  app U := toBW p ι U
  naturality _ _ a := bW_nat p ι a

theorem UpperTheory.leafLocalization_of_injective_slice_of_restriction_injective :
    LateralTheory.KummerTheory.InjSlice → LateralTheory.EWeil.AcycPf.RestrInj → LateralTheory.E.LeafConsPf.LeafLoc := by
  intro hS hR q _ i B W Y0 Y1 Y2 ι _ p g1 g2
  obtain ⟨-, hinj, hGE, -⟩ := GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties (ZMod q) (tw q i)
  have key : ∀ {G₁ G₂ : B.Etale ⥤ Scheme.{0}} (F : G₁ ⟶ G₂), Good (G₁ ⋙ yoneda ⋙ free (ZMod q)) →
      Good (G₂ ⋙ yoneda ⋙ free (ZMod q)) →
      ∃ h, (TC (coneF F q) (res (ZMod q) (tw q i)) h).IsKInjective := by
    intro G₁ G₂ F h₁ h₂
    obtain ⟨a, b⟩ := UpperTheory.homAcyclic_mappingCone_chains_of_homAcyclic_free q F h₁ h₂
    have c := UpperTheory.totalHomPresheaf_isSheaf_injective_of_homAcyclic q (coneF F q) (res (ZMod q) (tw q i)) a hinj
    choose h hi using c
    refine ⟨h, UpperTheory.totalHomComplex_isKInjective_of_bounded_injective q _ _ h hi b fun n hn => ?_⟩
    exact (res (ZMod q) (tw q i)).isZero_of_isStrictlyGE 0 n hn
  have gy : ∀ {Y : Scheme.{0}} (P : Y ⟶ B), Good (gY P ⋙ yoneda ⋙ free (ZMod q)) :=
    fun P => UpperTheory.homAcyclic_free_pullback_yoneda_of_injective_restriction hS hR q P
  have tr : ∀ {G G' : B.Etale ⥤ Scheme.{0}}, Nonempty (G ≅ G') → Good (G' ⋙ yoneda ⋙ free (ZMod q)) →
      Good (G ⋙ yoneda ⋙ free (ZMod q)) := by
    rintro G G' ⟨e⟩ h
    exact (UpperTheory.homAcyclic_of_iso_of_isZero_of_biproduct q B).1 _ _ ⟨Functor.isoWhiskerRight e.symm _⟩ h
  have gyw : ∀ {Y : Scheme.{0}} (P : Y ⟶ B), Good (gYW P ι ⋙ yoneda ⋙ free (ZMod q)) :=
    fun P => tr (UpperTheory.nonempty_iso_relativeEtaleFamily_baseChange P ι).1 (gy _)
  have gb : Good (gB B ⋙ yoneda ⋙ free (ZMod q)) := tr (UpperTheory.nonempty_iso_relativeEtaleFamily_baseChange p ι).2.1 (gy _)
  have gbw : Good (gBW ι ⋙ yoneda ⋙ free (ZMod q)) := tr (UpperTheory.nonempty_iso_relativeEtaleFamily_baseChange p ι).2.2 (gy _)
  obtain ⟨h0, k0⟩ := key (fY p ι) (gyw _) (gy _)
  obtain ⟨h1, k1⟩ := key (fY (g1 ≫ p) ι) (gyw _) (gy _)
  obtain ⟨h2, k2⟩ := key (fY (g2 ≫ g1 ≫ p) ι) (gyw _) (gy _)
  obtain ⟨hL, kL⟩ := key (fB ι) gbw gb
  obtain ⟨l, lb, ln, lm⟩ := UpperTheory.exists_cohomologyClass_to_derivedHom_bijective_of_kInjective q B (res (ZMod q) (tw q i))
  have w1 : fY (g1 ≫ p) ι ≫ mYn p g1 = mWn p g1 ι ≫ fY p ι :=
    NatTrans.ext (funext fun U => (pullback.lift_fst _ _ _).symm)
  have w2 : fY (g2 ≫ g1 ≫ p) ι ≫ mYn (g1 ≫ p) g2 = mWn (g1 ≫ p) g2 ι ≫ fY (g1 ≫ p) ι :=
    NatTrans.ext (funext fun U => (pullback.lift_fst _ _ _).symm)
  have w3 : fY (g2 ≫ g1 ≫ p) ι ≫ bY (g2 ≫ g1 ≫ p) = bW (g2 ≫ g1 ≫ p) ι ≫ fB ι :=
    NatTrans.ext (funext fun U => (pullback.lift_fst _ _ _).symm)
  refine ⟨DerivedCategory.Q.obj (TC _ _ h0), DerivedCategory.Q.obj (TC _ _ h1), DerivedCategory.Q.obj (TC _ _ h2),
    DerivedCategory.Q.obj (TC _ _ hL),
    DerivedCategory.Q.map (TM (coneM _ _ w1 q) _ h0 h1), DerivedCategory.Q.map (TM (coneM _ _ w2 q) _ h1 h2),
    DerivedCategory.Q.map (TM (coneM _ _ w3 q) _ hL h2),
    fun U n => l _ h0 U n, fun U n => l _ h1 U n, fun U n => l _ h2 U n, fun U n => l _ hL U n,
    ⟨fun U n => (lb _ h0 k0 U n), fun U U' a n y => ln _ h0 U U' a n y⟩,
    ⟨fun U n => (lb _ h1 k1 U n), fun U U' a n y => ln _ h1 U U' a n y⟩,
    ⟨fun U n => (lb _ h2 k2 U n), fun U U' a n y => ln _ h2 U U' a n y⟩,
    ⟨fun U n => (lb _ hL kL U n), fun U U' a n y => ln _ hL U U' a n y⟩,
    fun U n y => lm _ _ h0 h1 (coneM _ _ w1 q) U n y,
    fun U n y => lm _ _ h1 h2 (coneM _ _ w2 q) U n y,
    fun U n y => lm _ _ hL h2 (coneM _ _ w3 q) U n y⟩

end
