import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.AffineBlowup
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupBasic
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupExistence
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.BlowupChart
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.CoordinateSubstitution
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.CoordinateBlowupChart
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.ChartRing
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleCoordinates
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheaf
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace BlowupChart

variable {X X₁ : Scheme.{u}} {k : Type u} [Field k]
  {p : X ⟶ Spec (CommRingCat.of k)} {π : X₁ ⟶ X} {U : X.Opens} {m : ℕ}
  {c : EtaleChart p U m} {S : Finset (Fin m)} {s : Fin m}

private theorem comp_hom_apply {R₁ R₂ R₃ : CommRingCat.{u}} (a : R₁ ⟶ R₂)
    (b : R₂ ⟶ R₃) (x : R₁) : (a ≫ b).hom x = b.hom (a.hom x) := rfl

private theorem comp_appTop_apply {A B C : Scheme.{u}} (φ : A ⟶ B) (ψ : B ⟶ C)
    (t : Γ(C, ⊤)) :
    ((φ ≫ ψ).appTop).hom t = (φ.appTop).hom ((ψ.appTop).hom t) := rfl

private theorem presheaf_map_eq {T : Type u} [TopologicalSpace T]
    (F : (TopologicalSpace.Opens T)ᵒᵖ ⥤ CommRingCat.{u})
    {A B : (TopologicalSpace.Opens T)ᵒᵖ} (α β : A ⟶ B) : F.map α = F.map β := by
  rw [Quiver.Hom.unop_inj (Subsingleton.elim α.unop β.unop)]

private theorem presheaf_map_comp_eq {T : Type u} [TopologicalSpace T]
    (F : (TopologicalSpace.Opens T)ᵒᵖ ⥤ CommRingCat.{u})
    {A B C : (TopologicalSpace.Opens T)ᵒᵖ} (a : A ⟶ B) (b : B ⟶ C) (c : A ⟶ C) :
    F.map a ≫ F.map b = F.map c := by
  rw [← F.map_comp]
  exact presheaf_map_eq F _ c

private theorem top_le_ι_preimage {Y : Scheme.{u}} (W : Y.Opens) :
    (⊤ : W.toScheme.Opens) ≤ W.ι ⁻¹ᵁ W := by
  intro x _
  exact x.2

private theorem top_le_preimage_top {Y Y₁ : Scheme.{u}} (g : Y₁ ⟶ Y) :
    (⊤ : Y₁.Opens) ≤ g ⁻¹ᵁ (⊤ : Y.Opens) := by
  simp

private theorem topIso_inv_eq_ι_appLE {Y : Scheme.{u}} (W : Y.Opens) :
    W.topIso.inv = W.ι.appLE W ⊤ (top_le_ι_preimage W) := by
  simp [Scheme.Hom.appLE]
  exact (presheaf_map_comp_eq Y.presheaf _ _ _).symm

private theorem appLE_congr {Y Y₁ : Scheme.{u}} (g₁ g₂ : Y₁ ⟶ Y) (h : g₁ = g₂)
    (W : Y.Opens) (V : Y₁.Opens) (e₁ : V ≤ g₁ ⁻¹ᵁ W) (e₂ : V ≤ g₂ ⁻¹ᵁ W) :
    g₁.appLE W V e₁ = g₂.appLE W V e₂ := by
  subst h
  rfl

private theorem appLE_topIso_inv_comp {Y Y₁ : Scheme.{u}} (f : Y₁ ⟶ Y)
    (W : Y.Opens) (V : Y₁.Opens) (hV : V ≤ f ⁻¹ᵁ W) :
    f.appLE W V hV ≫ V.topIso.inv = W.topIso.inv ≫ (f.resLE W V hV).appTop := by
  have happ : (f.resLE W V hV).appTop
      = (f.resLE W V hV).appLE ⊤ ⊤ (top_le_preimage_top (f.resLE W V hV)) :=
    (Scheme.Hom.appLE_eq_app (f.resLE W V hV)).symm
  rw [topIso_inv_eq_ι_appLE, topIso_inv_eq_ι_appLE, happ,
    Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
  exact appLE_congr (V.ι ≫ f) (f.resLE W V hV ≫ W.ι) (by simp) W ⊤ _ _

private theorem topIso_hom_comp_appLE {Y Y₁ : Scheme.{u}} (f : Y₁ ⟶ Y)
    (W : Y.Opens) (V : Y₁.Opens) (hV : V ≤ f ⁻¹ᵁ W) :
    W.topIso.hom ≫ f.appLE W V hV = (f.resLE W V hV).appTop ≫ V.topIso.hom := by
  have h := appLE_topIso_inv_comp f W V hV
  calc W.topIso.hom ≫ f.appLE W V hV
      = W.topIso.hom ≫ (f.appLE W V hV ≫ V.topIso.inv) ≫ V.topIso.hom := by
        simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    _ = W.topIso.hom ≫ (W.topIso.inv ≫ (f.resLE W V hV).appTop) ≫ V.topIso.hom := by rw [h]
    _ = (f.resLE W V hV).appTop ≫ V.topIso.hom := by
        simp only [Category.assoc, Iso.hom_inv_id_assoc]

private theorem appLE_topIso_hom_apply {Y Y₁ : Scheme.{u}} (f : Y₁ ⟶ Y)
    (W : Y.Opens) (V : Y₁.Opens) (hV : V ≤ f ⁻¹ᵁ W) (y : Γ(W.toScheme, ⊤)) :
    (f.appLE W V hV).hom (W.topIso.hom.hom y)
      = V.topIso.hom.hom ((f.resLE W V hV).appTop.hom y) := by
  have h2 : (W.topIso.hom ≫ f.appLE W V hV).hom y
      = ((f.resLE W V hV).appTop ≫ V.topIso.hom).hom y := by
    rw [topIso_hom_comp_appLE f W V hV]
  rw [comp_hom_apply, comp_hom_apply] at h2
  exact h2

private theorem topIso_inv_appLE_apply {Y Y₁ : Scheme.{u}} (f : Y₁ ⟶ Y) (W : Y.Opens)
    (V : Y₁.Opens) (hV : V ≤ f ⁻¹ᵁ W) (a : Γ(Y, W)) :
    V.topIso.inv.hom ((f.appLE W V hV).hom a)
      = ((f.resLE W V hV).appTop).hom (W.topIso.inv.hom a) := by
  have h := appLE_topIso_inv_comp f W V hV
  have h2 := congrArg (fun φ : Γ(Y, W) ⟶ Γ(V.toScheme, ⊤) => CommRingCat.Hom.hom φ a) h
  rw [comp_hom_apply, comp_hom_apply] at h2
  exact h2

theorem restrictIdeal_comap (B : BlowupChart π c S s) (D : X.IdealSheafData) :
    restrictIdeal (D.comap π) B.domain =
      (restrictIdeal D U).comap (π.resLE U B.domain B.domain_le) := by
  rw [restrictIdeal_eq_comap_ι, restrictIdeal_eq_comap_ι,
    ← AlgebraicGeometry.Scheme.IdealSheafData.comap_comp,
    ← AlgebraicGeometry.Scheme.IdealSheafData.comap_comp,
    AlgebraicGeometry.Scheme.Hom.resLE_comp_ι]

theorem restrictIdeal_exceptionalIdeal (B : BlowupChart π c S s)
    (Z : X.IdealSheafData) (hs : s ∈ S) (hZ : restrictIdeal Z U = c.coordIdeal S) :
    restrictIdeal (Blowup.exceptionalIdeal π Z) B.domain = B.chart.coordIdeal {s} := by
  have h1 := restrictIdeal_comap B Z
  rw [Blowup.exceptionalIdeal_eq_comap, h1, hZ]
  exact comap_coordIdeal_center c B.chart (π.resLE U B.domain B.domain_le) B.comm hs

theorem restrictIdeal_comap_coordIdeal_of_mem (B : BlowupChart π c S s)
    (D : X.IdealSheafData) (j : Fin m) (hj : j ∈ S) (hjs : j ≠ s)
    (hD : restrictIdeal D U = c.coordIdeal {j}) :
    restrictIdeal (D.comap π) B.domain =
      B.chart.coordIdeal {j} * B.chart.coordIdeal {s} := by
  rw [restrictIdeal_comap B D, hD]
  exact comap_coordIdeal_singleton_of_mem c B.chart
    (π.resLE U B.domain B.domain_le) B.comm j hj hjs

theorem restrictIdeal_comap_coordIdeal_self (B : BlowupChart π c S s)
    (D : X.IdealSheafData) (hD : restrictIdeal D U = c.coordIdeal {s}) :
    restrictIdeal (D.comap π) B.domain = B.chart.coordIdeal {s} := by
  rw [restrictIdeal_comap B D, hD]
  exact comap_coordIdeal_singleton_self c B.chart
    (π.resLE U B.domain B.domain_le) B.comm

theorem restrictIdeal_comap_coordIdeal_of_not_mem (B : BlowupChart π c S s)
    (D : X.IdealSheafData) (j : Fin m) (hj : j ∉ S)
    (hD : restrictIdeal D U = c.coordIdeal {j}) :
    restrictIdeal (D.comap π) B.domain = B.chart.coordIdeal {j} := by
  rw [restrictIdeal_comap B D, hD]
  exact comap_coordIdeal_singleton_of_notMem c B.chart
    (π.resLE U B.domain B.domain_le) B.comm j hj

theorem restrictIdeal_comap_top (B : BlowupChart π c S s)
    (D : X.IdealSheafData) (hD : restrictIdeal D U = ⊤) :
    restrictIdeal (D.comap π) B.domain = ⊤ := by
  rw [restrictIdeal_comap B D, hD, Scheme.IdealSheafData.comap_top]

theorem appLE_coord_of_mem (B : BlowupChart π c S s) (i : Fin m)
    (hi : i ∈ S) (his : i ≠ s) :
    (π.appLE U B.domain B.domain_le).hom (c.coord i) =
      B.chart.coord i * B.chart.coord s := by
  have h0 : ((B.chart.map ≫ coordBlowupSubstMap k m S s).appTop).hom
        (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up i : ULift.{u} (Fin m)))
      = ((π.resLE U B.domain B.domain_le ≫ c.map).appTop).hom
        (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up i : ULift.{u} (Fin m))) :=
    congrArg (fun φ : B.domain.toScheme ⟶ affineSpaceFin k m =>
      (φ.appTop).hom
        (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up i : ULift.{u} (Fin m)))) B.comm
  rw [comp_appTop_apply, comp_appTop_apply,
    coordBlowupSubstMap_appTop_coord_of_mem k m S s i hi his, map_mul] at h0
  have hkey := h0.symm
  rw [EtaleChart.coord_def c i, EtaleChart.coord_def B.chart i, EtaleChart.coord_def B.chart s,
    appLE_topIso_hom_apply π U B.domain B.domain_le, hkey, map_mul]

theorem appLE_coord_self (B : BlowupChart π c S s) :
    (π.appLE U B.domain B.domain_le).hom (c.coord s) = B.chart.coord s := by
  have h1 : (coordBlowupSubstMap k m S s).appTop ≫ B.chart.map.appTop
      = c.map.appTop ≫ (π.resLE U B.domain B.domain_le).appTop := by
    refine CommRingCat.hom_ext (RingHom.ext fun z => ?_)
    exact congrArg (fun φ : B.domain.toScheme ⟶ affineSpaceFin k m => (φ.appTop).hom z) B.comm
  have h2 : B.chart.map.appTop.hom
        ((coordBlowupSubstMap k m S s).appTop.hom
          (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up s : ULift.{u} (Fin m))))
      = (π.resLE U B.domain B.domain_le).appTop.hom
          (c.map.appTop.hom
            (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up s : ULift.{u} (Fin m)))) := by
    have h3 : ((coordBlowupSubstMap k m S s).appTop ≫ B.chart.map.appTop).hom
          (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up s : ULift.{u} (Fin m)))
        = (c.map.appTop ≫ (π.resLE U B.domain B.domain_le).appTop).hom
          (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up s : ULift.{u} (Fin m))) := by
      rw [h1]
    exact h3
  rw [coordBlowupSubstMap_appTop_coord_self] at h2
  rw [EtaleChart.coord_def c s, EtaleChart.coord_def B.chart s, h2]
  exact appLE_topIso_hom_apply π U B.domain B.domain_le _

theorem appLE_coord_of_not_mem (B : BlowupChart π c S s) (i : Fin m) (hi : i ∉ S) :
    (π.appLE U B.domain B.domain_le).hom (c.coord i) = B.chart.coord i := by
  have hcomm : (coordBlowupSubstMap k m S s).appTop ≫ (B.chart.map).appTop
      = (c.map).appTop ≫ (π.resLE U B.domain B.domain_le).appTop := by
    refine CommRingCat.hom_ext (RingHom.ext fun z => ?_)
    exact congrArg (fun φ : B.domain.toScheme ⟶ affineSpaceFin k m => (φ.appTop).hom z) B.comm
  have hx : (B.chart.map).appTop.hom
        ((coordBlowupSubstMap k m S s).appTop.hom
          (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up i : ULift.{u} (Fin m))))
      = (π.resLE U B.domain B.domain_le).appTop.hom
        ((c.map).appTop.hom
          (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up i : ULift.{u} (Fin m)))) := by
    have h2 : ((coordBlowupSubstMap k m S s).appTop ≫ (B.chart.map).appTop).hom
          (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up i : ULift.{u} (Fin m)))
        = ((c.map).appTop ≫ (π.resLE U B.domain B.domain_le).appTop).hom
          (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up i : ULift.{u} (Fin m))) := by
      rw [hcomm]
    rw [comp_hom_apply, comp_hom_apply] at h2
    exact h2
  rw [coordBlowupSubstMap_appTop_coord_of_notMem k m S s i hi] at hx
  simp only [EtaleChart.coord_def]
  rw [hx]
  exact appLE_topIso_hom_apply π U B.domain B.domain_le _

theorem appLE_coord (B : BlowupChart π c S s) (i : Fin m) :
    (π.appLE U B.domain B.domain_le).hom (c.coord i) =
      if i ∈ S ∧ i ≠ s then B.chart.coord i * B.chart.coord s else B.chart.coord i := by
  by_cases h : i ∈ S ∧ i ≠ s
  · rw [if_pos h]
    exact B.appLE_coord_of_mem i h.1 h.2
  · rw [if_neg h]
    by_cases hi : i ∈ S
    · have hieq : i = s := by
        by_contra hne
        exact h ⟨hi, hne⟩
      rw [hieq]
      exact B.appLE_coord_self
    · exact B.appLE_coord_of_not_mem i hi

def coordEvalHom (B : BlowupChart π c S s) :
    MvPolynomial (ULift.{u} (Fin m)) Γ(X, U) →+* Γ(X₁, B.domain) :=
  MvPolynomial.eval₂Hom (π.appLE U B.domain B.domain_le).hom
    (fun i : ULift.{u} (Fin m) => B.chart.coord i.down)

theorem coordEvalHom_def (B : BlowupChart π c S s) :
    B.coordEvalHom = MvPolynomial.eval₂Hom (π.appLE U B.domain B.domain_le).hom
      (fun i : ULift.{u} (Fin m) => B.chart.coord i.down) := rfl

theorem coordEvalHom_C (B : BlowupChart π c S s) (a : Γ(X, U)) :
    B.coordEvalHom (MvPolynomial.C a) = (π.appLE U B.domain B.domain_le).hom a := by
  simp [coordEvalHom]

theorem coordEvalHom_X (B : BlowupChart π c S s) (i : Fin m) :
    B.coordEvalHom (MvPolynomial.X (ULift.up i : ULift.{u} (Fin m))) = B.chart.coord i := by
  simp [coordEvalHom]

def coordRelation (_B : BlowupChart π c S s) (i : Fin m) :
    MvPolynomial (ULift.{u} (Fin m)) Γ(X, U) :=
  (if i ∈ S ∧ i ≠ s then
      MvPolynomial.X (ULift.up i : ULift.{u} (Fin m)) *
        MvPolynomial.X (ULift.up s : ULift.{u} (Fin m))
    else MvPolynomial.X (ULift.up i : ULift.{u} (Fin m))) - MvPolynomial.C (c.coord i)

theorem coordRelation_def (B : BlowupChart π c S s) (i : Fin m) :
    B.coordRelation i =
      (if i ∈ S ∧ i ≠ s then
          MvPolynomial.X (ULift.up i : ULift.{u} (Fin m)) *
            MvPolynomial.X (ULift.up s : ULift.{u} (Fin m))
        else MvPolynomial.X (ULift.up i : ULift.{u} (Fin m))) -
        MvPolynomial.C (c.coord i) := rfl

theorem coordEvalHom_coordRelation (B : BlowupChart π c S s) (i : Fin m) :
    B.coordEvalHom (B.coordRelation i) = 0 := by
  rw [coordRelation_def]
  by_cases h : i ∈ S ∧ i ≠ s
  · rw [if_pos h, map_sub, map_mul, coordEvalHom_X, coordEvalHom_X, coordEvalHom_C, B.appLE_coord i,
      if_pos h, sub_self]
  · rw [if_neg h, map_sub, coordEvalHom_X, coordEvalHom_C, B.appLE_coord i, if_neg h, sub_self]

theorem coordEvalHom_eq_zero_of_mem_span (B : BlowupChart π c S s)
    (a : MvPolynomial (ULift.{u} (Fin m)) Γ(X, U))
    (ha : a ∈ Ideal.span (Set.range B.coordRelation)) : B.coordEvalHom a = 0 := by
  have h : Ideal.span (Set.range B.coordRelation) ≤ RingHom.ker B.coordEvalHom := by
    rw [Ideal.span_le]
    rintro x ⟨i, rfl⟩
    exact RingHom.mem_ker.mpr (B.coordEvalHom_coordRelation i)
  exact RingHom.mem_ker.mp (h ha)

def coordEvalQuotientHom (B : BlowupChart π c S s) :
    (MvPolynomial (ULift.{u} (Fin m)) Γ(X, U) ⧸ Ideal.span (Set.range B.coordRelation)) →+*
      Γ(X₁, B.domain) :=
  Ideal.Quotient.lift (Ideal.span (Set.range B.coordRelation)) B.coordEvalHom
    B.coordEvalHom_eq_zero_of_mem_span

theorem coordEvalQuotientHom_mk (B : BlowupChart π c S s)
    (a : MvPolynomial (ULift.{u} (Fin m)) Γ(X, U)) :
    B.coordEvalQuotientHom (Ideal.Quotient.mk (Ideal.span (Set.range B.coordRelation)) a) = B.coordEvalHom a := rfl

private theorem iso_inv_hom_apply {R T : CommRingCat.{u}} (e : R ≅ T) (x : R) :
    e.inv.hom (e.hom.hom x) = x := by
  have h := congrArg (fun φ : R ⟶ R => CommRingCat.Hom.hom φ x) e.hom_inv_id
  simpa only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_id,
    RingHom.id_apply] using h

private theorem iso_hom_inv_apply {R T : CommRingCat.{u}} (e : R ≅ T) (x : T) :
    e.hom.hom (e.inv.hom x) = x := by
  have h := congrArg (fun φ : T ⟶ T => CommRingCat.Hom.hom φ x) e.inv_hom_id
  simpa only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_id,
    RingHom.id_apply] using h

private def mvPolynomialIsoGlobalSectionsAffineSpace (k : Type u) [Field k] (m : ℕ) :
    CommRingCat.of (MvPolynomial (ULift.{u} (Fin m)) k) ≅ Γ(affineSpaceFin k m, ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (ULift.{u} (Fin m)) k))).symm ≪≫
    Scheme.Γ.mapIso (AffineSpace.SpecIso (ULift.{u} (Fin m)) (CommRingCat.of k)).op

private theorem mvPolynomialIsoGlobalSectionsAffineSpace_hom_apply (k : Type u) [Field k] (m : ℕ)
    (x : MvPolynomial (ULift.{u} (Fin m)) k) :
    (mvPolynomialIsoGlobalSectionsAffineSpace k m).hom.hom x = affineSpaceGlobalSectionsHom k m x := rfl

private theorem mvPolynomialIsoGlobalSectionsAffineSpace_hom_X (k : Type u) [Field k] (m : ℕ)
    (i : ULift.{u} (Fin m)) :
    (mvPolynomialIsoGlobalSectionsAffineSpace k m).hom.hom (MvPolynomial.X i)
      = AffineSpace.coord (Spec (CommRingCat.of k)) i := by
  have hcancel : ∀ x : Γ(affineSpaceFin k m, ⊤),
      ((AffineSpace.SpecIso (ULift.{u} (Fin m)) (CommRingCat.of k)).hom.appTop).hom
        (((AffineSpace.SpecIso (ULift.{u} (Fin m)) (CommRingCat.of k)).inv.appTop).hom x) = x := by
    intro x
    exact iso_hom_inv_apply
      (Scheme.Γ.mapIso (AffineSpace.SpecIso (ULift.{u} (Fin m)) (CommRingCat.of k)).op) x
  have h := AffineSpace.SpecIso_inv_appTop_coord (CommRingCat.of k) i
  have h2 : (mvPolynomialIsoGlobalSectionsAffineSpace k m).hom.hom (MvPolynomial.X i)
      = ((AffineSpace.SpecIso (ULift.{u} (Fin m)) (CommRingCat.of k)).hom.appTop).hom
        (((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (ULift.{u} (Fin m)) k))).inv).hom
          (MvPolynomial.X i)) := rfl
  rw [h2, ← h, hcancel]

private theorem specIso_hom_comp_map_C (k : Type u) [Field k] (m : ℕ) :
    (AffineSpace.SpecIso (ULift.{u} (Fin m)) (CommRingCat.of k)).hom ≫
        Spec.map (CommRingCat.ofHom
          (MvPolynomial.C : k →+* MvPolynomial (ULift.{u} (Fin m)) k)) =
      affineSpaceFinToSpec k m := by
  have h : (AffineSpace.SpecIso (ULift.{u} (Fin m)) (CommRingCat.of k)).inv ≫
      affineSpaceFinToSpec k m =
      Spec.map (CommRingCat.ofHom
        (MvPolynomial.C : k →+* MvPolynomial (ULift.{u} (Fin m)) k)) := by
    simp
  rw [← h, Iso.hom_inv_id_assoc]

private theorem mvPolynomialIsoGlobalSectionsAffineSpace_hom_C (k : Type u) [Field k] (m : ℕ) (a : k) :
    (mvPolynomialIsoGlobalSectionsAffineSpace k m).hom.hom (MvPolynomial.C a)
      = ((affineSpaceFinToSpec k m).appTop).hom
        (((Scheme.ΓSpecIso (CommRingCat.of k)).inv).hom a) := by
  have h0 : (Spec.map (CommRingCat.ofHom
        (MvPolynomial.C : k →+* MvPolynomial (ULift.{u} (Fin m)) k))).appTop ≫
      (AffineSpace.SpecIso (ULift.{u} (Fin m)) (CommRingCat.of k)).hom.appTop
      = (affineSpaceFinToSpec k m).appTop := by
    refine CommRingCat.hom_ext (RingHom.ext fun z => ?_)
    exact congrArg (fun φ : affineSpaceFin k m ⟶ Spec (CommRingCat.of k) =>
      (φ.appTop).hom z) (specIso_hom_comp_map_C k m)
  have key : (CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial (ULift.{u} (Fin m)) k)) ≫
      (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (ULift.{u} (Fin m)) k))).inv ≫
        (AffineSpace.SpecIso (ULift.{u} (Fin m)) (CommRingCat.of k)).hom.appTop
      = (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (affineSpaceFinToSpec k m).appTop := by
    rw [← Category.assoc, Scheme.ΓSpecIso_inv_naturality, Category.assoc, h0]
  have e1 : (mvPolynomialIsoGlobalSectionsAffineSpace k m).hom.hom (MvPolynomial.C a)
      = ((CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial (ULift.{u} (Fin m)) k)) ≫
          (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (ULift.{u} (Fin m)) k))).inv ≫
            (AffineSpace.SpecIso (ULift.{u} (Fin m)) (CommRingCat.of k)).hom.appTop).hom a := rfl
  rw [e1, key]
  rfl

private theorem affineSpaceFin_globalSections_hom_ext (k : Type u) [Field k] (m : ℕ) {T : CommRingCat.{u}}
    (u v : Γ(affineSpaceFin k m, ⊤) ⟶ T)
    (hτ : ∀ t : Γ(Spec (CommRingCat.of k), ⊤),
      u.hom (((affineSpaceFinToSpec k m).appTop).hom t)
        = v.hom (((affineSpaceFinToSpec k m).appTop).hom t))
    (hc : ∀ j : Fin m,
      u.hom (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up j : ULift.{u} (Fin m)))
        = v.hom (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up j : ULift.{u} (Fin m)))) :
    u = v := by
  have key : ∀ w : MvPolynomial (ULift.{u} (Fin m)) k,
      u.hom ((mvPolynomialIsoGlobalSectionsAffineSpace k m).hom.hom w) = v.hom ((mvPolynomialIsoGlobalSectionsAffineSpace k m).hom.hom w) := by
    intro w
    refine MvPolynomial.induction_on
      (motive := fun z : MvPolynomial (ULift.{u} (Fin m)) k =>
        u.hom ((mvPolynomialIsoGlobalSectionsAffineSpace k m).hom.hom z) = v.hom ((mvPolynomialIsoGlobalSectionsAffineSpace k m).hom.hom z))
      w (fun a => ?_) (fun q r hq hr => ?_) (fun q i hq => ?_)
    · rw [mvPolynomialIsoGlobalSectionsAffineSpace_hom_C]
      exact hτ _
    · simp only [map_add]
      rw [hq, hr]
    · obtain ⟨j⟩ := i
      simp only [map_mul]
      rw [hq, mvPolynomialIsoGlobalSectionsAffineSpace_hom_X, hc j]
  refine CommRingCat.hom_ext (RingHom.ext fun z => ?_)
  have h := key ((mvPolynomialIsoGlobalSectionsAffineSpace k m).inv.hom z)
  rwa [iso_hom_inv_apply] at h

private theorem coordBlowupSubstMap_appTop_affineSpaceFinToSpec (t : Γ(Spec (CommRingCat.of k), ⊤)) :
    ((coordBlowupSubstMap k m S s).appTop).hom (((affineSpaceFinToSpec k m).appTop).hom t)
      = ((affineSpaceFinToSpec k m).appTop).hom t := by
  have h : ((coordBlowupSubstMap k m S s ≫ affineSpaceFinToSpec k m).appTop).hom t
      = ((affineSpaceFinToSpec k m).appTop).hom t :=
    congrArg (fun φ : affineSpaceFin k m ⟶ Spec (CommRingCat.of k) => (φ.appTop).hom t)
      (coordBlowupSubstMap_comp_affineSpaceFinToSpec k m S s)
  rw [comp_appTop_apply] at h
  exact h

private theorem chart_appTop_coordBlowupSubstMap_apply (B : BlowupChart π c S s) (z : Γ(affineSpaceFin k m, ⊤)) :
    (B.chart.map.appTop).hom (((coordBlowupSubstMap k m S s).appTop).hom z)
      = ((π.resLE U B.domain B.domain_le).appTop).hom ((c.map.appTop).hom z) := by
  have h : ((B.chart.map ≫ coordBlowupSubstMap k m S s).appTop).hom z
      = ((π.resLE U B.domain B.domain_le ≫ c.map).appTop).hom z :=
    congrArg (fun φ : B.domain.toScheme ⟶ affineSpaceFin k m => (φ.appTop).hom z) B.comm
  rw [comp_appTop_apply, comp_appTop_apply] at h
  exact h

private theorem etaleChart_appTop_affineSpaceFinToSpec_apply {Y : Scheme.{u}} {q : Y ⟶ Spec (CommRingCat.of k)}
    {W : Y.Opens} (d : EtaleChart q W m) (t : Γ(Spec (CommRingCat.of k), ⊤)) :
    W.topIso.hom.hom ((d.map.appTop).hom (((affineSpaceFinToSpec k m).appTop).hom t))
      = sectionsAlgebraMap k q W (((Scheme.ΓSpecIso (CommRingCat.of k)).hom).hom t) := by
  have ha : affineSpaceGlobalSectionsHom k m
      (MvPolynomial.C (((Scheme.ΓSpecIso (CommRingCat.of k)).hom).hom t))
      = ((affineSpaceFinToSpec k m).appTop).hom t := by
    rw [← mvPolynomialIsoGlobalSectionsAffineSpace_hom_apply k m, mvPolynomialIsoGlobalSectionsAffineSpace_hom_C, iso_inv_hom_apply]
  rw [← ha]
  exact EtaleChart.coordRingHom_C d _

private def constToCoordRelationQuotient (B : BlowupChart π c S s) :
    Γ(X, U) →+*
      (MvPolynomial (ULift.{u} (Fin m)) Γ(X, U) ⧸ Ideal.span (Set.range B.coordRelation)) :=
  (Ideal.Quotient.mk (Ideal.span (Set.range B.coordRelation))).comp MvPolynomial.C

private theorem constToCoordRelationQuotient_apply (B : BlowupChart π c S s) (y : Γ(X, U)) :
    constToCoordRelationQuotient B y = Ideal.Quotient.mk (Ideal.span (Set.range B.coordRelation)) (MvPolynomial.C y) := rfl

private theorem coordEvalQuotientHom_constToCoordRelationQuotient (B : BlowupChart π c S s) (y : Γ(X, U)) :
    B.coordEvalQuotientHom (constToCoordRelationQuotient B y) = (π.appLE U B.domain B.domain_le).hom y := by
  rw [constToCoordRelationQuotient_apply, coordEvalQuotientHom_mk, coordEvalHom_C]

private def affineSectionsToCoordRelationQuotient (B : BlowupChart π c S s) :
    Γ(affineSpaceFin k m, ⊤) ⟶
      CommRingCat.of
        (MvPolynomial (ULift.{u} (Fin m)) Γ(X, U) ⧸ Ideal.span (Set.range B.coordRelation)) :=
  CommRingCat.ofHom
    ((MvPolynomial.eval₂Hom ((constToCoordRelationQuotient B).comp (sectionsAlgebraMap k p U))
        (fun i : ULift.{u} (Fin m) =>
          Ideal.Quotient.mk (Ideal.span (Set.range B.coordRelation)) (MvPolynomial.X i))).comp
      (mvPolynomialIsoGlobalSectionsAffineSpace k m).inv.hom)

private def openSectionsToCoordRelationQuotient (B : BlowupChart π c S s) :
    Γ(U.toScheme, ⊤) ⟶
      CommRingCat.of
        (MvPolynomial (ULift.{u} (Fin m)) Γ(X, U) ⧸ Ideal.span (Set.range B.coordRelation)) :=
  CommRingCat.ofHom ((constToCoordRelationQuotient B).comp (U.topIso.hom.hom))

private theorem openSectionsToCoordRelationQuotient_apply (B : BlowupChart π c S s) (y : Γ(U.toScheme, ⊤)) :
    (openSectionsToCoordRelationQuotient B).hom y
      = Ideal.Quotient.mk (Ideal.span (Set.range B.coordRelation))
        (MvPolynomial.C (U.topIso.hom.hom y)) := rfl

private theorem affineSectionsToCoordRelationQuotient_coord (B : BlowupChart π c S s) (j : Fin m) :
    (affineSectionsToCoordRelationQuotient B).hom
        (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up j : ULift.{u} (Fin m)))
      = Ideal.Quotient.mk (Ideal.span (Set.range B.coordRelation))
        (MvPolynomial.X (ULift.up j : ULift.{u} (Fin m))) := by
  have h : (mvPolynomialIsoGlobalSectionsAffineSpace k m).inv.hom
      (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up j : ULift.{u} (Fin m)))
      = MvPolynomial.X (ULift.up j : ULift.{u} (Fin m)) := by
    rw [← mvPolynomialIsoGlobalSectionsAffineSpace_hom_X k m (ULift.up j : ULift.{u} (Fin m)), iso_inv_hom_apply]
  have h2 : (affineSectionsToCoordRelationQuotient B).hom
        (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up j : ULift.{u} (Fin m)))
      = (MvPolynomial.eval₂Hom ((constToCoordRelationQuotient B).comp (sectionsAlgebraMap k p U))
          (fun i : ULift.{u} (Fin m) =>
            Ideal.Quotient.mk (Ideal.span (Set.range B.coordRelation)) (MvPolynomial.X i)))
        ((mvPolynomialIsoGlobalSectionsAffineSpace k m).inv.hom
          (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up j : ULift.{u} (Fin m)))) := rfl
  rw [h2, h, MvPolynomial.eval₂Hom_X']

private theorem affineSectionsToCoordRelationQuotient_affineSpaceFinToSpec (B : BlowupChart π c S s)
    (t : Γ(Spec (CommRingCat.of k), ⊤)) :
    (affineSectionsToCoordRelationQuotient B).hom (((affineSpaceFinToSpec k m).appTop).hom t)
      = constToCoordRelationQuotient B (sectionsAlgebraMap k p U
          (((Scheme.ΓSpecIso (CommRingCat.of k)).hom).hom t)) := by
  have ha : (mvPolynomialIsoGlobalSectionsAffineSpace k m).hom.hom
      (MvPolynomial.C (((Scheme.ΓSpecIso (CommRingCat.of k)).hom).hom t))
      = ((affineSpaceFinToSpec k m).appTop).hom t := by
    rw [mvPolynomialIsoGlobalSectionsAffineSpace_hom_C, iso_inv_hom_apply]
  have h : (mvPolynomialIsoGlobalSectionsAffineSpace k m).inv.hom (((affineSpaceFinToSpec k m).appTop).hom t)
      = MvPolynomial.C (((Scheme.ΓSpecIso (CommRingCat.of k)).hom).hom t) := by
    rw [← ha, iso_inv_hom_apply]
  have h2 : (affineSectionsToCoordRelationQuotient B).hom (((affineSpaceFinToSpec k m).appTop).hom t)
      = (MvPolynomial.eval₂Hom ((constToCoordRelationQuotient B).comp (sectionsAlgebraMap k p U))
          (fun i : ULift.{u} (Fin m) =>
            Ideal.Quotient.mk (Ideal.span (Set.range B.coordRelation)) (MvPolynomial.X i)))
        ((mvPolynomialIsoGlobalSectionsAffineSpace k m).inv.hom (((affineSpaceFinToSpec k m).appTop).hom t)) := rfl
  rw [h2, h, MvPolynomial.eval₂Hom_C]
  rfl

private theorem openSectionsToCoordRelationQuotient_coord (B : BlowupChart π c S s) (j : Fin m) :
    (openSectionsToCoordRelationQuotient B).hom
        ((c.map.appTop).hom
          (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up j : ULift.{u} (Fin m))))
      = Ideal.Quotient.mk (Ideal.span (Set.range B.coordRelation))
        (MvPolynomial.C (c.coord j)) := by
  rw [openSectionsToCoordRelationQuotient_apply, ← EtaleChart.coord_def c j]

private theorem mk_eq_mk_C_coord (B : BlowupChart π c S s) (j : Fin m) :
    Ideal.Quotient.mk (Ideal.span (Set.range B.coordRelation))
        ((if j ∈ S ∧ j ≠ s then
            MvPolynomial.X (ULift.up j : ULift.{u} (Fin m)) *
              MvPolynomial.X (ULift.up s : ULift.{u} (Fin m))
          else MvPolynomial.X (ULift.up j : ULift.{u} (Fin m))) :
            MvPolynomial (ULift.{u} (Fin m)) Γ(X, U))
      = Ideal.Quotient.mk (Ideal.span (Set.range B.coordRelation))
        (MvPolynomial.C (c.coord j)) := by
  have h : Ideal.Quotient.mk (Ideal.span (Set.range B.coordRelation)) (B.coordRelation j) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨j, rfl⟩)
  rw [coordRelation_def, map_sub, sub_eq_zero] at h
  exact h

private theorem appTop_comp_affineSectionsToCoordRelationQuotient (B : BlowupChart π c S s) :
    (coordBlowupSubstMap k m S s).appTop ≫ affineSectionsToCoordRelationQuotient B = c.map.appTop ≫ openSectionsToCoordRelationQuotient B := by
  refine affineSpaceFin_globalSections_hom_ext k m _ _ (fun t => ?_) (fun j => ?_)
  · rw [comp_hom_apply, comp_hom_apply, coordBlowupSubstMap_appTop_affineSpaceFinToSpec,
      affineSectionsToCoordRelationQuotient_affineSpaceFinToSpec, openSectionsToCoordRelationQuotient_apply, etaleChart_appTop_affineSpaceFinToSpec_apply c t]
    rfl
  · rw [comp_hom_apply, comp_hom_apply, openSectionsToCoordRelationQuotient_coord]
    by_cases hjS : j ∈ S
    · by_cases hjs : j = s
      · subst hjs
        rw [coordBlowupSubstMap_appTop_coord_self, affineSectionsToCoordRelationQuotient_coord]
        have hrel := mk_eq_mk_C_coord B j
        rw [if_neg (by simp)] at hrel
        exact hrel
      · rw [coordBlowupSubstMap_appTop_coord_of_mem k m S s j hjS hjs, map_mul, affineSectionsToCoordRelationQuotient_coord,
          affineSectionsToCoordRelationQuotient_coord, ← map_mul]
        have hrel := mk_eq_mk_C_coord B j
        rw [if_pos ⟨hjS, hjs⟩] at hrel
        exact hrel
    · rw [coordBlowupSubstMap_appTop_coord_of_notMem k m S s j hjS, affineSectionsToCoordRelationQuotient_coord]
      have hrel := mk_eq_mk_C_coord B j
      rw [if_neg (by tauto)] at hrel
      exact hrel

private theorem bijective_coordEvalQuotientHom_of_isPullback (B : BlowupChart π c S s)
    (hU : IsAffineOpen U)
    (hB : IsPullback B.chart.map (π.resLE U B.domain B.domain_le) (coordBlowupSubstMap k m S s) c.map) :
    Function.Bijective B.coordEvalQuotientHom := by
  have hUaff : IsAffine U.toScheme := hU
  have hPaff : IsAffine (CategoryTheory.Limits.pullback (coordBlowupSubstMap k m S s) c.map) :=
    inferInstance
  have hDaff : IsAffine B.domain.toScheme := IsAffine.of_isIso hB.isoPullback.hom
  have HP : IsPushout (coordBlowupSubstMap k m S s).appTop c.map.appTop B.chart.map.appTop
      (π.resLE U B.domain B.domain_le).appTop :=
    AlgebraicGeometry.isPushout_appTop_of_isPullback hB
  obtain ⟨Δ, hinl, hinr⟩ :
      ∃ Δ : Γ(B.domain.toScheme, ⊤) ⟶
          CommRingCat.of
            (MvPolynomial (ULift.{u} (Fin m)) Γ(X, U) ⧸ Ideal.span (Set.range B.coordRelation)),
        B.chart.map.appTop ≫ Δ = affineSectionsToCoordRelationQuotient B ∧
          (π.resLE U B.domain B.domain_le).appTop ≫ Δ = openSectionsToCoordRelationQuotient B :=
    ⟨HP.desc (affineSectionsToCoordRelationQuotient B) (openSectionsToCoordRelationQuotient B) (appTop_comp_affineSectionsToCoordRelationQuotient B),
      HP.inl_desc _ _ _, HP.inr_desc _ _ _⟩
  have hinl' : ∀ z, Δ.hom ((B.chart.map.appTop).hom z) = (affineSectionsToCoordRelationQuotient B).hom z := by
    intro z
    have h := congrArg (fun φ => CommRingCat.Hom.hom φ z) hinl
    rw [comp_hom_apply] at h
    exact h
  have hinr' : ∀ y, Δ.hom (((π.resLE U B.domain B.domain_le).appTop).hom y)
      = (openSectionsToCoordRelationQuotient B).hom y := by
    intro y
    have h := congrArg (fun φ => CommRingCat.Hom.hom φ y) hinr
    rw [comp_hom_apply] at h
    exact h
  have hbeta : Δ ≫ CommRingCat.ofHom B.coordEvalQuotientHom = B.domain.topIso.hom := by
    refine HP.hom_ext ?_ ?_
    · rw [← Category.assoc, hinl]
      refine affineSpaceFin_globalSections_hom_ext k m _ _ (fun t => ?_) (fun j => ?_)
      · rw [comp_hom_apply, comp_hom_apply, affineSectionsToCoordRelationQuotient_affineSpaceFinToSpec,
          ← etaleChart_appTop_affineSpaceFinToSpec_apply c t, CommRingCat.hom_ofHom, coordEvalQuotientHom_constToCoordRelationQuotient,
          appLE_topIso_hom_apply π U B.domain B.domain_le,
          ← chart_appTop_coordBlowupSubstMap_apply B (((affineSpaceFinToSpec k m).appTop).hom t),
          coordBlowupSubstMap_appTop_affineSpaceFinToSpec]
      · rw [comp_hom_apply, comp_hom_apply, affineSectionsToCoordRelationQuotient_coord,
          CommRingCat.hom_ofHom, coordEvalQuotientHom_mk, coordEvalHom_X, EtaleChart.coord_def B.chart j]
    · rw [← Category.assoc, hinr]
      refine CommRingCat.hom_ext (RingHom.ext fun y => ?_)
      rw [comp_hom_apply, comp_hom_apply, CommRingCat.hom_ofHom,
        openSectionsToCoordRelationQuotient_apply, coordEvalQuotientHom_mk, coordEvalHom_C,
        appLE_topIso_hom_apply π U B.domain B.domain_le]
  have hbeta' : ∀ z, B.coordEvalQuotientHom (Δ.hom z) = B.domain.topIso.hom.hom z := by
    intro z
    have h := congrArg (fun φ => CommRingCat.Hom.hom φ z) hbeta
    rw [comp_hom_apply] at h
    exact h
  have hring : (Δ.hom).comp ((B.domain.topIso.inv.hom).comp B.coordEvalQuotientHom)
      = RingHom.id _ := by
    refine Ideal.Quotient.ringHom_ext ?_
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)
    · simp only [RingHom.comp_apply, RingHom.id_apply]
      rw [coordEvalQuotientHom_mk, coordEvalHom_C, topIso_inv_appLE_apply, hinr', openSectionsToCoordRelationQuotient_apply,
        iso_hom_inv_apply]
    · obtain ⟨j⟩ := i
      simp only [RingHom.comp_apply, RingHom.id_apply]
      rw [coordEvalQuotientHom_mk, coordEvalHom_X, EtaleChart.coord_def B.chart j, iso_inv_hom_apply,
        hinl', affineSectionsToCoordRelationQuotient_coord]
  have halpha : ∀ q, Δ.hom (B.domain.topIso.inv.hom (B.coordEvalQuotientHom q)) = q := by
    intro q
    have h := RingHom.congr_fun hring q
    simpa only [RingHom.comp_apply, RingHom.id_apply] using h
  refine ⟨fun x y hxy => ?_, fun y => ⟨Δ.hom (B.domain.topIso.inv.hom y), ?_⟩⟩
  · rw [← halpha x, ← halpha y, hxy]
  · rw [hbeta', iso_hom_inv_apply]

theorem surjective_coordEvalHom (B : BlowupChart π c S s) (hU : IsAffineOpen U)
    (hB : IsPullback B.chart.map (π.resLE U B.domain B.domain_le) (coordBlowupSubstMap k m S s) c.map) :
    Function.Surjective B.coordEvalHom := by
  intro y
  obtain ⟨q, hq⟩ := (bijective_coordEvalQuotientHom_of_isPullback B hU hB).2 y
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
  exact ⟨a, hq⟩

theorem bijective_coordEvalQuotientHom (B : BlowupChart π c S s) (hU : IsAffineOpen U)
    (hB : IsPullback B.chart.map (π.resLE U B.domain B.domain_le) (coordBlowupSubstMap k m S s) c.map) :
    Function.Bijective B.coordEvalQuotientHom :=
  bijective_coordEvalQuotientHom_of_isPullback B hU hB

end BlowupChart

end FunctorialResolution.EmbeddedResolution

end
