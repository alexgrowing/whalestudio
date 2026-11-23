import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

abbrev affineSpaceCoord (k : Type u) [Field k] (m : ℕ) (j : Fin m) :=
  AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up j : ULift.{u} (Fin m))

section

variable {X : Scheme.{u}} {k : Type u} [Field k] {q : X ⟶ Spec (CommRingCat.of k)}
  {U : X.Opens} {m : ℕ}

@[reducible] def EtaleChart.coordTop (c : EtaleChart q U m) (j : Fin m) :
    U.toScheme.presheaf.obj (op ⊤) :=
  c.map.appTop.hom (affineSpaceCoord k m j)

end

def pointOfMem {P : Scheme.{u}} (V : P.Opens) (p : ↥P) (hp : p ∈ V) : ↥(V.toScheme) :=
  ⟨p, hp⟩

def specResidueFieldPoint {X : Scheme.{u}} (x : ↥X) : ↥(Spec (X.residueField x)) :=
  (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (X.residueField x))

section

variable {P : Scheme.{u}} {k : Type u} [Field k] {q : P ⟶ Spec (CommRingCat.of k)}
  {V : P.Opens} {n : ℕ}

abbrev chartPullback (c₁ c₂ : EtaleChart q V n) : Scheme.{u} := pullback c₁.map c₂.map

abbrev chartPullbackFst (c₁ c₂ : EtaleChart q V n) : chartPullback c₁ c₂ ⟶ P :=
  pullback.fst c₁.map c₂.map ≫ V.ι

abbrev chartPullbackSnd (c₁ c₂ : EtaleChart q V n) : chartPullback c₁ c₂ ⟶ P :=
  pullback.snd c₁.map c₂.map ≫ V.ι

theorem etale_pullback_fst_map (c₁ c₂ : EtaleChart q V n) :
    AlgebraicGeometry.Etale (pullback.fst c₁.map c₂.map) := by
  have : AlgebraicGeometry.Etale c₂.map := c₂.isEtale
  infer_instance

instance instEtalePullbackFstChart (c₁ c₂ : EtaleChart q V n) :
    AlgebraicGeometry.Etale (pullback.fst c₁.map c₂.map) :=
  etale_pullback_fst_map c₁ c₂

theorem etale_pullback_snd_map (c₁ c₂ : EtaleChart q V n) :
    AlgebraicGeometry.Etale (pullback.snd c₁.map c₂.map) := by
  have h1 : AlgebraicGeometry.Etale c₁.map := c₁.isEtale
  have h2 : AlgebraicGeometry.Etale c₂.map := c₂.isEtale
  exact inferInstance

instance instEtalePullbackSndChart (c₁ c₂ : EtaleChart q V n) :
    AlgebraicGeometry.Etale (pullback.snd c₁.map c₂.map) :=
  etale_pullback_snd_map c₁ c₂

private theorem etale_comp {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (hf : AlgebraicGeometry.Etale f) (hg : AlgebraicGeometry.Etale g) :
    AlgebraicGeometry.Etale (f ≫ g) := by
  have := hf
  have := hg
  infer_instance

theorem etale_chartPullbackFst (c₁ c₂ : EtaleChart q V n) :
    AlgebraicGeometry.Etale (chartPullbackFst c₁ c₂) := by
  have h₁ : AlgebraicGeometry.Etale (pullback.fst c₁.map c₂.map) :=
    etale_pullback_fst_map c₁ c₂
  have h₂ : AlgebraicGeometry.Etale V.ι := inferInstance
  show AlgebraicGeometry.Etale (pullback.fst c₁.map c₂.map ≫ V.ι)
  exact etale_comp _ _ h₁ h₂

instance instEtaleChartPairFst (c₁ c₂ : EtaleChart q V n) :
    AlgebraicGeometry.Etale (chartPullbackFst c₁ c₂) :=
  etale_chartPullbackFst c₁ c₂

theorem etale_chartPullbackSnd (c₁ c₂ : EtaleChart q V n) :
    AlgebraicGeometry.Etale (chartPullbackSnd c₁ c₂) := by
  have h₁ : AlgebraicGeometry.Etale (pullback.snd c₁.map c₂.map) :=
    etale_pullback_snd_map c₁ c₂
  have h₂ : AlgebraicGeometry.Etale V.ι := inferInstance
  show AlgebraicGeometry.Etale (pullback.snd c₁.map c₂.map ≫ V.ι)
  exact etale_comp _ _ h₁ h₂

instance instEtaleChartPairSnd (c₁ c₂ : EtaleChart q V n) :
    AlgebraicGeometry.Etale (chartPullbackSnd c₁ c₂) :=
  etale_chartPullbackSnd c₁ c₂

private theorem appTop_comp_apply {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (x : C.presheaf.obj (op ⊤)) :
    (f ≫ g).appTop.hom x = f.appTop.hom (g.appTop.hom x) := rfl

theorem chartPullback_coordTop_eq (c₁ c₂ : EtaleChart q V n) (j : Fin n) :
    (pullback.fst c₁.map c₂.map).appTop.hom (c₁.coordTop j) =
      (pullback.snd c₁.map c₂.map).appTop.hom (c₂.coordTop j) := by
  have h : (pullback.fst c₁.map c₂.map ≫ c₁.map).appTop.hom (affineSpaceCoord k n j)
      = (pullback.snd c₁.map c₂.map ≫ c₂.map).appTop.hom (affineSpaceCoord k n j) := by
    rw [pullback.condition]
  rw [appTop_comp_apply, appTop_comp_apply] at h
  exact h

theorem chartPullbackFst_comp_eq_chartPullbackSnd_comp (c₁ c₂ : EtaleChart q V n) :
    chartPullbackFst c₁ c₂ ≫ q = chartPullbackSnd c₁ c₂ ≫ q := by
  have h : (pullback.fst c₁.map c₂.map ≫ c₁.map) ≫ affineSpaceFinToSpec k n
      = (pullback.snd c₁.map c₂.map ≫ c₂.map) ≫ affineSpaceFinToSpec k n := by
    rw [pullback.condition]
  rw [Category.assoc, Category.assoc] at h
  rw [c₁.comp_struct, c₂.comp_struct] at h
  simpa only [Category.assoc] using h

theorem chartPullback_comap_coordIdeal_eq (c₁ c₂ : EtaleChart q V n) (S : Finset (Fin n)) :
    (c₁.coordIdeal S).comap (pullback.fst c₁.map c₂.map) =
      (c₂.coordIdeal S).comap (pullback.snd c₁.map c₂.map) := by
  rw [c₁.coordIdeal_eq_comap_coordSubspaceIdeal S, c₂.coordIdeal_eq_comap_coordSubspaceIdeal S, ← Scheme.IdealSheafData.comap_comp,
    ← Scheme.IdealSheafData.comap_comp, pullback.condition]

abbrev ChartsAgreeAt (c₁ c₂ : EtaleChart q V n) (p : ↥P) (hp : p ∈ V) : Prop :=
  V.toScheme.fromSpecResidueField (pointOfMem V p hp) ≫ c₁.map =
    V.toScheme.fromSpecResidueField (pointOfMem V p hp) ≫ c₂.map

def chartPullbackLift (c₁ c₂ : EtaleChart q V n) (p : ↥P) (hp : p ∈ V)
    (h : ChartsAgreeAt c₁ c₂ p hp) :
    Spec (V.toScheme.residueField (pointOfMem V p hp)) ⟶ chartPullback c₁ c₂ :=
  pullback.lift (V.toScheme.fromSpecResidueField (pointOfMem V p hp))
    (V.toScheme.fromSpecResidueField (pointOfMem V p hp)) h

@[simp] theorem chartPullbackLift_fst (c₁ c₂ : EtaleChart q V n) (p : ↥P) (hp : p ∈ V)
    (h : ChartsAgreeAt c₁ c₂ p hp) :
    chartPullbackLift c₁ c₂ p hp h ≫ pullback.fst c₁.map c₂.map =
      V.toScheme.fromSpecResidueField (pointOfMem V p hp) :=
  pullback.lift_fst _ _ _

@[simp] theorem chartPullbackLift_snd (c₁ c₂ : EtaleChart q V n) (p : ↥P) (hp : p ∈ V)
    (h : ChartsAgreeAt c₁ c₂ p hp) :
    chartPullbackLift c₁ c₂ p hp h ≫ pullback.snd c₁.map c₂.map =
      V.toScheme.fromSpecResidueField (pointOfMem V p hp) :=
  pullback.lift_snd _ _ _

@[simp] theorem chartPullbackLift_fst_assoc {W : Scheme.{u}} (c₁ c₂ : EtaleChart q V n) (p : ↥P)
    (hp : p ∈ V) (h : ChartsAgreeAt c₁ c₂ p hp) (g : V.toScheme ⟶ W) :
    chartPullbackLift c₁ c₂ p hp h ≫ pullback.fst c₁.map c₂.map ≫ g =
      V.toScheme.fromSpecResidueField (pointOfMem V p hp) ≫ g := by
  rw [← Category.assoc, chartPullbackLift_fst]

@[simp] theorem chartPullbackLift_snd_assoc {W : Scheme.{u}} (c₁ c₂ : EtaleChart q V n) (p : ↥P)
    (hp : p ∈ V) (h : ChartsAgreeAt c₁ c₂ p hp) (g : V.toScheme ⟶ W) :
    chartPullbackLift c₁ c₂ p hp h ≫ pullback.snd c₁.map c₂.map ≫ g =
      V.toScheme.fromSpecResidueField (pointOfMem V p hp) ≫ g := by
  rw [← Category.assoc, chartPullbackLift_snd]

def chartPullbackPoint (c₁ c₂ : EtaleChart q V n) (p : ↥P) (hp : p ∈ V)
    (h : ChartsAgreeAt c₁ c₂ p hp) : ↥(chartPullback c₁ c₂) :=
  (chartPullbackLift c₁ c₂ p hp h).base (specResidueFieldPoint (pointOfMem V p hp))

theorem chartPullbackFst_base_chartPullbackPoint (c₁ c₂ : EtaleChart q V n) (p : ↥P) (hp : p ∈ V)
    (h : ChartsAgreeAt c₁ c₂ p hp) :
    (chartPullbackFst c₁ c₂).base (chartPullbackPoint c₁ c₂ p hp h) = p := by
  have hfs : (V.toScheme.fromSpecResidueField (pointOfMem V p hp)).base
      (specResidueFieldPoint (pointOfMem V p hp)) = pointOfMem V p hp := by
    simp
  have e : (chartPullbackLift c₁ c₂ p hp h ≫ pullback.fst c₁.map c₂.map).base
      (specResidueFieldPoint (pointOfMem V p hp)) = pointOfMem V p hp := by
    rw [chartPullbackLift_fst]
    exact hfs
  have key : (pullback.fst c₁.map c₂.map).base (chartPullbackPoint c₁ c₂ p hp h)
      = pointOfMem V p hp := e
  have key2 : V.ι.base ((pullback.fst c₁.map c₂.map).base (chartPullbackPoint c₁ c₂ p hp h))
      = V.ι.base (pointOfMem V p hp) := by rw [key]
  exact key2

private theorem comp_base_apply {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (x : ↥A) : (f ≫ g).base x = g.base (f.base x) := rfl

theorem chartPullbackSnd_base_chartPullbackPoint (c₁ c₂ : EtaleChart q V n) (p : ↥P) (hp : p ∈ V)
    (h : ChartsAgreeAt c₁ c₂ p hp) :
    (chartPullbackSnd c₁ c₂).base (chartPullbackPoint c₁ c₂ p hp h) = p := by
  have key := chartPullbackLift_snd_assoc c₁ c₂ p hp h V.ι
  have e1 : (V.toScheme.fromSpecResidueField (pointOfMem V p hp)).base
      (specResidueFieldPoint (pointOfMem V p hp)) = pointOfMem V p hp := by
    simp
  have e2 : V.ι.base (pointOfMem V p hp) = p := rfl
  have hA := comp_base_apply (chartPullbackLift c₁ c₂ p hp h)
      (pullback.snd c₁.map c₂.map ≫ V.ι) (specResidueFieldPoint (pointOfMem V p hp))
  have hB := comp_base_apply
      (V.toScheme.fromSpecResidueField (pointOfMem V p hp)) V.ι
      (specResidueFieldPoint (pointOfMem V p hp))
  have h3 : (chartPullbackLift c₁ c₂ p hp h ≫ pullback.snd c₁.map c₂.map ≫ V.ι).base
        (specResidueFieldPoint (pointOfMem V p hp))
      = (V.toScheme.fromSpecResidueField (pointOfMem V p hp) ≫ V.ι).base
        (specResidueFieldPoint (pointOfMem V p hp)) := by
    rw [key]
  exact hA.symm.trans (h3.trans (hB.trans ((congrArg (fun z => V.ι.base z) e1).trans e2)))

private theorem affineSpaceFin_hom_ext {K : Type u} [Field K] {m : ℕ} {Z : Scheme.{u}}
    (f g : Z ⟶ affineSpaceFin K m)
    (h₁ : f ≫ affineSpaceFinToSpec K m = g ≫ affineSpaceFinToSpec K m)
    (h₂ : ∀ i : ULift.{u} (Fin m),
      f.appTop.hom (AffineSpace.coord (Spec (CommRingCat.of K)) i) =
        g.appTop.hom (AffineSpace.coord (Spec (CommRingCat.of K)) i)) :
    f = g := by
  apply AffineSpace.hom_ext
  · exact h₁
  · exact h₂

private theorem not_isUnit_of_mem_maximalIdeal {R : Type u} [CommRing R] [IsLocalRing R] {a : R}
    (ha : a ∈ IsLocalRing.maximalIdeal R) : ¬ IsUnit a :=
  (IsLocalRing.mem_maximalIdeal a).mp ha

private theorem specResidueField_eq_zero_of_not_isUnit {X : Scheme.{u}} (x : ↥X)
    (t : Γ(Spec (X.residueField x), ⊤)) (ht : ¬ IsUnit t) : t = 0 := by
  have h2 : (Scheme.ΓSpecIso (X.residueField x)).inv.hom
      ((Scheme.ΓSpecIso (X.residueField x)).hom.hom t) = t := by
    have e1 := congrArg CommRingCat.Hom.hom
      (Iso.hom_inv_id (Scheme.ΓSpecIso (X.residueField x)))
    rw [CommRingCat.hom_comp, CommRingCat.hom_id] at e1
    exact DFunLike.congr_fun e1 t
  by_contra hne
  have hne0 : (Scheme.ΓSpecIso (X.residueField x)).hom.hom t ≠ 0 := by
    intro h0
    apply hne
    rw [← h2, h0]
    exact map_zero _
  have hu : IsUnit ((Scheme.ΓSpecIso (X.residueField x)).hom.hom t) :=
    isUnit_iff_ne_zero.mpr hne0
  have hu2 : IsUnit ((Scheme.ΓSpecIso (X.residueField x)).inv.hom
      ((Scheme.ΓSpecIso (X.residueField x)).hom.hom t)) :=
    hu.map (Scheme.ΓSpecIso (X.residueField x)).inv.hom
  rw [h2] at hu2
  exact ht hu2

private theorem fromSpecResidueField_appTop_eq_zero {X : Scheme.{u}} (x : ↥X)
    (hx : x ∈ (⊤ : X.Opens)) (s : Γ(X, ⊤))
    (hs : (X.presheaf.germ ⊤ x hx).hom s ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x)) :
    (X.fromSpecResidueField x).appTop.hom s = 0 := by
  have hxb : x ∉ X.basicOpen s := fun hmem =>
    not_isUnit_of_mem_maximalIdeal hs ((X.mem_basicOpen_top s x).1 hmem)
  have hy : (X.fromSpecResidueField x).base (specResidueFieldPoint x) = x := by simp
  have hynot : specResidueFieldPoint x ∉ (Spec (X.residueField x)).basicOpen
      ((X.fromSpecResidueField x).appTop.hom s) := by
    intro hmem
    have h1 : specResidueFieldPoint x ∈ (X.fromSpecResidueField x) ⁻¹ᵁ (X.basicOpen s) := by
      rw [Scheme.preimage_basicOpen]
      exact hmem
    have h2 : (X.fromSpecResidueField x).base (specResidueFieldPoint x) ∈ X.basicOpen s := h1
    rw [hy] at h2
    exact hxb h2
  have hnu : ¬ IsUnit ((X.fromSpecResidueField x).appTop.hom s) := by
    intro hu
    apply hynot
    rw [Scheme.mem_basicOpen_top]
    exact hu.map
      ((Spec (X.residueField x)).presheaf.germ ⊤ (specResidueFieldPoint x) (by trivial)).hom
  exact specResidueField_eq_zero_of_not_isUnit x _ hnu

theorem chartsAgreeAt_of_germ_sub_mem_maximalIdeal (c₁ c₂ : EtaleChart q V n) (p : ↥P)
    (hp : p ∈ V)
    (h : ∀ j : Fin n,
      (V.toScheme.presheaf.germ ⊤ (pointOfMem V p hp) (by trivial)).hom
          (c₁.coordTop j - c₂.coordTop j) ∈
        IsLocalRing.maximalIdeal (V.toScheme.presheaf.stalk (pointOfMem V p hp))) :
    ChartsAgreeAt c₁ c₂ p hp := by
  have hover : (V.toScheme.fromSpecResidueField (pointOfMem V p hp) ≫ c₁.map) ≫
        affineSpaceFinToSpec k n =
      (V.toScheme.fromSpecResidueField (pointOfMem V p hp) ≫ c₂.map) ≫
        affineSpaceFinToSpec k n := by
    rw [Category.assoc, Category.assoc, c₁.comp_struct, c₂.comp_struct]
  refine affineSpaceFin_hom_ext _ _ hover ?_
  rintro ⟨j⟩
  have h0 := fromSpecResidueField_appTop_eq_zero (pointOfMem V p hp) (by trivial)
    (c₁.coordTop j - c₂.coordTop j) (h j)
  rw [map_sub, sub_eq_zero] at h0
  rw [appTop_comp_apply, appTop_comp_apply]
  exact h0

end

section

variable {P : Scheme.{u}} {k : Type u} [Field k] {q : P ⟶ Spec (CommRingCat.of k)}
  {V : P.Opens} {n : ℕ}

def chartPullbackFstStalkMap (c₁ c₂ : EtaleChart q V n) (p : ↥P) (hp : p ∈ V)
    (h : ChartsAgreeAt c₁ c₂ p hp) :
    P.presheaf.stalk p ⟶ (chartPullback c₁ c₂).presheaf.stalk (chartPullbackPoint c₁ c₂ p hp h) :=
  eqToHom (congrArg (fun y : ↥P => P.presheaf.stalk y)
      (chartPullbackFst_base_chartPullbackPoint c₁ c₂ p hp h).symm) ≫
    (chartPullbackFst c₁ c₂).stalkMap (chartPullbackPoint c₁ c₂ p hp h)

def chartPullbackSndStalkMap (c₁ c₂ : EtaleChart q V n) (p : ↥P) (hp : p ∈ V)
    (h : ChartsAgreeAt c₁ c₂ p hp) :
    P.presheaf.stalk p ⟶ (chartPullback c₁ c₂).presheaf.stalk (chartPullbackPoint c₁ c₂ p hp h) :=
  eqToHom (congrArg (fun y : ↥P => P.presheaf.stalk y)
      (chartPullbackSnd_base_chartPullbackPoint c₁ c₂ p hp h).symm) ≫
    (chartPullbackSnd c₁ c₂).stalkMap (chartPullbackPoint c₁ c₂ p hp h)

theorem chartPullbackFstStalkMap_eq (c₁ c₂ : EtaleChart q V n) (p : ↥P) (hp : p ∈ V)
    (h : ChartsAgreeAt c₁ c₂ p hp) :
    chartPullbackFstStalkMap c₁ c₂ p hp h =
      eqToHom (congrArg (fun y : ↥P => P.presheaf.stalk y)
          (chartPullbackFst_base_chartPullbackPoint c₁ c₂ p hp h).symm) ≫
        (chartPullbackFst c₁ c₂).stalkMap (chartPullbackPoint c₁ c₂ p hp h) := rfl

theorem chartPullbackSndStalkMap_eq (c₁ c₂ : EtaleChart q V n) (p : ↥P) (hp : p ∈ V)
    (h : ChartsAgreeAt c₁ c₂ p hp) :
    chartPullbackSndStalkMap c₁ c₂ p hp h =
      eqToHom (congrArg (fun y : ↥P => P.presheaf.stalk y)
          (chartPullbackSnd_base_chartPullbackPoint c₁ c₂ p hp h).symm) ≫
        (chartPullbackSnd c₁ c₂).stalkMap (chartPullbackPoint c₁ c₂ p hp h) := rfl

end

end FunctorialResolution.EmbeddedResolution
