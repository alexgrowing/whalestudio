import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HermitianLattice
import GroundTheory.HeightsAndTheta.Heights.ComplexMetrics.Statements
import GroundTheory.HeightsAndTheta.Heights.ComplexPointsBase
import GroundTheory.HeightsAndTheta.Heights.FubiniStudy
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.PSpaceFinite
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace MonoidalCategory MeasureTheory
  NumberField NumberField.ComplexEmbedding TensorProduct GroundTheory.Arith.SchemeCoh ComplexAt
open scoped LinearAlgebra.Projectivization

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

structure NormedMetric (K : Type*) [Field K] [NumberField K] (E : Type*) [AddCommGroup E]
    [Module (𝓞 K) E] where

  norm : ∀ σ : K →+* ℂ, Fibre σ E → ℝ
  norm_add_le : ∀ (σ : K →+* ℂ) (x y : Fibre σ E), norm σ (x + y) ≤ norm σ x + norm σ y
  norm_smul : ∀ (σ : K →+* ℂ) (c : ℂ) (x : Fibre σ E), norm σ (c • x) = ‖c‖ * norm σ x
  eq_zero_of_norm_eq_zero : ∀ (σ : K →+* ℂ) (x : Fibre σ E), norm σ x = 0 → x = 0

  norm_conj : ∀ (σ : K →+* ℂ) (x : Fibre σ E), norm (conjugate σ) (conjMap σ E x) = norm σ x

structure NormedBundle.{v} (K : Type*) [Field K] [NumberField K] where

  carrier : Type v
  [instAddCommGroup : AddCommGroup carrier]
  [instModule : Module (𝓞 K) carrier]
  [instFinite : Module.Finite (𝓞 K) carrier]
  [instProjective : Module.Projective (𝓞 K) carrier]

  metric : NormedMetric K carrier

attribute [instance] NormedBundle.instAddCommGroup NormedBundle.instModule NormedBundle.instFinite
  NormedBundle.instProjective

section NormedExamples

variable (K : Type*) [Field K] [NumberField K]

def NormedMetric.integers : NormedMetric K (𝓞 K) where
  norm σ x := ‖integersCoord K σ x‖
  norm_add_le σ x y := by
    rw [(integersCoord K σ).map_add x y]; exact _root_.norm_add_le _ _
  norm_smul σ c x := by rw [LinearEquiv.map_smul, _root_.norm_smul]
  eq_zero_of_norm_eq_zero σ x h := (integersCoord K σ).map_eq_zero_iff.mp (norm_eq_zero.mp h)
  norm_conj σ x := by rw [integersCoord_conjMap, Complex.norm_conj]

def NormedBundle.integers : NormedBundle K := ⟨𝓞 K, NormedMetric.integers K⟩

theorem NormedMetric.integers_norm_one (σ : K →+* ℂ) :
    (NormedMetric.integers K).norm σ ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] (1 : 𝓞 K)) = 1 := by
  change ‖integersCoord K σ ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] (1 : 𝓞 K))‖ = 1
  rw [integersCoord_tmul]
  simp

example : NormedBundle ℚ := NormedBundle.integers ℚ

end NormedExamples

namespace ProjScheme

variable {A : Type u} [CommRing A] {N : ℕ} (X : ProjScheme A N)

def toBase : X.X ⟶ Spec (.of A) := X.ι ≫ ProjSpace.toSpecBase A N

def baseHom : A →+* ringOn X.X ⊤ :=
  (X.toBase.appTop).hom.comp (Scheme.ΓSpecIso (.of A)).inv.hom

def H0 (L : X.X.Modules) : Type u := ((preMod X.X).obj L).obj (op ⊤)

instance (L : X.X.Modules) : AddCommGroup (X.H0 L) :=
  inferInstanceAs (AddCommGroup (((preMod X.X).obj L).obj (op ⊤)))

instance (L : X.X.Modules) : Module (ringOn X.X ⊤) (X.H0 L) :=
  inferInstanceAs (Module (ringOn X.X ⊤) (((preMod X.X).obj L).obj (op ⊤)))

instance (L : X.X.Modules) : Module A (X.H0 L) := Module.compHom _ X.baseHom

theorem smul_globalSections_def (L : X.X.Modules) (a : A) (s : X.H0 L) : a • s = X.baseHom a • s := rfl

end ProjScheme

namespace ProjScheme

variable {A : Type u} [CommRing A] {N : ℕ}

attribute [local instance] algebraOfOver in

theorem evalStalkProj_base {ρ : A →+* ℂ} {w : Fin (N + 1) → ℂ} {x : projectiveSpace A N}
    (h : IsOver ρ w x) (a : A) :
    evalStalkProj h ((projectiveSpace A N).presheaf.germ ⊤ x trivial
      ((ProjSpace.toSpecBase A N).appTop ((Scheme.ΓSpecIso (.of A)).inv a))) = ρ a := by
  have : x.asHomogeneousIdeal.toIdeal.IsPrime := x.isPrime
  have hv := ProjSpace.projValue_algebraMap (n := N) a x
  have hC : (MvPolynomial.C a : MvPolynomial (Fin (N + 1)) A) ∈ ProjSpace.grading A N 0 :=
    (MvPolynomial.mem_homogeneousSubmodule _ _).mpr (MvPolynomial.isHomogeneous_C _ a)
  have h1 : (1 : MvPolynomial (Fin (N + 1)) A) ∈ ProjSpace.grading A N 0 := SetLike.GradedOne.one_mem
  let c : HomogeneousLocalization.NumDenSameDeg (ProjSpace.grading A N)
      x.asHomogeneousIdeal.toIdeal.primeCompl :=
    ⟨0, ⟨_, hC⟩, ⟨1, h1⟩, fun h0 ↦ (Ideal.ne_top_iff_one _).mp x.isPrime.ne_top h0⟩
  have hy : (Proj.stalkIso (ProjSpace.grading A N) x).hom.hom
      ((projectiveSpace A N).presheaf.germ ⊤ x trivial
        ((ProjSpace.toSpecBase A N).appTop ((Scheme.ΓSpecIso (.of A)).inv a))) =
      HomogeneousLocalization.mk c := by
    apply HomogeneousLocalization.val_injective
    rw [HomogeneousLocalization.val_mk]
    change (Proj.stalkIso' (ProjSpace.grading A N) x
      ((ProjectiveSpectrum.Proj.structureSheaf (ProjSpace.grading A N)).presheaf.germ ⊤ x trivial _)).val = _
    refine (congrArg HomogeneousLocalization.val
      (Proj.stalkIso'_germ (ProjSpace.grading A N) ⊤ x trivial _)).trans ?_
    refine hv.trans ?_
    rw [Localization.mk_eq_mk']
    exact (IsLocalization.mk'_one (M := x.asHomogeneousIdeal.toIdeal.primeCompl) _
      (MvPolynomial.C a)).symm
  change evalAtPrime h _ = _
  rw [hy]
  refine (evalAtPrime_mk h c).trans ?_
  simp [c, evalAt]

variable (X : ProjScheme A N)

theorem evalAtPoint_baseHom {ρ : A →+* ℂ} (x : X.complexPoints ρ) (a : A) :
    X.evalAtPoint x (germR (show X.point x ∈ (⊤ : X.X.Opens) from trivial) (X.baseHom a)) = ρ a := by
  have e := Scheme.Hom.germ_stalkMap_apply X.ι ⊤ (X.point x) trivial
    ((ProjSpace.toSpecBase A N).appTop ((Scheme.ΓSpecIso (.of A)).inv a))
  have e2 : germR (show X.point x ∈ (⊤ : X.X.Opens) from trivial) (X.baseHom a) =
      (X.ι.stalkMap (X.point x)).hom ((projectiveSpace A N).presheaf.germ ⊤ (X.ι.base (X.point x))
        trivial ((ProjSpace.toSpecBase A N).appTop ((Scheme.ΓSpecIso (.of A)).inv a))) := by
    rw [e]
    rfl
  rw [e2]
  change X.evalStalk (X.isOver_point x) _ = _
  rw [evalStalk_stalkMap]
  exact evalStalkProj_base _ a

end ProjScheme

namespace ProjScheme

variable {A : Type u} [CommRing A] {N : ℕ} (X : ProjScheme A N) (L : X.X.Modules)

def evalGlobalSection {ρ : A →+* ℂ} (x : X.complexPoints ρ) : X.H0 L →+ X.Fibre L x where
  toFun s := X.sectionValue x (show X.point x ∈ (⊤ : X.X.Opens) from trivial) s
  map_zero' := by
    change fibreMk L _ 1 (germM _ (0 : ((preMod X.X).obj L).obj (op ⊤))) = 0
    rw [germM_zero]
    exact TensorProduct.tmul_zero _ _
  map_add' s t := by
    change fibreMk L _ 1 (germM _ (s + t : ((preMod X.X).obj L).obj (op ⊤))) =
      fibreMk L _ 1 (germM _ (s : ((preMod X.X).obj L).obj (op ⊤))) +
        fibreMk L _ 1 (germM _ (t : ((preMod X.X).obj L).obj (op ⊤)))
    unfold germM
    refine (congrArg (fibreMk L _ 1) (map_add _ _ _)).trans ?_
    exact TensorProduct.tmul_add _ _ _

theorem evalGlobalSection_apply {ρ : A →+* ℂ} (x : X.complexPoints ρ) (s : X.H0 L) :
    X.evalGlobalSection L x s = X.sectionValue x (show X.point x ∈ (⊤ : X.X.Opens) from trivial) s := rfl

theorem evalGlobalSection_smul {ρ : A →+* ℂ} (x : X.complexPoints ρ) (a : A) (s : X.H0 L) :
    X.evalGlobalSection L x (a • s) = ρ a • X.evalGlobalSection L x s := by
  change fibreMk L _ 1 (germM _ (X.baseHom a • (s : ((preMod X.X).obj L).obj (op ⊤)))) =
    ρ a • fibreMk L _ 1 (germM _ (s : ((preMod X.X).obj L).obj (op ⊤)))
  erw [germM_smul]
  rw [complex_smul_def]
  unfold fibreMk
  rw [← TensorProduct.smul_tmul]
  erw [TensorProduct.smul_tmul']
  congr 1
  rw [Algebra.smul_def, Via.algebraMap_apply, smul_eq_mul, mul_one, mul_one]
  congr 1
  exact X.evalAtPoint_baseHom x a

end ProjScheme

namespace ProjScheme

variable {K : Type} [Field K] [NumberField K] {N : ℕ} (X : ProjScheme (𝓞 K) N) (L : X.X.Modules)

abbrev intEmb (σ : K →+* ℂ) : 𝓞 K →+* ℂ := σ.comp (algebraMap (𝓞 K) K)

omit [NumberField K] in

def evalPair (σ : K →+* ℂ) (x : X.complexPoints (intEmb σ)) :
    ComplexAt σ →+ X.H0 L →+ X.Fibre L x :=
  AddMonoidHom.mk'
    (fun z ↦ (DistribSMul.toAddMonoidHom (X.Fibre L x) ((ofComplex σ).symm z)).comp
      (X.evalGlobalSection L x))
    (fun z w ↦ by ext s; simp [add_smul])

omit [NumberField K] in
theorem evalPair_apply (σ : K →+* ℂ) (x : X.complexPoints (intEmb σ)) (z : ComplexAt σ)
    (s : X.H0 L) : X.evalPair L σ x z s = (ofComplex σ).symm z • X.evalGlobalSection L x s := rfl

omit [NumberField K] in

theorem evalPair_smul (σ : K →+* ℂ) (x : X.complexPoints (intEmb σ)) (a : 𝓞 K) (z : ComplexAt σ)
    (s : X.H0 L) : X.evalPair L σ x (a • z) s = X.evalPair L σ x z (a • s) := by
  rw [evalPair_apply, evalPair_apply, evalGlobalSection_smul, smul_smul, ComplexAt.smul_def, map_mul,
    AlgEquiv.symm_apply_apply, mul_comm]
  rfl

def evalFibre (σ : K →+* ℂ) (x : X.complexPoints (intEmb σ)) :
    Heights.Fibre σ (X.H0 L) →ₗ[ℂ] X.Fibre L x where
  toFun := liftAddHom (X.evalPair L σ x) (X.evalPair_smul L σ x)
  map_add' := map_add _
  map_smul' c t := by
    induction t using TensorProduct.induction_on with
    | zero => simp only [smul_zero, map_zero]
    | tmul z s =>
      rw [TensorProduct.smul_tmul', liftAddHom_tmul, liftAddHom_tmul, evalPair_apply,
        evalPair_apply, RingHom.id_apply, smul_smul, map_smul, smul_eq_mul]
    | add t₁ t₂ h₁ h₂ => simp only [smul_add, map_add, h₁, h₂]

omit [NumberField K] in
theorem evalFibre_tmul (σ : K →+* ℂ) (x : X.complexPoints (intEmb σ)) (z : ComplexAt σ)
    (s : X.H0 L) : X.evalFibre L σ x (z ⊗ₜ s) = (ofComplex σ).symm z • X.evalGlobalSection L x s := by
  change liftAddHom (X.evalPair L σ x) (X.evalPair_smul L σ x) (z ⊗ₜ[𝓞 K] s) = _
  rw [liftAddHom_tmul]
  rfl

variable (Lb : X.HermitianLineBundle)

def supNorm (σ : K →+* ℂ) (t : Heights.Fibre σ (X.H0 Lb.L)) : ℝ :=
  ⨆ x : X.complexPoints (intEmb σ), Lb.metric.norm (intEmb σ) x (X.evalFibre Lb.L σ x t)

def fibreInner {ρ : 𝓞 K →+* ℂ} (x : X.complexPoints ρ) (v w : X.Fibre Lb.L x) : ℂ :=
  ((((Lb.metric.norm ρ x (v + w)) ^ 2 - (Lb.metric.norm ρ x (v - w)) ^ 2 : ℝ) : ℂ) +
    (((Lb.metric.norm ρ x (v - Complex.I • w)) ^ 2 -
      (Lb.metric.norm ρ x (v + Complex.I • w)) ^ 2 : ℝ) : ℂ) * Complex.I) / 4

open Classical in

def l2Inner (μ : Measure (CP N)) (σ : K →+* ℂ) (t u : Heights.Fibre σ (X.H0 Lb.L)) : ℂ :=
  ∫ v, (if h : v ∈ X.complexPoints (intEmb σ) then
      X.fibreInner Lb ⟨v, h⟩ (X.evalFibre Lb.L σ ⟨v, h⟩ t) (X.evalFibre Lb.L σ ⟨v, h⟩ u)
    else 0) ∂μ

structure PointMeasures where

  μ : (K →+* ℂ) → Measure (CP N)
  isFinite : ∀ σ, IsFiniteMeasure (μ σ)

  null_compl : ∀ σ, μ σ (X.complexPoints (intEmb σ))ᶜ = 0

  pos_of_isOpen : ∀ σ (U : Set (CP N)), IsOpen U → (U ∩ X.complexPoints (intEmb σ)).Nonempty →
    0 < μ σ U

  map_conj : ∀ σ, μ (conjugate σ) = (μ σ).map CP.conj

end ProjScheme

namespace SectionsLattice

open ProjScheme

def Finite.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (N : ℕ) (X : ProjScheme (𝓞 K) N), Flat X.toBase →
    ∀ L : X.X.Modules, IsInvertibleSheaf L →
      Module.Finite (𝓞 K) (X.H0 L) ∧ Module.Projective (𝓞 K) (X.H0 L)

def EvalInjective.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (N : ℕ) (X : ProjScheme (𝓞 K) N), Flat X.toBase →
    IsReduced X.X → ∀ L : X.X.Modules, IsInvertibleSheaf L →
      ∀ (σ : K →+* ℂ) (t : Heights.Fibre σ (X.H0 L)),
        (∀ x : X.complexPoints (intEmb σ), X.evalFibre L σ x t = 0) → t = 0

def EvalContinuous.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (N : ℕ) (X : ProjScheme (𝓞 K) N)
    (Lb : X.HermitianLineBundle) (σ : K →+* ℂ) (t : Heights.Fibre σ (X.H0 Lb.L)),
      Continuous fun x : X.complexPoints (intEmb σ) ↦
        Lb.metric.norm (intEmb σ) x (X.evalFibre Lb.L σ x t)

def SupNorm.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (N : ℕ) (X : ProjScheme (𝓞 K) N), Flat X.toBase →
    IsReduced X.X → ∀ Lb : X.HermitianLineBundle,
      ∃ m : NormedMetric K (X.H0 Lb.L), ∀ σ t, m.norm σ t = X.supNorm Lb σ t

def L2.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (N : ℕ) (X : ProjScheme (𝓞 K) N), Flat X.toBase →
    IsReduced X.X → ∀ (Lb : X.HermitianLineBundle) (μ : X.PointMeasures)
      [Module.Finite (𝓞 K) (X.H0 Lb.L)] [Module.Projective (𝓞 K) (X.H0 Lb.L)],
      ∃ h : HermitianMetric K (X.H0 Lb.L),
        ∀ σ t u, (h.form σ).inner t u = X.l2Inner Lb (μ.μ σ) σ t u

variable {K : Type} [Field K] [NumberField K] {N : ℕ}

def sectionsNormed (hfin : Finite.Statement) (hsup : SupNorm.Statement) (X : ProjScheme (𝓞 K) N)
    (hflat : Flat X.toBase) (hred : IsReduced X.X) (Lb : X.HermitianLineBundle) : NormedBundle K :=
  haveI := (hfin K N X hflat Lb.L Lb.invertible).1
  haveI := (hfin K N X hflat Lb.L Lb.invertible).2
  ⟨X.H0 Lb.L, Classical.choose (hsup K N X hflat hred Lb)⟩

def sectionsHermitian (hfin : Finite.Statement) (hl2 : L2.Statement) (X : ProjScheme (𝓞 K) N)
    (hflat : Flat X.toBase) (hred : IsReduced X.X) (Lb : X.HermitianLineBundle)
    (μ : X.PointMeasures) : HermitianBundle K :=
  haveI := (hfin K N X hflat Lb.L Lb.invertible).1
  haveI := (hfin K N X hflat Lb.L Lb.invertible).2
  ⟨X.H0 Lb.L, Classical.choose (hl2 K N X hflat hred Lb μ)⟩

end SectionsLattice

namespace ProjScheme

variable (A : Type u) [CommRing A] (N : ℕ)

theorem toBase_base : (base A N).toBase = 𝟙 (Spec (.of A)) := baseSection_toSpecBase A N

instance flat_toBase_base : Flat (base A N).toBase := by
  rw [toBase_base]
  exact AlgebraicGeometry.Flat.instOfIsOpenImmersion (𝟙 _)

instance (ρ : A →+* ℂ) (U : (base A N).X.Opens) :
    Subsingleton {x : (base A N).complexPoints ρ // (base A N).point x ∈ U} :=
  ⟨fun y z ↦ by
    have hy := Set.mem_singleton_iff.mp ((Set.ext_iff.mp (complexPoints_base ρ) y.1.1).mp y.1.2)
    have hz := Set.mem_singleton_iff.mp ((Set.ext_iff.mp (complexPoints_base ρ) z.1.1).mp z.1.2)
    exact Subtype.ext (Subtype.ext (hy.trans hz.symm))⟩

def baseMetric : (base A N).ContinuousMetric (𝟙_ (base A N).X.Modules) where
  norm ρ x s := ‖(base A N).unitFibreEquiv x s‖
  norm_smul ρ x c s := by rw [LinearEquiv.map_smul, smul_eq_mul, norm_mul]
  norm_pos ρ x s hs := norm_pos_iff.mpr (by
    intro h0
    exact hs (((base A N).unitFibreEquiv x).map_eq_zero_iff.mp h0))
  continuous_frame ρ U e _ := continuous_of_discreteTopology
  norm_conj ρ U s x hx hx' := by
    rw [unitFibreEquiv_sectionValue, unitFibreEquiv_sectionValue,
      (base A N).evalAtPoint_conjPoint_germ x hx hx', Complex.norm_conj]

def baseBundle : (base A N).HermitianLineBundle :=
  ⟨𝟙_ _, isInvertibleSheaf_unit, baseMetric A N⟩

def baseGlobalSectionsEquiv : (base A N).H0 (𝟙_ (base A N).X.Modules) ≃ₗ[A] A where
  toFun s := (Scheme.ΓSpecIso (.of A)).hom.hom (show Γ(Spec (.of A), ⊤) from s)
  invFun a := (show (base A N).H0 (𝟙_ (base A N).X.Modules) from (Scheme.ΓSpecIso (.of A)).inv.hom a)
  map_add' s t := map_add (Scheme.ΓSpecIso (.of A)).hom.hom (show Γ(Spec (.of A), ⊤) from s)
    (show Γ(Spec (.of A), ⊤) from t)
  map_smul' a s := by
    change (Scheme.ΓSpecIso (.of A)).hom.hom
      ((show Γ(Spec (.of A), ⊤) from (base A N).baseHom a) * (show Γ(Spec (.of A), ⊤) from s)) =
        a * _
    rw [map_mul]
    congr 1
    change (Scheme.ΓSpecIso (.of A)).hom.hom
      (((base A N).toBase.appTop).hom ((Scheme.ΓSpecIso (.of A)).inv.hom a)) = a
    rw [toBase_base, Scheme.Hom.id_appTop]
    exact Iso.inv_hom_id_apply (Scheme.ΓSpecIso (.of A)) a
  left_inv s := Iso.hom_inv_id_apply (Scheme.ΓSpecIso (.of A)) _
  right_inv a := Iso.inv_hom_id_apply (Scheme.ΓSpecIso (.of A)) a

def basePoint : CP N :=
  Projectivization.mk ℂ (Pi.single 0 1) (by simp [funext_iff, Pi.single_apply])

theorem conj_basePoint : CP.conj (basePoint N) = basePoint N := by
  rw [basePoint, CP.conj_mk]
  congr 1
  funext k
  rw [CP.conjVec_apply]
  by_cases hk : k = 0
  · subst hk; simp
  · simp [hk]

variable {A N}

theorem complexPoints_base' (ρ : A →+* ℂ) : (base A N).complexPoints ρ = {basePoint N} :=
  complexPoints_base ρ

variable (K : Type) [Field K] [NumberField K] (N)

instance isReduced_base : IsReduced (base (𝓞 K) N).X := by
  change IsReduced (Spec (.of (𝓞 K)))
  infer_instance

instance : Module.Finite (𝓞 K) ((base (𝓞 K) N).H0 (baseBundle (𝓞 K) N).L) :=
  Module.Finite.equiv (baseGlobalSectionsEquiv (𝓞 K) N).symm

instance : Module.Projective (𝓞 K) ((base (𝓞 K) N).H0 (baseBundle (𝓞 K) N).L) :=
  Module.Projective.of_equiv (baseGlobalSectionsEquiv (𝓞 K) N).symm

instance : Nontrivial ((base (𝓞 K) N).H0 (baseBundle (𝓞 K) N).L) :=
  (baseGlobalSectionsEquiv (𝓞 K) N).toEquiv.nontrivial

def baseMeasures : (base (𝓞 K) N).PointMeasures where
  μ _ := Measure.dirac (basePoint N)
  isFinite _ := inferInstance
  null_compl σ := by
    rw [Measure.dirac_apply' _
      ((base (𝓞 K) N).isClosed_complexPoints _).isOpen_compl.measurableSet, complexPoints_base']
    simp
  pos_of_isOpen σ U _ hU := by
    obtain ⟨y, hyU, hy⟩ := hU
    rw [complexPoints_base', Set.mem_singleton_iff] at hy
    rw [Measure.dirac_apply_of_mem (hy ▸ hyU)]
    exact one_pos
  map_conj σ := by
    rw [Measure.map_dirac' CP.continuous_conj.measurable, conj_basePoint]

example : Flat (base (𝓞 ℚ) 1).toBase := inferInstance
example : IsReduced (base (𝓞 ℚ) 1).X := inferInstance
example : IsInvertibleSheaf (baseBundle (𝓞 ℚ) 1).L := (baseBundle (𝓞 ℚ) 1).invertible
example : (base (𝓞 ℚ) 1).PointMeasures := baseMeasures 1 ℚ
example : Module.Finite (𝓞 ℚ) ((base (𝓞 ℚ) 1).H0 (baseBundle (𝓞 ℚ) 1).L) := inferInstance
example : Module.Projective (𝓞 ℚ) ((base (𝓞 ℚ) 1).H0 (baseBundle (𝓞 ℚ) 1).L) := inferInstance
example : Nontrivial ((base (𝓞 ℚ) 1).H0 (baseBundle (𝓞 ℚ) 1).L) := inferInstance

end ProjScheme

end

end GroundTheory.Heights₂.Heights
