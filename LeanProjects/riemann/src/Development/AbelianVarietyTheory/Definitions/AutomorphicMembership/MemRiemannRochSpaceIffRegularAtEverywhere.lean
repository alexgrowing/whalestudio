import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContractsOfConstant

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.CechPic GlobalTheory.Adelic GlobalTheory.Cartier GlobalTheory.Cartier.CartierDiv GlobalTheory.QCoh

namespace GlobalTheory.ProjVar

structure Var (F : Type) [Field F] : Type where

  N : ℕ

  I : (PSpace F N).IdealSheafData

  dim : ℕ

  smooth : SmoothOfRelativeDimension dim (I.subschemeι ≫ PSpace.str F N)

  geomIntegral : GeometricallyIntegral (I.subschemeι ≫ PSpace.str F N)

namespace Var

variable {F : Type} [Field F] (Y : Var F)

def X : Scheme.{0} := Y.I.subscheme

def ι : Y.X ⟶ PSpace F Y.N := Y.I.subschemeι

def str : Y.X ⟶ Sp F := Y.ι ≫ PSpace.str F Y.N

theorem ι_str : Y.ι ≫ PSpace.str F Y.N = Y.str := rfl

instance isClosedImmersion_ι : IsClosedImmersion Y.ι :=
  inferInstanceAs (IsClosedImmersion Y.I.subschemeι)

instance smooth_str : SmoothOfRelativeDimension Y.dim Y.str := Y.smooth

instance geometricallyIntegral_str : GeometricallyIntegral Y.str := Y.geomIntegral

instance geometricallyConnected_str : GeometricallyConnected Y.str :=
  ⟨fun _ _ y _ fst snd h =>
    have := GeometricallyIntegral.geometrically_isIntegral (f := Y.str) y fst snd h
    inferInstance⟩

instance isIntegral_X : IsIntegral Y.X := GeometricallyIntegral.isIntegral_of_subsingleton Y.str

theorem isProjOver : IsProjOver Y.str := ⟨Y.N, Y.ι, inferInstance, rfl⟩

instance isProper_str : IsProper Y.str :=
  have := Geo.Tor.isProper_str F Y.N
  inferInstanceAs (IsProper (Y.ι ≫ PSpace.str F Y.N))

theorem isNormalScheme : IsNormalScheme Y.X :=
  have := SmoothOfRelativeDimension.smooth Y.dim Y.str
  isNormalScheme_of_smooth Y.str

theorem topologicalKrullDim_eq : topologicalKrullDim Y.X = Y.dim := by
  have hc (U : Y.X.Opens) (hU : IsAffineOpen U) (h : (U : Set Y.X).Nonempty) :
      topologicalKrullDim (U : Set Y.X) = Y.dim := by
    rw [topologicalKrullDim_eq_of_isEmbedding hU.fromSpec.isOpenEmbedding.isEmbedding
      hU.range_fromSpec]
    exact (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (R := Γ(Y.X, U))).trans
      (SmoothDim.ringKrullDim_affineOpen F _ Y.str _ inferInstance U hU h)
  refine le_antisymm (topologicalKrullDim_le_of_forall_exists_isOpen fun x => ?_) ?_
  · obtain ⟨U, hU, hx, -⟩ := Opens.isBasis_iff_nbhd.1 Y.X.isBasis_affineOpens (Opens.mem_top x)
    exact ⟨U, U.isOpen, hx, (hc U hU ⟨x, hx⟩).le⟩
  · obtain ⟨U, hU, hx, -⟩ := Opens.isBasis_iff_nbhd.1 Y.X.isBasis_affineOpens
      (Opens.mem_top (genericPoint Y.X))
    exact (hc U hU ⟨_, hx⟩).ge.trans (topologicalKrullDim_subspace_le _ _)

attribute [local instance] MvPolynomial.gradedAlgebra in

def coneIdeal : Ideal (MvPolynomial (Fin (Y.N + 1)) F) :=
  (show ProjectiveSpectrum (ProjSpace.grading F Y.N) from
    Y.ι (genericPoint Y.X)).asHomogeneousIdeal.toIdeal

attribute [local instance] MvPolynomial.gradedAlgebra in

theorem isPrime_coneIdeal : Y.coneIdeal.IsPrime :=
  (show ProjectiveSpectrum (ProjSpace.grading F Y.N) from Y.ι (genericPoint Y.X)).isPrime

attribute [local instance] MvPolynomial.gradedAlgebra in

theorem range_ι : Set.range Y.ι =
    ProjectiveSpectrum.zeroLocus (ProjSpace.grading F Y.N) Y.coneIdeal := by
  have h := ((genericPoint_spec Y.X).image Y.ι.continuous).def
  rw [Set.image_univ, Y.ι.isClosedEmbedding.isClosed_range.closure_eq] at h
  refine h.symm.trans ((ProjectiveSpectrum.zeroLocus_vanishingIdeal_eq_closure
    (ProjSpace.grading F Y.N) _).symm.trans ?_)
  exact congrArg (fun J : HomogeneousIdeal (ProjSpace.grading F Y.N) =>
    ProjectiveSpectrum.zeroLocus (ProjSpace.grading F Y.N) J)
      (ProjectiveSpectrum.vanishingIdeal_singleton _)

section OfImmersion

variable {Z : Scheme.{0}} {N : ℕ} (i : Z ⟶ PSpace F N) [IsClosedImmersion i] (d : ℕ)
  [SmoothOfRelativeDimension d (i ≫ PSpace.str F N)] [GeometricallyIntegral (i ≫ PSpace.str F N)]

omit [SmoothOfRelativeDimension d (i ≫ PSpace.str F N)]
  [GeometricallyIntegral (i ≫ PSpace.str F N)] in

theorem subschemeι_ker : i.ker.subschemeι = inv i.toImage ≫ i := by
  rw [IsIso.eq_inv_comp]; exact i.toImage_imageι

def ofClosedImmersion : Var F where
  N := N
  I := i.ker
  dim := d
  smooth := by
    rw [subschemeι_ker, Category.assoc]
    have := smoothOfRelativeDimension_isStableUnderBaseChange.{0} d
    exact MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension d)
      (IsPullback.of_horiz_isIso ⟨(Category.comp_id _).symm⟩) ‹_›
  geomIntegral := by
    rw [subschemeι_ker, Category.assoc]
    exact MorphismProperty.of_isPullback (P := @GeometricallyIntegral)
      (IsPullback.of_horiz_isIso ⟨(Category.comp_id _).symm⟩) ‹_›

def isoOfClosedImmersion : Z ≅ (ofClosedImmersion i d).X :=
  show Z ≅ i.image from asIso i.toImage

theorem isoOfClosedImmersion_ι :
    (isoOfClosedImmersion i d).hom ≫ (ofClosedImmersion i d).ι = i := i.toImage_imageι

end OfImmersion

theorem exists_iso {Z : Scheme.{0}} (p : Z ⟶ Sp F) (d : ℕ) [SmoothOfRelativeDimension d p]
    [GeometricallyConnected p] (h : IsProjOver p) :
    ∃ (Y : Var F) (e : Z ≅ Y.X), Y.dim = d ∧ e.hom ≫ Y.str = p := by
  obtain ⟨N, i, _, rfl⟩ := h
  have := SmoothOfRelativeDimension.smooth d (i ≫ PSpace.str F N)
  have := geometricallyIntegral_of_smooth (i ≫ PSpace.str F N)
  exact ⟨ofClosedImmersion i d, isoOfClosedImmersion i d, rfl,
    (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) (isoOfClosedImmersion_ι i d))⟩

instance algebraΓ : Algebra F Γ(Y.X, ⊤) := algebraΓOfHom Y.str

theorem algebraMap_Γ (a : F) :
    algebraMap F Γ(Y.X, ⊤) a = Y.str.appTop ((Scheme.ΓSpecIso (.of F)).inv a) := rfl

abbrev Fn : Type := Y.X.functionField

instance algebraFn : Algebra F Y.Fn := (Cartier.constFn Y.str).toAlgebra

theorem algebraMap_Fn : algebraMap F Y.Fn = Cartier.constFn Y.str := rfl

instance isScalarTower_Fn : IsScalarTower F Γ(Y.X, ⊤) Y.Fn :=
  .of_algebraMap_eq fun a => congrArg (fnOf ⊤ trivial) (LB.resG_self (X := Y.X) le_top _)

theorem regAt_algebraMap (x : Y.X) (a : F) : RegAt x (algebraMap F Y.Fn a) :=
  regAt_fnOf (U := ⊤) trivial trivial _

abbrev Dv : Type := CartierDiv Y.X

def Eff (Δ : Y.Dv) : Prop := Δ.Eff

def H0 (Δ : Y.Dv) : Submodule F Y.Fn := Δ.sections.restrictScalars F

variable {Y} in

theorem mem_riemannRochSpace_iff_regularAt_everywhere {Δ : Y.Dv} {f : Y.Fn} : f ∈ Y.H0 Δ ↔ ∀ x, Δ.RegularAt x f := mem_sections

variable {Y} in

theorem mem_riemannRoch_iff_effective {Δ : Y.Dv} {g : Y.Fnˣ} :
    (g : Y.Fn) ∈ Y.H0 Δ ↔ Y.Eff (principal g + Δ) := mem_sections_iff_eff

variable {Y} in

theorem eff_iff_one_mem {Δ : Y.Dv} : Y.Eff Δ ↔ (1 : Y.Fn) ∈ Y.H0 Δ := mem_riemannRochSpace_iff_regularAt_everywhere.symm

theorem eff_zero : Y.Eff 0 := CartierDiv.eff_zero

theorem eff_add (a b : Y.Dv) (ha : Y.Eff a) (hb : Y.Eff b) : Y.Eff (a + b) :=
  CartierDiv.Eff.add ha hb

theorem mul_mem_riemannRochSpace_add (Δ Δ' : Y.Dv) (f g : Y.Fn) (hf : f ∈ Y.H0 Δ) (hg : g ∈ Y.H0 Δ') :
    f * g ∈ Y.H0 (Δ + Δ') := mem_riemannRochSpace_iff_regularAt_everywhere.2 fun x => (mem_riemannRochSpace_iff_regularAt_everywhere.1 hf x).mul (mem_riemannRochSpace_iff_regularAt_everywhere.1 hg x)

theorem riemannRoch_mono (Δ Δ' : Y.Dv) (h : Y.Eff (Δ' - Δ)) : Y.H0 Δ ≤ Y.H0 Δ' := fun f hf => by
  simpa using Y.mul_mem_riemannRochSpace_add Δ (Δ' - Δ) f 1 hf (eff_iff_one_mem.1 h)

abbrev lb (Δ : Y.Dv) : LB Y.X := toLB Δ

variable {Y} in

def cohEquiv {Δ : Y.Dv} {L : LB Y.X} {r : L.ι → Y.Fnˣ} (h : Presents Δ L r) :
    coh (twist (structureModule Y.X) L) 0 ≃ₗ[F] Y.H0 Δ :=
  ((cohZeroTwistEquiv L).trans h.secEquiv).restrictScalars F

variable {Y} in

theorem finrank_sections_projectiveLine {Δ : Y.Dv} {L : LB Y.X} {r : L.ι → Y.Fnˣ} (h : Presents Δ L r) :
    Module.finrank F (Y.H0 Δ) = lbH0 F L := (cohEquiv h).finrank_eq.symm

instance finiteDimensional_riemannRochSpace (Δ : Y.Dv) : FiniteDimensional F (Y.H0 Δ) :=
  have := finite_coh_zero_twist_of_isProjOver Y.algebraMap_Γ Y.isProjOver (isLB_toLB Δ)
  .equiv (cohEquiv (presents_toLB Δ))

def omega0 : RatForms Y.str Y.dim := baseForm Y.str Y.dim

def KY : Y.Dv := canonical Y.str Y.dim

theorem omega0_ne_zero : Y.omega0 ≠ 0 := baseForm_ne_zero _ _

theorem isDivOfForm_KY : IsDivOfForm Y.KY Y.omega0 := isDivOfForm_canonical _ _

theorem exists_frame_KY (x : Y.X) : ∃ (U : Y.X.Opens) (hx : x ∈ U)
    (ω : TopForm.FormsOn Y.str Y.dim U) (g : Y.Fnˣ), TopForm.IsFrame ω ∧
      Y.omega0 = (g : Y.Fn) • formOf U (gen_mem hx) ω ∧ ∀ y ∈ U, Y.KY.IsEqn y g := by
  obtain ⟨U, ω, hx, hω⟩ := TopForm.exists_isFrame Y.str Y.dim x
  obtain ⟨c, hc⟩ := (isFreeGen_formOf (gen_mem hx) hω).2 Y.omega0
  have h0 : c ≠ 0 := fun e => Y.omega0_ne_zero (by rw [← hc, e]; exact zero_smul _ _)
  exact ⟨U, hx, ω, Units.mk0 c h0, hω, hc.symm,
    fun y hy => Y.isDivOfForm_KY U ω hω y hy _ hc.symm⟩

theorem regularAt_KY_iff {U : Y.X.Opens} {x : Y.X} (hx : x ∈ U) {ω : TopForm.FormsOn Y.str Y.dim U}
    (hω : TopForm.IsFrame ω) {f c : Y.Fn} (e : f • Y.omega0 = c • formOf U (gen_mem hx) ω) :
    Y.KY.RegularAt x f ↔ RegAt x c := by
  obtain ⟨g, hg⟩ := (isFreeGen_formOf (gen_mem hx) hω).2 Y.omega0
  replace hg : g • formOf U (gen_mem hx) ω = Y.omega0 := hg
  have h0 : g ≠ 0 := fun e => Y.omega0_ne_zero (by rw [← hg, e, zero_smul])
  rw [← hg, smul_smul] at e
  rw [(Y.isDivOfForm_KY U ω hω x hx (Units.mk0 g h0) hg.symm).regularAt_iff,
    ← (isFreeGen_formOf (gen_mem hx) hω).1 e]
  rfl

theorem toPic_KY (K : CanonLB Y.str Y.dim) : toPic Y.KY = cls K.bundle K.isLB :=
  (presents_canonical _ _).toPic_eq.trans ((cls_eq_iff _ _).2 (CanonLB.lbIso _ K))

abbrev Cl : Type := Closeds Y.X

def properCl (Z : Y.Cl) : Prop := Z ≠ ⊤

def subCl (Z Z' : Y.Cl) : Prop := Z ≤ Z'

def supp (Δ : Y.Dv) : Y.Cl := Δ.supp

def bpf (Δ : Y.Dv) (V : Set Y.Fn) : Prop := Δ.BasePointFree V

def vanishOn (Δ : Y.Dv) (f : Y.Fn) (Z : Y.Cl) : Prop := Δ.VanishesOn f Z

def phiBir (Δ : Y.Dv) (V : Set Y.Fn) : Prop := Δ.Birational F V

def phiNoContr (Δ : Y.Dv) (V : Set Y.Fn) (bd : Y.Cl) : Prop := Δ.NoContract F V bd

theorem properCl_iff (Z : Y.Cl) : Y.properCl Z ↔ genericPoint Y.X ∉ Z :=
  not_congr ⟨fun h => h.ge (Set.mem_univ _), fun h => top_le_iff.1
    (((genericPoint_spec Y.X).mem_closed_set_iff Z.isClosed).1 h)⟩

theorem properCl_supp (Δ : Y.Dv) : Y.properCl (Y.supp Δ) := Δ.supp_ne_top

variable {Y} in

theorem vanishOn.properCl {Δ : Y.Dv} {f : Y.Fn} {Z : Y.Cl} (h : Y.vanishOn Δ f Z) (hf : f ≠ 0) :
    Y.properCl Z := by
  rintro rfl
  exact hf (VanishesOn.eq_zero h)

variable {Y} in

theorem Eff.vanishOn_one_iff {Δ : Y.Dv} (h : Y.Eff Δ) {Z : Y.Cl} :
    Y.vanishOn Δ 1 Z ↔ Y.subCl Z (Y.supp Δ) := CartierDiv.Eff.vanishesOn_one_iff h

theorem isCompleteCurve_iff (Z : Y.Cl) : IsCompleteCurve F Z ↔
    IsIrreducible (Z : Set Y.X) ∧ topologicalKrullDim (Z : Set Y.X) = 1 :=
  GlobalTheory.isCompleteCurve_iff Y.algebraMap_Γ

abbrev sysOf {L : LB Y.X} (hL : L.IsLB) {n : ℕ} (s : Fin n → L.Sec) : LinSys F where
  Y := Y.X
  str := Y.str
  D := Y.dim
  L := L
  isLB := hL
  N := n
  b := s

theorem isVariety_sysOf (h : 1 ≤ Y.dim) {L : LB Y.X} (hL : L.IsLB) {n : ℕ} (s : Fin n → L.Sec) :
    (Y.sysOf hL s).IsVariety := ⟨Y.smooth, Y.isProjOver, Y.geometricallyConnected_str, h⟩

variable {Y} in

def sec {Δ : Y.Dv} (f : Y.H0 Δ) : (Y.lb Δ).Sec := (presents_toLB Δ).secEquiv.symm ⟨f.1, f.2⟩

variable {Y} in

@[simp] theorem rat_sec {Δ : Y.Dv} (f : Y.H0 Δ) : (presents_toLB Δ).rat (sec f) = f :=
  congrArg Subtype.val ((presents_toLB Δ).secEquiv.apply_symm_apply ⟨f.1, f.2⟩)

section LinSys

variable {Δ : Y.Dv} {n : ℕ} (b : Fin n → Y.H0 Δ)

abbrev linSys : LinSys F := Y.sysOf (isLB_toLB Δ) fun j => sec (b j)

theorem ratSet_linSys : Presents.ratSet (S := Y.linSys b) (presents_toLB Δ) =
    Set.range fun j => (b j : Y.Fn) :=
  congrArg Set.range (funext fun j => rat_sec (b j))

theorem bpf_iff : Y.bpf Δ (Set.range fun j => (b j : Y.Fn)) ↔ (Y.linSys b).BasePointFree :=
  Y.ratSet_linSys b ▸ Presents.basePointFree_iff (S := Y.linSys b) (presents_toLB Δ)

theorem phiBir_iff : Y.phiBir Δ (Set.range fun j => (b j : Y.Fn)) ↔
    (∃ j, (Y.linSys b).b j ≠ 0) ∧ (Y.linSys b).Birational :=
  Y.ratSet_linSys b ▸ Presents.birational_iff (S := Y.linSys b) (presents_toLB Δ)

theorem phiNoContr_iff (h : (Y.linSys b).BasePointFree) (bd : Y.Cl) :
    Y.phiNoContr Δ (Set.range fun j => (b j : Y.Fn)) bd ↔ (Y.linSys b).NoContract bd :=
  Y.ratSet_linSys b ▸ Presents.noContract_iff (S := Y.linSys b) (presents_toLB Δ) h bd

end LinSys

section Hyperplane

open ProjSpace

abbrev O1 : LB Y.X := (ProjSpace.O1 F Y.N).pull Y.ι

theorem isLineBundle_twistingSheafOne : Y.O1.IsLB := LB.isLB_pull (O1_isLB F Y.N) _

theorem isAmple_projective_O_one : IsAmpleLB Y.O1 :=
  (GlobalTheory.isAmple_projective_O_one F Y.N).pull_of_isClosedImmersion _

def coordSec (j : Fin (Y.N + 1)) : Y.O1.Sec := secPull (coord F Y.N j) Y.ι

theorem nonzeroLocus_coordSec (j : Fin (Y.N + 1)) :
    nonzeroLocus (Y.coordSec j) = Y.ι ⁻¹ᵁ chart F Y.N j := by
  rw [coordSec, nonzeroLocus_secPull, nonzeroLocus_coord]
  rfl

abbrev coordSys : LinSys F := Y.sysOf Y.isLineBundle_twistingSheafOne Y.coordSec

def idx (i : Fin (Y.N + 1)) : Y.O1.ι := fun _ => i

theorem twistingSheafOne_chart_eq_preimage_standardChart (i : Fin (Y.N + 1)) : Y.O1.U (Y.idx i) = Y.ι ⁻¹ᵁ chart F Y.N i :=
  LB.pull_U (L := ProjSpace.O1 F Y.N) Y.ι (Y.idx i)

def chartHom (i : Fin (Y.N + 1)) :
    Γ(PSpace F Y.N, chart F Y.N i) →+* Γ(Y.X, Y.O1.U (Y.idx i)) :=
  (Y.ι.appLE _ _ (Y.twistingSheafOne_chart_eq_preimage_standardChart i).le).hom

theorem chartEval_coordSec (i : Fin (Y.N + 1)) (g : MvPolynomial (Fin (Y.N + 1)) F) :
    Twist.chartEval F Y.coordSec (Y.idx i) le_rfl g = Y.chartHom i (aeval (ratio F Y.N i) g) := by
  rw [Twist.chartEval, aeval_def, ← coe_eval₂Hom, map_eval₂Hom]
  congr 2
  · refine RingHom.ext fun a => ?_
    rw [RingHom.comp_apply, RingHom.comp_apply, ← resG_algebraMap le_top, chartHom, LB.appLE_resG,
      algebraMap_top_eq]
    rfl
  · exact funext fun l => LB.resG_self _ _

attribute [local instance] MvPolynomial.gradedAlgebra in

theorem mem_nonzeroLocus_form {d : ℕ} {g : MvPolynomial (Fin (Y.N + 1)) F} (hg : g.IsHomogeneous d)
    (y : Y.X) : y ∈ nonzeroLocus (Y.coordSys.form hg) ↔
      Y.ι y ∈ Proj.basicOpen (grading F Y.N) g := by
  obtain ⟨i, hi⟩ := exists_mem_chart F Y.N (Y.ι y)
  have hj : y ∈ Y.O1.U (Y.idx i) := (Y.twistingSheafOne_chart_eq_preimage_standardChart i).ge hi
  have e := Twist.basicOpen_zfun (Y.coordSys.form hg) (Y.idx i)
  rw [LinSys.form, Twist.zfun_formSec, chartEval_coordSec, ← formOn_eq_aeval hg] at e
  replace e := (Scheme.basicOpen_appLE Y.ι _ _ (Y.twistingSheafOne_chart_eq_preimage_standardChart i).le _).symm.trans e
  rw [basicOpen_formOn] at e
  exact ⟨fun h => (e.ge ⟨hj, h⟩).2.2, fun h => (e.le ⟨hj, hi, h⟩).2⟩

theorem basePointFree_coordSys : Y.coordSys.BasePointFree := eq_top_iff.2 fun y _ =>
  have ⟨j, hj⟩ := exists_mem_chart F Y.N (Y.ι y)
  Opens.mem_iSup.2 ⟨j, (Y.nonzeroLocus_coordSec j).ge hj⟩

attribute [local instance] MvPolynomial.gradedAlgebra in

theorem eq_of_sameImage {y y' : Y.X} (h : Y.coordSys.SameImage y y') : y = y' := by
  refine Y.ι.isClosedEmbedding.injective
    (ProjectiveSpectrum.ext (HomogeneousIdeal.ext' fun d g hg => ?_))
  replace hg : g.IsHomogeneous d := hg
  have := h d g hg
  rw [mem_nonzeroLocus_form, mem_nonzeroLocus_form] at this
  exact not_iff_not.1 this

theorem noContract_coordSys (bd : Set Y.X) : Y.coordSys.NoContract bd := fun C _ _ hC _ h => by
  have : Subsingleton C := ⟨fun a b => Subtype.ext (Y.eq_of_sameImage (h _ a.2 _ b.2))⟩
  have := topologicalKrullDim_zero_of_discreteTopology C
  rw [hC] at this
  exact absurd this (by decide)

theorem exists_coord_ne_zero : ∃ i, Y.ι (genericPoint Y.X) ∈ chart F Y.N i :=
  exists_mem_chart F Y.N _

variable {i : Fin (Y.N + 1)} (hi : Y.ι (genericPoint Y.X) ∈ chart F Y.N i)

include hi in

theorem genericPoint_mem_twistingSheafOne_chart : genericPoint Y.X ∈ Y.O1.U (Y.idx i) := (Y.twistingSheafOne_chart_eq_preimage_standardChart i).ge hi

def hyp : Y.Dv := ofLB Y.isLineBundle_twistingSheafOne (Y.idx i) (Y.genericPoint_mem_twistingSheafOne_chart hi)

theorem presents_hyp : Presents (Y.hyp hi) Y.O1 (frameRat _ (Y.idx i) (Y.genericPoint_mem_twistingSheafOne_chart hi)) :=
  presents_ofLB _ _ _

def coordFn (j : Fin (Y.N + 1)) : Y.Fn := (Y.presents_hyp hi).rat (Y.coordSec j)

theorem aeval_coordFn (g : MvPolynomial (Fin (Y.N + 1)) F) : aeval (Y.coordFn hi) g =
    fnOf _ (Y.genericPoint_mem_twistingSheafOne_chart hi) (Y.chartHom i (aeval (ratio F Y.N i) g)) := by
  rw [← Y.chartEval_coordSec i, Twist.chartEval, map_eval₂Hom, aeval_def, coe_eval₂Hom]
  congr 1
  · exact RingHom.ext fun a => (IsScalarTower.algebraMap_apply F Γ(Y.X, ⊤) _ a).trans
      (fnOf_resG le_top _ _).symm
  · funext j
    rw [LB.resG_self, ← (Y.presents_hyp hi).rat_mul, frameRat_self Y.isLineBundle_twistingSheafOne, Units.val_one, mul_one,
      coordFn]

theorem coordFn_self : Y.coordFn hi i = 1 := by
  have := Y.aeval_coordFn hi (MvPolynomial.X i)
  rwa [aeval_X, aeval_X, ratio, ratioOn_self, map_one, map_one] at this

theorem coordFn_mem (j : Fin (Y.N + 1)) : Y.coordFn hi j ∈ Y.H0 (Y.hyp hi) :=
  (Y.presents_hyp hi).rat_mem _

theorem generatesAt_coordFn_iff (j : Fin (Y.N + 1)) (y : Y.X) :
    (Y.hyp hi).GeneratesAt y (Y.coordFn hi j) ↔ Y.ι y ∈ chart F Y.N j := by
  rw [coordFn, Presents.generatesAt_rat_iff, nonzeroLocus_coordSec]
  rfl

theorem eff_hyp : Y.Eff (Y.hyp hi) := eff_iff_one_mem.2 (Y.coordFn_self hi ▸ Y.coordFn_mem hi i)

theorem mem_supp_hyp (y : Y.X) : y ∈ Y.supp (Y.hyp hi) ↔ Y.ι y ∉ chart F Y.N i := by
  rw [← Y.generatesAt_coordFn_iff hi, coordFn_self, ← notMem_supp_iff, not_not]
  rfl

theorem bpf_hyp : Y.bpf (Y.hyp hi) (Set.range (Y.coordFn hi)) :=
  (Presents.basePointFree_iff (S := Y.coordSys) (Y.presents_hyp hi)).2 Y.basePointFree_coordSys

theorem phiNoContr_hyp (bd : Y.Cl) : Y.phiNoContr (Y.hyp hi) (Set.range (Y.coordFn hi)) bd :=
  (Presents.noContract_iff (S := Y.coordSys) (Y.presents_hyp hi) Y.basePointFree_coordSys _).2
    (Y.noContract_coordSys _)

theorem phiBir_hyp : Y.phiBir (Y.hyp hi) (Set.range (Y.coordFn hi)) := by
  refine ⟨(Y.bpf_hyp hi).mem, (Y.bpf_hyp hi).exists_ne_zero, eq_top_iff.2 fun f _ => ?_⟩
  have hU : IsAffineOpen (Y.ι ⁻¹ᵁ chart F Y.N i) := (isAffineOpen_chart F Y.N i).preimage _
  have : Nonempty (Y.ι ⁻¹ᵁ chart F Y.N i :) := ⟨⟨_, hi⟩⟩
  have := functionField_isFractionRing_of_isAffineOpen _ _ hU
  have key (a : Γ(Y.X, Y.ι ⁻¹ᵁ chart F Y.N i)) :
      algebraMap _ Y.Fn a ∈ ratioField F (Set.range (Y.coordFn hi)) := by
    obtain ⟨a, rfl⟩ := Y.ι.app_surjective _ (isAffineOpen_chart F Y.N i) a
    obtain ⟨g, rfl⟩ := aeval_ratio_surjective F Y.N i a
    have e := Y.aeval_coordFn hi g
    rw [chartHom, ← LB.resG_app, fnOf_resG] at e
    refine e ▸ (?_ : aeval (Y.coordFn hi) g ∈ _)
    clear e
    induction g using MvPolynomial.induction_on with
    | C a => rw [algHom_C]; exact IntermediateField.algebraMap_mem _ a
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | mul_X p j hp =>
      rw [map_mul, aeval_X]
      exact mul_mem hp (IntermediateField.subset_adjoin _ _ ⟨_, ⟨j, rfl⟩, _, ⟨i, rfl⟩,
        by rw [coordFn_self]; exact one_ne_zero, by rw [coordFn_self, div_one]⟩)
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := Γ(Y.X, Y.ι ⁻¹ᵁ chart F Y.N i)) f
  exact div_mem (key a) (key b)

end Hyperplane

theorem not_phiNoContr_of_constant (h : Y.dim = 1) {Δ : Y.Dv} {V : Set Y.Fn}
    (hV : ∀ f ∈ V, f ∈ Set.range (algebraMap F Y.Fn)) : ¬ Y.phiNoContr Δ V ⊥ := fun c =>
  c.2 Set.univ isClosed_univ (IrreducibleSpace.isIrreducible_univ _)
    ((topologicalKrullDim_eq_of_isEmbedding Topology.IsEmbedding.id Set.range_id).trans
      (Y.topologicalKrullDim_eq.trans (by rw [h]; rfl)))
    (Set.disjoint_empty _) (contracts_of_constant Y.regAt_algebraMap hV _)

end Var

def RiemannRochFinite (F : Type) [Field F] : Prop :=
  ∀ (Y : Var F) (Δ : Y.Dv), FiniteDimensional F (Y.H0 Δ)

theorem riemannRoch_finite (F : Type) [Field F] : RiemannRochFinite F := Var.finiteDimensional_riemannRochSpace

section Proj

open ProjSpace

variable (F : Type) [Field F] (n : ℕ)

instance smooth_id_str : SmoothOfRelativeDimension n (𝟙 _ ≫ PSpace.str F n) := by
  rw [Category.id_comp]; exact smoothOfRelativeDimension_pspace F n

instance geometricallyIntegral_id_str : GeometricallyIntegral (𝟙 _ ≫ PSpace.str F n) := by
  have := SmoothOfRelativeDimension.smooth n (𝟙 _ ≫ PSpace.str F n)
  have : GeometricallyConnected (𝟙 _ ≫ PSpace.str F n) := by
    rw [Category.id_comp]; exact geometricallyConnected_pspace F n
  exact geometricallyIntegral_of_smooth _

def proj : Var F := Var.ofClosedImmersion (𝟙 (PSpace F n)) n

instance : Inhabited (Var F) := ⟨proj F 0⟩

theorem proj_dim : (proj F n).dim = n := rfl

instance isIso_proj_ι : IsIso (proj F n).ι :=
  have : IsIso ((Var.isoOfClosedImmersion (𝟙 (PSpace F n)) n).hom ≫ (proj F n).ι) :=
    (Var.isoOfClosedImmersion_ι (𝟙 (PSpace F n)) n).symm ▸ inferInstanceAs (IsIso (𝟙 _))
  IsIso.of_isIso_comp_left (Var.isoOfClosedImmersion (𝟙 (PSpace F n)) n).hom _

theorem proj_gen_mem (i : Fin (n + 1)) :
    (proj F n).ι (genericPoint (proj F n).X) ∈ chart F n i :=
  have h : genericPoint (PSpace F (proj F n).N) ∈ chart F n i := gen_mem (projSys.gen_mem F n i)
  (genericPoint_eq_of_isOpenImmersion (proj F n).ι).symm ▸ h

def projHyp : (proj F n).Dv := (proj F n).hyp (proj_gen_mem F n 0)

theorem finrank_riemannRoch_hyperplane : Module.finrank F ((proj F n).H0 (projHyp F n)) = n + 1 := by
  have := Geo.Tor.isProper_str F n
  have H : IsPullback (proj F n).ι (proj F n).str (PSpace.str F n)
      (Spec.map (CommRingCat.ofHom (algebraMap F F))) := by
    rw [show Spec.map (CommRingCat.ofHom (algebraMap F F)) = 𝟙 _ from Spec.map_id _]
    exact IsPullback.of_horiz_isIso ⟨(Category.comp_id _).symm⟩
  have h := FieldChangeInter.hdim_pull (f := PSpace.str F n) H (O1_isLB F n) 0
  refine (Var.finrank_sections_projectiveLine ((proj F n).presents_hyp _)).trans (h.trans ?_)
  have e := sectionDim_twistingSheaf_pow F n 1
  rw [lineBundleGlobalSectionsDim_congr_picardClass (isLB_lbPow (O1_isLB F n) 1) (O1_isLB F n)
    (by rw [cls_lbPow (O1_isLB F n), one_nsmul]), add_comm, Nat.choose_succ_self_right,
    ← projSys.algebraΓ_eq] at e
  exact e

theorem riemannRoch_hyperplane_ne_bot : (proj F n).H0 (projHyp F n) ≠ ⊥ := fun h => by
  have := finrank_riemannRoch_hyperplane F n
  rw [h, finrank_bot] at this
  omega

theorem exists_nonconstant_line : ∃ f ∈ (proj F 1).H0 (projHyp F 1),
    f ∉ Set.range (algebraMap F (proj F 1).Fn) := by
  by_contra! h
  exact (proj F 1).not_phiNoContr_of_constant rfl
    (fun f hf => h f (((proj F 1).bpf_hyp _).mem f hf))
    ((proj F 1).phiNoContr_hyp (proj_gen_mem F 1 0) ⊥)

example : Module.finrank F ((proj F 1).H0 (projHyp F 1)) = 2 := finrank_riemannRoch_hyperplane F 1

example : (proj F 1).Eff (projHyp F 1) ∧ projHyp F 1 ≠ 0 ∧ ¬ (proj F 1).Eff (-projHyp F 1) := by
  have h : projHyp F 1 ≠ 0 := fun e => by
    have h₁ := ((proj F 1).presents_hyp (proj_gen_mem F 1 0)).toPic_eq
    have hA := (proj F 1).isAmple_projective_O_one
    refine hA.not_isNef_dual (k := F) (((proj F 1).isCompleteCurve_iff ⊤).2
      ⟨IrreducibleSpace.isIrreducible_univ _,
        (topologicalKrullDim_eq_of_isEmbedding Topology.IsEmbedding.id Set.range_id).trans
          (proj F 1).topologicalKrullDim_eq⟩)
      ((isNef_triv F _).of_cls_eq (isLB_dual hA.isLB) ?_)
    rw [cls_dual hA.isLB, ← h₁, show (proj F 1).hyp (proj_gen_mem F 1 0) = 0 from e, map_zero,
      neg_zero]
    rfl
  exact ⟨(proj F 1).eff_hyp _, h, fun h' => h (CartierDiv.Eff.eq_zero ((proj F 1).eff_hyp _) h')⟩

example : (proj F 1).bpf 0 {1} ∧ ¬ (proj F 1).phiBir 0 {1} ∧ ¬ (proj F 1).phiNoContr 0 {1} ⊥ := by
  refine ⟨⟨?_, fun x => ⟨1, rfl, generatesAt_zero_iff.2 (unitAt_one x)⟩⟩, fun h => ?_,
    (proj F 1).not_phiNoContr_of_constant rfl ?_⟩
  · intro f hf
    rw [Set.mem_singleton_iff.1 hf]
    exact mem_sections.2 CartierDiv.eff_zero
  · obtain ⟨f, -, hf⟩ := exists_nonconstant_line F
    have hle : ratioField F ({1} : Set (proj F 1).Fn) ≤ ⊥ := IntermediateField.adjoin_le_iff.2 (by
      rintro _ ⟨f, hf, g, hg, -, rfl⟩
      rw [Set.mem_singleton_iff.1 hf, Set.mem_singleton_iff.1 hg, div_one]
      exact one_mem _)
    exact hf (IntermediateField.mem_bot.1 (hle (h.ratioField_eq.ge trivial)))
  · exact fun f hf => ⟨1, (map_one _).trans (Set.mem_singleton_iff.1 hf).symm⟩

end Proj

end GlobalTheory.ProjVar
