import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TwistBaseChangeAndValuationStatements
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsNsmulIffEq
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsAddInjective
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionPointActionPeriodValueFractionFielStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiGeneratorValueOneZeroFirstFactorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordBundleIsoTwoHomNormalisedAtOriginStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoValueOneZeroFirstFactorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordIsoEqRosatiGeneratorMulComparisonStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

noncomputable section

theorem GlobalTheory.Mum.Two.Fac.pt_ext (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F]
    [Algebra (FractionRing R) F] (a b : 𝟙_ (Over (Sp R)) ⟶ D.P.A)
    (h : toUnit (TF (R := R) F) ≫ a = toUnit (TF (R := R) F) ≫ b) : a = b := by
  have : IsDominant (jK R) := isDominant_jK
  have : Surjective (jFK (R := R) F) := GlobalTheory.Balanced.surjective_spMap (algebraMap (FractionRing R) F)
  have : IsDominant (jFK (R := R) F) := inferInstance
  have : IsProper D.P.A.hom := D.P.isAb.proper
  have e := congrArg (fun m => m.left) h
  simp only [Over.comp_left] at e
  refine Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated (X := Spec (CommRingCat.of R)) D.P.A.hom
    ((Over.w a).trans (Over.w b).symm) (jFK (R := R) F ≫ jK R) ?_)
  simpa using e

open GlobalTheory.Mum.Two.Fac in

theorem GlobalTheory.Mum.Two.Fac.periods_of_factor : ∀ (R : Type) [CommRing R] [IsDomain R] (D₀ D' : DegPre R), D'.TauBimult → ∀ (O : Type) [Ring O] [StarRing O] [Module O D'.X] (o : D'.OAct O) (e f : O) (inc : D₀.P.A ⟶ D'.P.A) (pr : D'.P.A ⟶ D₀.P.A) (h : D₀.X →+ D'.X) (φ : D'.X →+ D₀.X), IsMonHom inc → IsMonHom pr → pr ≫ inc = o.onB.act e → (∀ χ, ∃ u : LB.Gen (CmpLB D' D₀ pr (h χ) χ), Nrm u) → LBIso (abelian₂ D₀.P.A D₀.P.L) ((abelian₂ D'.P.A D'.P.L).pull (lift (fst D₀.P.A D₀.P.A ≫ inc) (snd D₀.P.A D₀.P.A ≫ inc ≫ o.onB.act f) : G2 D₀.P.A ⟶ G2 D'.P.A).left) → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F], (∀ (y : D'.X) (g : GtPtF D' F), GtPtF.IsIota y g → ∃ g' : GtPtF D₀ F, Act D' D₀ pr h g g' ∧ GtPtF.IsIota (φ y) g') → (∀ y, h (φ y) = star e • f • e • y) → (∀ y, D₀.c (φ y) = D'.c y ≫ pr) ∧ ∃ w : LB.Iso (abelian₂ D₀.P.A D₀.P.L) ((abelian₂ D'.P.A D'.P.L).pull (lift (fst D₀.P.A D₀.P.A ≫ inc) (snd D₀.P.A D₀.P.A ≫ inc ≫ o.onB.act f) : G2 D₀.P.A ⟶ G2 D'.P.A).left), w.IsGen ∧ ∀ y y' z J J', Good D'.P.L z J → Good D₀.P.L z J' → val (D₀.tau (φ y) (φ y')) (𝟙 _) z J' = GlobalTheory.PolDeg.lamVal w (lift (toUnit (TK R) ≫ D₀.c (φ y)) (toUnit (TK R) ≫ D₀.c (φ y'))).left z J J' * val (D'.tau (e • y) (f • e • y')) (𝟙 _) z J := by
  intro R _ _ D₀ D' hB O _ _ _ o e f inc pr h φ hinc hpr hpi hu hw F _ _ hiota hh
  have hG := GlobalTheory.globalFns_holds
  have hc : ∀ y, D₀.c (φ y) = D'.c y ≫ pr := by
    intro y
    obtain ⟨g', ha, hg'⟩ := hiota y _ (GlobalTheory.TorusExt.isIota_iota hB y)
    have h1 := ha.1
    rw [hg'.1, (GlobalTheory.TorusExt.isIota_iota hB y).1] at h1
    refine pt_ext R D₀ F _ _ ?_
    simpa only [Category.assoc] using h1
  refine ⟨hc, ?_⟩
  haveI := hinc
  haveI := hpr
  haveI : IsMonHom (o.onB.act f) := o.onB.hom f
  haveI : IsMonHom (o.onB.act e) := o.onB.hom e
  haveI : IsMonHom (o.onB.act (star e)) := o.onB.hom (star e)
  obtain ⟨w, hwg, hwn⟩ := GlobalTheory.T.exists_mumfordBundleIso_twoHom_normalisedAtOrigin D₀.P.A D'.P.A D₀.P.L D'.P.L D₀.P.isLB D'.P.isLB inc (inc ≫ o.onB.act f) hw
  have hw1 := GlobalTheory.T.mumfordBundleIso_value_one_zero_first_factor D₀.P.A D'.P.A D₀.P.L D'.P.L D₀.P.isLB D'.P.isLB D₀.P.isAb inc (inc ≫ o.onB.act f)
    w hwg hwn
  refine ⟨w, hwg, fun y y' z J J' hJ hJ' => ?_⟩
  obtain ⟨ur, hur, hur0⟩ := exists_ros hG D'.P.isAb D'.P.isLB (o.onB.act e) (o.onB.act (star e)) (o.onB.rosati e)
  have hur1 := GlobalTheory.T.rosatiGenerator_value_one_zero_first_factor D'.P.A D'.P.L D'.P.isLB D'.P.isAb _ _ ur hur hur0
  obtain ⟨JN₀, hJN, hl, hr⟩ := exists_good_join D'.P.isLB D₀.P.isLB hJ hJ'
  obtain ⟨u, hun⟩ := hu (φ y')
  obtain ⟨g', ha, hg'⟩ := hiota y _ (GlobalTheory.TorusExt.isIota_iota hB y)
  have A := GlobalTheory.T.torusExtensionPointAction_period_value_fractionField R D₀ D' pr h F y (φ y) _ g' (GlobalTheory.TorusExt.isIota_iota hB y) hg' ha (φ y') u hun z JN₀ hJN
  rw [hl, hr] at A
  have B := val_corr hJ (o.tau_bal e ur hur hur0 y (f • e • y')) (𝟙 _)
  beta_reduce at B
  rw [val_mul hJ, val_pull hJ, Category.id_comp, ← hh y'] at B
  have hq : D₀.c (φ y') ≫ inc ≫ o.onB.act f = D'.c (f • e • y') := by
    rw [hc, o.c_lin, o.c_lin, ← hpi]; simp only [Category.assoc]
  have hq' : D'.c (h (φ y')) = D'.c (f • e • y') ≫ o.onB.act (star e) := by
    rw [hh y', o.c_lin]
  have C := GlobalTheory.T.mumfordIso_eq_rosatiGenerator_mul_comparison R D₀ D' inc pr (o.onB.act e) (o.onB.act f) (o.onB.act (star e)) hpi w hwg hw1 ur hur hur1
    (h (φ y')) (φ y') (D'.c (f • e • y')) hq hq' u hun (TK R) (toUnit (TK R) ≫ D'.c y) z JN₀ hJN
  rw [hl, hr, Category.assoc, ← hc] at C
  rw [A, ← B, C]
  show _ = _ * _ * val (D'.tau (e • y) (f • e • y')) (𝟙 _) z J
  rw [mul_comm (val ur _ z J)]
  ac_rfl
