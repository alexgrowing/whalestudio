import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CInfGood
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BcMapBcVec
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.FlatChernWeightEqOfIndependence
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.OnbMat
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.RegularFormsIsBundleProjectiveCover
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.TwistedDualRegularFormsFiniteCover
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CuspOnto
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.AdelicGLLastRowAndDetModuleUnderLeftMultiplicati
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import Development.AutomorphicSpectrum.Statements.GeometryStatements.LamLevel
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ThmFlatA
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
import Development.AutomorphicSpectrum.Statements.MetricStatements.SmallOnTower
import Development.AutomorphicSpectrum.Statements.MetricStatements.RankBound
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.ShareLow
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.LineDegreeClosedFormula
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.SpecFirstDetFormNeZero
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SectionsGenericIndicators
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivComp
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.GeometricLiftsOfFrames
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CoefficientFieldAlgClosedInFunctionFieldsOfPerio
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.LinearDisjointAlgebraicClosure
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.CountableFractionRingMvPolynomial
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.EvCEqZeroIffRdUEqZero
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.SectionEqZeroOfGenericFramedPointValues
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.EvaluationLawsGenericFramesAtlasHold
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.FrMapComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GGConn
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Plug.ArchimedeanSections

open AlgebraicGeometry CategoryTheory Limits GlobalTheory.LevelCoverCompare GlobalTheory.IndefiniteRowSideFullHecke.DeltaDatumCombinedCoefficient GlobalTheory.CompRat.FixedConst
open scoped IntermediateField

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

theorem frames_nonempty' {r : ℕ} (X : Data E r) : X.dom.Nonempty := by
  classical
  choose P hP hG using X.signature
  refine ⟨fun τ => P τ, fun τ => ⟨hP τ, fun i => ?_⟩⟩
  have h : dmin X.Gm (fun τ => P τ) τ i = ((psgn X.p0 i : ℝ) : ℂ) := by
    have hm : mat (Ψ := X.Ψ) (fun τ => P τ) τ = P τ := rfl
    unfold dmin lminor
    rw [hm, hG τ, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal]
    unfold psgn
    rw [Complex.ofReal_prod, ← Fin.prod_univ_eq_prod_range (fun a => ((sgn X.p0 a : ℝ) : ℂ))]
    rfl
  rw [h, Complex.ofReal_re]
  refine mul_self_pos.2 ?_
  unfold psgn
  refine Finset.prod_ne_zero_iff.2 fun a _ => ?_
  unfold sgn
  split_ifs <;> norm_num

theorem rdU_eq_of_reads' {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (h : GenFrEx Xo c) (k : U.Comp)
    (Z : Comp Xo c) (x : (U.X k).dom) (φ : Om Z →ₐ[c.F] CAt σ) (y' : FrPt Xo c (CAt σ)) (t : Ix Dw → (CAt σ)ˣ)
    (hm : FrMap φ (genFr h Z) y') (hb : FrBor t (U.un k x) y') (u : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) :
    ∃ w : ℂ, w ≠ 0 ∧ ∀ f ∈ Formalism.L2.Pj.sec Xo c u n, w * rdU U f k x = toC (φ (evC h Z f)) := by
  letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
  obtain ⟨hL, -, -, -⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c
  have h3 : wchar (ex Dw u n) t ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (t i).ne_zero
  refine ⟨toC (wchar (ex Dw u n) t), h3, fun f hf => ?_⟩
  have h1 : evR Xo c f y' = φ (evC h Z f) := by
    obtain ⟨q, χ, y₀, hy₀⟩ := hL.test (Om Z) (genFr h Z)
    unfold evC
    rw [GlobalTheory.Reg.evR_eq_map_of_test_point hL hf q χ y₀ _ hy₀,
      GlobalTheory.Reg.evR_eq_map_of_test_point hL hf q (φ.comp χ) y₀ y' (ReciprocityTheory.ChartRestriction.G.PullbackSections.frMap_trans χ φ hy₀ hm)]
    rfl
  have h2 : evR Xo c f y' = wchar (ex Dw u n) t * evR Xo c f (U.un k x) :=
    hL.wt u n f hf (CAt σ) t _ _ (hL.test _ _) (hL.test _ _) hb
  have h4 : rdU U f k x = toC (evR Xo c f (U.un k x)) := by
    simp only [rdU, LinearMap.coe_mk, AddHom.coe_mk]
    rw [dif_pos x.2]
  rw [h4, ← h1, h2]
  rfl

theorem dom_zero : Dom (0 : (E →+* ℂ) × ℕ → ℕ) 0 := ⟨fun _ _ _ _ => le_rfl, ⟨0, rfl⟩⟩

theorem one_mem_weight_zero_sections : (1 : Rul Xo c) ∈ Formalism.L2.Pj.sec Xo c 0 0 := by
  refine ⟨fun p q φ y z _ => (map_one φ).symm, fun p t y y' _ => ?_⟩
  have hw : wchar (ex Dw 0 0) t = 1 := Finset.prod_eq_one fun i _ => by cases i <;> exact pow_zero _
  show (1 : p.R) = wchar (ex Dw 0 0) t * 1
  rw [hw, one_mul]

def evA {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S)
    (hy : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y) : Rul Xo c →ₐ[c.F] S where
  toFun f := evR Xo c f y
  map_one' := evalAt_one _ _ y hy
  map_mul' f g := evalAt_mul _ _ f g y
  map_zero' := evalAt_zero _ _ y
  map_add' f g := evalAt_add _ _ f g y
  commutes' a := by
    show evR Xo c (algebraMap c.F (Rul Xo c) a) y = _
    rw [Algebra.algebraMap_eq_smul_one]
    exact (evalAt_smul _ _ a 1 y).trans (by rw [evalAt_one _ _ y hy, mul_one])

theorem pow_mem_weight_zero_sections {f : Rul Xo c} (hf : f ∈ Formalism.L2.Pj.sec Xo c 0 0) (n : ℕ) :
    f ^ n ∈ Formalism.L2.Pj.sec Xo c 0 0 := by
  induction n with
  | zero => simpa using one_mem_weight_zero_sections
  | succ n ih =>
    rw [pow_succ]
    simpa using sec_mul Xo c 0 0 0 0 ih hf

theorem aeval_mem_weight_zero_sections {f : Rul Xo c} (hf : f ∈ Formalism.L2.Pj.sec Xo c 0 0) (P : Polynomial c.F) :
    Polynomial.aeval f P ∈ Formalism.L2.Pj.sec Xo c 0 0 := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add]
    exact add_mem hp hq
  | monomial n a =>
    rw [Polynomial.aeval_monomial, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (pow_mem_weight_zero_sections hf n)

theorem rdU_apply {σ : c.F →+* ℂ} (V : Unf Xo c σ r) (f : Rul Xo c) (k : V.Comp) (x : (V.X k).dom) :
    rdU V f k x = toC (evR Xo c f (V.un k x)) := by
  simp only [rdU, LinearMap.coe_mk, AddHom.coe_mk]
  rw [dif_pos x.2]

theorem exists_two_emb {K Ω : Type} [Field K] [CharZero K] [Countable K] [Field Ω] [Countable Ω] [Algebra K Ω]
    (σ : K →+* ℂ) (a : Ω) (ha : IsAlgebraic K a) (hne : a ∉ (algebraMap K Ω).range) :
    letI := σ.toAlgebra
    ∃ φ₁ φ₂ : Ω →ₐ[K] ℂ, φ₁ a ≠ φ₂ a := by
  letI : Algebra K ℂ := σ.toAlgebra
  have hi : IsIntegral K a := ha.isIntegral
  have hirr := minpoly.irreducible hi
  have hdeg : 2 ≤ (minpoly K a).natDegree := by
    by_contra h
    have h0 : (minpoly K a).natDegree ≠ 0 := hirr.natDegree_pos.ne'
    have h1 : (minpoly K a).natDegree = 1 := by omega
    exact hne (minpoly.mem_range_of_degree_eq_one K a
      ((Polynomial.degree_eq_iff_natDegree_eq_of_pos one_pos).2 h1))
  have hcard := IntermediateField.card_algHom_adjoin_integral K (K := ℂ) (α := a) hi
    hirr.separable (IsAlgClosed.splits _)
  have : Finite (K⟮a⟯ →ₐ[K] ℂ) := by
    apply Nat.finite_of_card_ne_zero
    omega
  have hnt : Nontrivial (K⟮a⟯ →ₐ[K] ℂ) := Finite.one_lt_card_iff_nontrivial.1 (by omega)
  obtain ⟨ψ₁, ψ₂, hψ⟩ := exists_pair_ne (K⟮a⟯ →ₐ[K] ℂ)
  have hext : ∀ ψ : K⟮a⟯ →ₐ[K] ℂ, ∃ φ : Ω →ₐ[K] ℂ, φ a = ψ (IntermediateField.AdjoinSimple.gen K a) := by
    intro ψ
    letI : Algebra K⟮a⟯ ℂ := ψ.toRingHom.toAlgebra
    have : FaithfulSMul K⟮a⟯ Ω :=
      (faithfulSMul_iff_algebraMap_injective _ _).2 (algebraMap K⟮a⟯ Ω).injective
    have : FaithfulSMul K⟮a⟯ ℂ :=
      (faithfulSMul_iff_algebraMap_injective _ _).2 (algebraMap K⟮a⟯ ℂ).injective
    obtain ⟨φ'⟩ := GlobalTheory.nonempty_algHom_complex_of_countable K⟮a⟯ Ω
    refine ⟨{ φ'.toRingHom with commutes' := fun k => ?_ }, ?_⟩
    · have h1 : algebraMap K Ω k = algebraMap K⟮a⟯ Ω (algebraMap K K⟮a⟯ k) := rfl
      show φ' (algebraMap K Ω k) = _
      rw [h1, φ'.commutes]
      exact ψ.commutes k
    · have h1 : a = algebraMap K⟮a⟯ Ω (IntermediateField.AdjoinSimple.gen K a) := rfl
      show φ' a = _
      exact (congrArg φ' h1).trans (φ'.commutes _)
  obtain ⟨φ₁, h₁⟩ := hext ψ₁
  obtain ⟨φ₂, h₂⟩ := hext ψ₂
  refine ⟨φ₁, φ₂, fun e => hψ ?_⟩
  refine (IntermediateField.adjoin.powerBasis hi).algHom_ext ?_
  rw [IntermediateField.adjoin.powerBasis_gen, ← h₁, ← h₂, e]

theorem basePt_genFr (h : GenFrEx Xo c) (Z : Comp Xo c) :
    basePt (genFr h Z) = spMap (algebraMap (kap Z) (Om Z)) ≫ genSp Z := by
  have e0 : Spec.map (CommRingCat.ofHom (algebraMap c.F (kap Z))) = genSp Z ≫ strK := by
    show Spec.map (CommRingCat.ofHom (Spec.preimage (genSp Z ≫ strK)).hom) = _
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  apply pullback.hom_ext
  · rw [basePt, pullback.lift_fst, (isGenFr_genFr h Z).1, Category.assoc]
    rfl
  · rw [basePt, pullback.lift_snd, Category.assoc]
    show _ = spMap (algebraMap (kap Z) (Om Z)) ≫ (genSp Z ≫ strK)
    rw [← e0]
    show Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

set_option maxHeartbeats 1000000 in

theorem exists_fn (h : GenFrEx Xo c) (Z : Comp Xo c) (r₀ : kap Z) (hr : IsIntegral c.F r₀) :
    ∃ f ∈ Formalism.L2.Pj.sec Xo c 0 0, evC h Z f = algebraMap (kap Z) (Om Z) r₀ := by
  have hfin : FiniteDimensional ℚ c.F := c.fin
  have hcF : Countable c.F := Cardinal.mk_le_aleph0_iff.1 (by
    simpa [Cardinal.mkRat] using Algebra.IsAlgebraic.cardinalMk_le_max ℚ c.F)
  have hk : Countable (kap Z) :=
    GlobalTheory.GenericReading.countable_of_fg_top ((GlobalTheory.Reg.kap_fg_trdeg E H Dw l Xo c).1 Z)
  obtain ⟨φ⟩ : Nonempty (kap Z →ₐ[c.F] ℂ) := GlobalTheory.nonempty_algHom_complex_of_countable c.F (kap Z)
  have := Xo.smooth
  have : Smooth Xo.s := SmoothOfRelativeDimension.smooth Dw.dim Xo.s
  have := CompFin.isNoetherian_XF Xo c
  have : GlobalTheory.IsNormalScheme (Xo.XF c) := (GlobalTheory.isNormalScheme_iff _).2
    (GlobalTheory.forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth (strK (Xo := Xo) (c := c))
      ((GlobalTheory.isNormalScheme_iff _).1 inferInstance))
  let κ : c.F →+* Γ(Xo.XF c, ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of c.F)).inv ≫ (strK (Xo := Xo) (c := c)).appTop).hom
  let j : c.F →+* ℂ := algebraMap c.F ℂ
  have hκ : ∀ (x : Sp ℂ ⟶ Xo.XF c) (i : c.F →+* ℂ), x ≫ strK = spMap i → (ev x).comp κ = i := by
    intro x i hx
    ext k
    change ev x ((strK (Xo := Xo) (c := c)).appTop.hom _) = _
    rw [← ev_comp, hx, ev_spec]
    exact congrArg i ((Scheme.ΓSpecIso (CommRingCat.of c.F)).inv_hom_id_apply k)
  let x : Sp ℂ ⟶ Xo.XF c := Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ genSp Z
  have hx : x ≫ strK = spMap j := by
    rw [Category.assoc, ← Spec.map_preimage (genSp Z ≫ strK), ← Spec.map_comp]
    congr 1
    ext k
    exact φ.commutes k
  have hev : ∀ f, ev x f = φ (((Xo.XF c).evaluation ⊤ (Formalism.L2.Pj.genPt Z) trivial).hom f) := ev_residue _ φ.toRingHom
  have hm := minpoly.monic hr
  obtain ⟨g, hg, -⟩ := exists_section Z (Formalism.L2.Pj.genPt Z)
    ((Z.2.1 : IsIrreducible (Z : Set (Xo.XF c))).isGenericPoint_genericPoint
      (isClosed_of_mem_irreducibleComponents _ Z.2)) ((minpoly c.F r₀).map κ) (hm.map _) r₀ (by
    apply φ.toRingHom.injective
    rw [Polynomial.hom_eval₂, ← (RingHom.ext hev : ev x = φ.toRingHom.comp _), Polynomial.eval₂_map, hκ x j hx, map_zero]
    exact (Polynomial.aeval_algHom_apply φ r₀ _).trans (by rw [minpoly.aeval, map_zero]))
  refine ⟨fnRule g, fnRule_mem g, ?_⟩
  show evR Xo c (fnRule g) (genFr h Z) = _
  rw [evR_fnRule, basePt_genFr, fnAt_comp]
  congr 1
  have e := congrArg (fun m => m.hom g) (ΓSpecIso_fromSpecResidueField (Formalism.L2.Pj.genPt Z))
  exact e.trans hg

theorem fnAlgClosed_of_card {σ : c.F →+* ℂ} (V : Unf Xo c σ r) (hσ : GoodEmb c σ) (hV : IsUnf V) (h : GenFrEx Xo c)
    (hone : ∀ k x, FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (V.un k x))
    (hgen : GenFromTest Xo c h) (hcard : Nat.card (Comp Xo c) = Fintype.card V.Comp) : FnAlgClosed Xo c := by
  classical
  have hlies : ∀ k : V.Comp, ∃ Z : Comp Xo c, ∀ x : (V.X k).dom, GlobalTheory.AllWt.LiesOn Z (V.un k x) :=
    GlobalTheory.UnifComp.exists_liesOn (Formalism.L2.PjFree.Unf.ofPj V) hV
  choose q hq using hlies
  have hsurj : Function.Surjective q := fun Z => by
    obtain ⟨k, hk⟩ := GlobalTheory.CompModel.exists_model (Formalism.L2.PjFree.Unf.ofPj V) hV h Z
    exact ⟨k, GlobalTheory.UnifComp.eq_of_carries hk (hq k)⟩
  have hfinC := CompFin.finite_comp Xo c
  have hfinV : Finite V.Comp := @Finite.of_fintype _ V.fin
  have hinj : Function.Injective q :=
    (hsurj.bijective_of_nat_card_le (by rw [hcard, Nat.card_eq_fintype_card])).1
  have hfin : FiniteDimensional ℚ c.F := c.fin
  have hcF : Countable c.F := Cardinal.mk_le_aleph0_iff.1 (by
    simpa [Cardinal.mkRat] using Algebra.IsAlgebraic.cardinalMk_le_max ℚ c.F)
  intro Z a ha
  by_contra hne
  have hk : Countable (kap Z) :=
    GlobalTheory.GenericReading.countable_of_fg_top ((GlobalTheory.Reg.kap_fg_trdeg E H Dw l Xo c).1 Z)
  have hO : Countable (Om Z) := GlobalTheory.GenericReading.countable_fractionRing_mvPolynomial _ _
  obtain ⟨φ₁, φ₂, hφ⟩ : ∃ φ₁ φ₂ : Om Z →ₐ[c.F] CAt σ, φ₁ a ≠ φ₂ a := exists_two_emb σ a ha hne
  obtain ⟨r₀, rfl⟩ := GlobalTheory.GeomIrr.mem_range_of_isAlgebraic_ratFun a (ha.tower_top (kap Z))
  have hr : IsIntegral c.F r₀ :=
    (isIntegral_algebraMap_iff (algebraMap (kap Z) (Om Z)).injective).1 ha.isIntegral
  obtain ⟨f, hf, hev⟩ := exists_fn h Z r₀ hr
  have hread := (GlobalTheory.GenericReading.embedding_read_at_frame E H Dw l Xo c σ r V hσ hV h Z).2
  have key : ∀ φ : Om Z →ₐ[c.F] CAt σ, ∃ (k : V.Comp) (x : (V.X k).dom), q k = Z ∧
      (∃ (φ' : Om Z →ₐ[c.F] CAt σ) (y' : FrPt Xo c (CAt σ)) (t : Ix Dw → (CAt σ)ˣ),
        FrMap φ' (genFr h Z) y' ∧ FrBor t (V.un k x) y') ∧
      rdU V f k x = toC (φ (evC h Z f)) := by
    intro φ
    obtain ⟨k, x, y', t, hm, hb⟩ := hread φ
    refine ⟨k, x, GlobalTheory.UnifComp.eq_of_carries (U := Formalism.L2.PjFree.Unf.ofPj V) ⟨φ, y', x, t, hm, hb⟩ (hq k),
      ⟨φ, y', t, hm, hb⟩, ?_⟩
    obtain ⟨w, hw0, hw⟩ := rdU_eq_of_reads' V h k Z x φ y' t hm hb 0 0
    have h1 := hw 1 one_mem_weight_zero_sections
    have e1 : evC h Z (1 : Rul Xo c) = 1 := map_one (evA (genFr h Z) (hgen Z))
    have e2 : rdU V (1 : Rul Xo c) k x = 1 := by
      rw [rdU_apply]
      exact congrArg toC (map_one (evA (V.un k x) (hone k x)))
    rw [e1, e2, map_one, mul_one] at h1
    have h2 := hw f hf
    rw [h1] at h2
    exact (one_mul _).symm.trans h2
  obtain ⟨k₁, x₁, hq₁, hc₁, hr₁⟩ := key φ₁
  obtain ⟨k₂, x₂, hq₂, hc₂, hr₂⟩ := key φ₂
  obtain rfl : k₁ = k₂ := hinj (hq₁.trans hq₂.symm)
  have hPf := aeval_mem_weight_zero_sections hf (minpoly c.F r₀)
  have hz : evC h Z (Polynomial.aeval f (minpoly c.F r₀)) = 0 := by
    show evA (genFr h Z) (hgen Z) (Polynomial.aeval f (minpoly c.F r₀)) = 0
    rw [← Polynomial.aeval_algHom_apply]
    show Polynomial.aeval (evC h Z f) (minpoly c.F r₀) = 0
    rw [hev, Polynomial.aeval_algebraMap_apply, minpoly.aeval, map_zero]
  have hvan := (GlobalTheory.evC_eq_zero_iff_rdU_eq_zero E H Dw l Xo c σ r V hσ hV h k₁ Z x₁ hc₁ 0 0 dom_zero _ hPf).1 hz
  have hP0 : (minpoly c.F r₀).map σ ≠ 0 := (Polynomial.map_ne_zero_iff σ.injective).2 (minpoly.ne_zero hr)
  have hroot : Set.MapsTo (rdU V f k₁) (V.X k₁).dom (((minpoly c.F r₀).map σ).roots.toFinset : Set ℂ) := by
    intro x hx
    have h0 := hvan x hx
    have e1 : rdU V f k₁ x = toC (evR Xo c f (V.un k₁ ⟨x, hx⟩)) := rdU_apply V f k₁ ⟨x, hx⟩
    have e2 : rdU V (Polynomial.aeval f (minpoly c.F r₀)) k₁ x =
        toC (evR Xo c (Polynomial.aeval f (minpoly c.F r₀)) (V.un k₁ ⟨x, hx⟩)) := rdU_apply V _ k₁ ⟨x, hx⟩
    rw [e2] at h0
    have e3 : Polynomial.aeval (evR Xo c f (V.un k₁ ⟨x, hx⟩)) (minpoly c.F r₀) = 0 :=
      (Polynomial.aeval_algHom_apply (evA (V.un k₁ ⟨x, hx⟩) (hone _ _)) f (minpoly c.F r₀)).trans h0
    rw [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hP0, Polynomial.IsRoot.def, Polynomial.eval_map, e1]
    exact e3
  have hcont : ContinuousOn (rdU V f k₁) (V.X k₁).dom :=
    (hV.2.2.2.2.1 0 0 dom_zero f hf k₁).1.continuousOn
  have hconn : IsPreconnected (V.X k₁).dom :=
    (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.flag_domain_frames_connected (E := E) r (V.X k₁)).isPreconnected
  have hdisc : IsDiscrete (((minpoly c.F r₀).map σ).roots.toFinset : Set ℂ) :=
    (Finset.finite_toSet _).isDiscrete
  have hconst := hconn.constant_of_mapsTo hdisc hcont hroot x₁.2 x₂.2
  rw [hr₁, hr₂, hev] at hconst
  exact hφ hconst

theorem over_unique {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {h : GenFrEx Xo c} {e : Comp Xo c → Rul Xo c}
    (hL : CompLaws U h e) {σ : c.F →+* ℂ} (hσ : GoodEmb c σ) {Z : Comp Xo c} {k k' : (U σ).Comp}
    (hk : Over (U σ) (e Z) k) (hk' : Over (U σ) (e Z) k') : k = k' := by
  have hF : FnAlgClosed Xo c :=
    fnAlgClosed_of_card (U c.F.val.toRingHom) rfl (hL.unf _ rfl) h (hL.unTest _ rfl) hL.genT hL.comps
  have hU := hL.unf σ hσ
  have key : ∀ k₁, Over (U σ) (e Z) k₁ → ∃ x : ((U σ).X k₁).dom, ∃ (φ : Om Z →ₐ[c.F] CAt σ)
      (y' : FrPt Xo c (CAt σ)) (t : Ix Dw → (CAt σ)ˣ), FrMap φ (genFr h Z) y' ∧ FrBor t ((U σ).un k₁ x) y' := by
    intro k₁ hk₁
    obtain ⟨Z', S, hS, hg⟩ := GlobalTheory.GenericFrames.exists_comp_generic_off_meagre E H Dw l Xo c σ r (U σ) hσ hU h k₁
    have hd : Dense (⋂ n, (S n)ᶜ) :=
      dense_iInter_of_isOpen (fun n => (hS n).1.isOpen_compl) fun n => interior_eq_empty_iff_dense_compl.1 (hS n).2
    obtain ⟨x, hx, hxS⟩ := hd.inter_open_nonempty _ (FourierCoefficientDomain.isOpen_dom _) (frames_nonempty' _)
    obtain ⟨φ, y₁, t, hm, hb⟩ := hg ⟨x, hx⟩ fun n hn => Set.mem_iInter.1 hxS n hn
    obtain rfl : Z' = Z := by
      by_contra hne
      obtain ⟨w, hw0, hw⟩ := rdU_eq_of_reads' (U σ) h k₁ Z' ⟨x, hx⟩ φ y₁ t hm hb 0 0
      have h1 := hw (e Z) (hL.e_sec Z)
      rw [hk₁ x hx, (hL.e_val Z).2 Z' hne, map_zero, mul_one] at h1
      exact hw0 h1
    exact ⟨⟨x, hx⟩, φ, y₁, t, hm, hb⟩
  obtain ⟨x, hx⟩ := key k hk
  obtain ⟨x', hx'⟩ := key k' hk'
  exact GlobalTheory.GeomConn.comp_eq_of_fnAlgClosed E H Dw l Xo c σ r (U σ) hσ hU hF h Z k k' x x' hx hx'

end GlobalTheory.CompanionTheory.Ar.Plug.ArchimedeanSections
