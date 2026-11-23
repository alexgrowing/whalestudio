import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatDegreeStatementOfDegreeTheorem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameCoord
import Development.AbelianVarietyTheory.Definitions.Divisors.VolMeasureOfAdd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameTangentVectorsOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpPullbackBasisLiftCompatible
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTanAtOfGenericFibre
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Formalism.LocalToGlobal.ProjectiveLattices.GenFrPfS
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.FlatDegreeCompare

private theorem basisAt_of_eigBasis {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {K : Type} [Field K] [Algebra c.F K]
    {x : Sp K ⟶ Xo.X} {t₀ : SAB H (Sp K)} (m1 : SABMap t₀ Xo.univ.t x) (ρ : E →+* ℂ)
    (v : Fin (Dw.mult ρ) → (epsR K ⟶ t₀.G))
    (hv : EigenvectorLieDegree.IsEigBasis t₀.act ((EigenvectorLieDegree.embIn c (algebraMap c.F K) ρ).comp (algebraMap (𝓞 E) E)) v) :
    EigenLatticeFrames.IsEigenBasisAt Xo c x ρ (fun i => (v i).left ≫ m1.φ) := by
  have h1 : IsGrpPullback t₀.G Xo.univ.t.G x m1.φ := m1.cart
  have key : ∀ w : epsR K ⟶ t₀.G, IsEigAt c ρ (w.left ≫ m1.φ) ↔
      ∀ a, (w ≫ t₀.act.act a).left = spMap (epsScaleR (algebraMap c.F K (embK c ρ a))) ≫ w.left := by
    intro w
    refine forall_congr' fun a => ?_
    have h := GlobalTheory.KSExist.FrameLift.eig_iff h1 (m1.act a) w (algebraMap c.F K (embK c ρ a))
    refine Iff.trans ?_ (h.trans ?_)
    · simp only [Category.assoc]
    · constructor
      · intro e
        rw [e, Over.comp_left, GlobalTheory.GrpTangent.epsScale_left]
      · intro e
        apply Over.OverMorphism.ext
        rw [e, Over.comp_left, GlobalTheory.GrpTangent.epsScale_left]
  refine ⟨fun i => (GlobalTheory.KSExist.FrameLift.tan_iff h1 (v i)).2 (hv.1 i).1, fun i => (key _).2 (hv.1 i).2,
    fun w hw he => ?_⟩
  obtain ⟨w', rfl⟩ := GlobalTheory.KSExist.FrameLift.exists_lift h1 (T := epsR K) w hw.1
  obtain ⟨a, ha, hu⟩ := hv.2 w' ⟨(GlobalTheory.KSExist.FrameLift.tan_iff h1 w').1 hw, (key _).1 he⟩
  exact ⟨a, GlobalTheory.LieBasisRing.isCombAt_of_isLieComb h1 v a w' ha,
    fun b hb => hu b (GlobalTheory.KSExist.FrameLift.isLieComb_of_isCombAt h1 v b w' hb)⟩

theorem UpperTheory.tangent_families_distinct_embeddings_independent :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [NumberField K] [Algebra c.F K] (x : Sp K ⟶ Xo.X), x ≫ Xo.s = sOf c K → ∀ (t₀ : SAB H (Sp K)) (m1 : SABMap t₀ Xo.univ.t x) (ρ ρ' : E →+* ℂ), ρ ≠ ρ' → ∀ (v : Fin (Dw.mult ρ) → (epsR K ⟶ t₀.G)) (v' : Fin (Dw.mult ρ') → (epsR K ⟶ t₀.G)), EigenvectorLieDegree.IsEigBasis t₀.act ((EigenvectorLieDegree.embIn c (algebraMap c.F K) ρ).comp (algebraMap (𝓞 E) E)) v → EigenvectorLieDegree.IsEigBasis t₀.act ((EigenvectorLieDegree.embIn c (algebraMap c.F K) ρ').comp (algebraMap (𝓞 E) E)) v' → ∃ y : FrPt Xo c K, y.x = x ∧ (∀ i, (v i).left ≫ m1.φ = y.u ρ i) ∧ ∀ i, (v' i).left ≫ m1.φ = y.u ρ' i := by
  intro E _ _ _ H Dw l Xo c K _ _ _ x hx t₀ m1 ρ ρ' hne v v' hv hv'
  classical
  choose u₀ hu₀ using fun τ => GlobalTheory.IntFramesCompare.exists_eigenBasisAt (c := c) hx τ
  obtain ⟨s, hs⟩ := gfp_gen GlobalTheory.abelianSchemeLaws_all.2.secTwist x
  obtain ⟨u, hu, e, e'⟩ : ∃ u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber K) ⟶ Xo.univ.t.G.left),
      (∀ τ, EigenLatticeFrames.IsEigenBasisAt Xo c x τ (u τ)) ∧ (u ρ = fun i => (v i).left ≫ m1.φ) ∧
        u ρ' = fun i => (v' i).left ≫ m1.φ := by
    refine ⟨Function.update (Function.update u₀ ρ fun i => (v i).left ≫ m1.φ) ρ' fun i => (v' i).left ≫ m1.φ,
      fun τ => ?_, ?_, ?_⟩
    · by_cases h' : τ = ρ'
      · subst h'
        rw [Function.update_self]
        exact basisAt_of_eigBasis m1 _ v' hv'
      · rw [Function.update_of_ne h']
        by_cases h : τ = ρ
        · subst h
          rw [Function.update_self]
          exact basisAt_of_eigBasis m1 _ v hv
        · rw [Function.update_of_ne h]
          exact hu₀ τ
    · rw [Function.update_of_ne hne, Function.update_self]
    · rw [Function.update_self]
  exact ⟨⟨x, hx, u, fun τ => (hu τ).1, fun τ => (hu τ).2.1, fun τ => (hu τ).2.2, s, hs⟩, rfl,
    fun i => (congrFun e i).symm, fun i => (congrFun e' i).symm⟩
