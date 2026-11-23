import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.ExistsSecTieFOfTies
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Formalism.LocalToGlobal.ProjectiveLattices.ConjNeSelfOfCM
import Formalism.LocalToGlobal.ProjectiveLattices.BetaAtSymm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGenFam
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsGeneratorOfBasis
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IntegralOfPullAl
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PowGerm GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.ThetaFrameLine

section
variable {V : Type} [CommRing V] [IsDomain V]

theorem cst_prB (D : DegPre V) (F : Type) [Field F] [Algebra (FractionRing V) F] (y : (DegPre.BF D F).left) (a : V) :
    Geo.Tor.cst ((𝟙 _ ≫ (DegPre.prB D F).left) ≫ D.P.A.hom) y a =
      gs (𝟙 _) y ⊤ (gF D F (algebraMap (FractionRing V) F (algebraMap V (FractionRing V) a))) := by
  have hw : (DegPre.prB D F).left ≫ D.P.A.hom = (fst (TF (R := V) F) D.P.A).left ≫ jFK (R := V) F ≫ jK V :=
    (Over.w (DegPre.prB D F)).trans (Over.w (fst (TF (R := V) F) D.P.A)).symm
  have e : (jFK (R := V) F ≫ jK V).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom a) =
      (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom
        (algebraMap (FractionRing V) F (algebraMap V (FractionRing V) a)) := by
    have h := Scheme.ΓSpecIso_inv_naturality
      (CommRingCat.ofHom ((algebraMap (FractionRing V) F).comp (algebraMap V (FractionRing V))))
    have h' := congrArg (fun f => f.hom a) h
    rw [jFK, jK, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact h'.symm
  rw [Category.assoc, hw, Geo.Tor.cst]
  refine (gs_pull (𝟙 _) _ y ⊤ trivial _).symm.trans (congrArg (gs (𝟙 _) y ⊤) ?_)
  exact congrArg (fst (TF (R := V) F) D.P.A).left.appTop.hom e

end

theorem main : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] (ϖ : V), Irreducible ϖ → ∀ (D : DegData V (maximalIdeal V)) (F : Type) [Field F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → ∀ θ θ' : Fam D.toPre F 1, ThFrame D ϖ F θ → ThFrame D ϖ F θ' → ∃ u : F, v u = 0 ∧ Fam.IsSmul D.toPre F u θ θ' := by
  intro V _ _ _ _ ϖ hϖ D F _ _ v hv θ θ' h h'
  obtain ⟨σ, σF, hs, he, hn⟩ := h
  obtain ⟨τ, τF, ht, hf, hm⟩ := h'
  have hL := D.toPre.P.isLB
  have gσ := GlobalTheory.IndivisibleSection.secBGenerates_of_not_dvd GlobalTheory.firstFiveLaws.1.secBaseChange V ϖ hϖ D σ hn
  obtain ⟨a, ha, -⟩ := gσ τ
  have hu : IsUnit a := by
    by_contra hna
    have hmem : a ∈ maximalIdeal V := hna
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.mem_span_singleton] at hmem
    obtain ⟨b, rfl⟩ := hmem
    refine hm ⟨SecOps.secScale (Out.scal D.toPre.P.A.hom b) σ, ?_⟩
    show SecIsMul D.toPre.P.A.hom ϖ τ (SecOps.secScale (Out.scal D.toPre.P.A.hom b) σ)
    intro j
    refine (ha j).trans ?_
    simp only [SecOps.secScale, Out.scal, resTop, map_mul, _root_.mul_assoc]
  refine ⟨algebraMap (FractionRing V) F (algebraMap V (FractionRing V) a), ?_, ?_⟩
  · have := hv (algebraMap V (FractionRing V) a) 0 ⟨hu.unit, by simp⟩
    simpa using this
  · set u := algebraMap (FractionRing V) F (algebraMap V (FractionRing V) a) with hudef
    have eθ : θ.s 0 = σF := SecOps.sec_ext he
    have eθ' : θ'.s 0 = τF := SecOps.sec_ext hf
    have h0 : ∀ j, (θ'.s 0).f j = ((u • θ).s 0).f j := by
      refine sec_ext_val hL fun y J hJ => ?_
      have e₁ := GlobalTheory.PullIntegral.sval_of_secScal hs (𝟙 _) y hJ
      have e₂ := GlobalTheory.PullIntegral.sval_of_secScal ht (𝟙 _) y hJ
      have e₃ := GlobalTheory.IndivisibleSection.sval_of_secIsMul ha (𝟙 _ ≫ (DegPre.prB D.toPre F).left) y hJ
      have o : gs (𝟙 (DegPre.BF D.toPre F).left) y ⊤ 1 = 1 := by
        rw [gs_eq _ y ⊤ trivial, map_one, map_one]
      rw [o, _root_.one_mul] at e₁ e₂
      rw [e₁, e₂, cst_prB, ← eθ, ← eθ'] at e₃
      refine e₃.trans ?_
      have hmem := hJ.mem (DegPre.famφ D.toPre F 0) (𝟙 _)
      exact ((gs_mul (𝟙 _) y _ hmem _ _).trans (congrArg₂ (· * ·) (gs_res (𝟙 _) y le_top hmem _) rfl)).symm
    refine (isSmul_iff u θ θ').2 (sub_eq_zero.1 (fam_ext fun α j => TG.fam_eq_zero hϖ (θ' - u • θ) (fun j => ?_) α j))
    exact (congrArg (· + -((u • θ).s 0).f j) (h0 j)).trans (add_neg_cancel _)

end GlobalTheory.ThetaFrameLine
