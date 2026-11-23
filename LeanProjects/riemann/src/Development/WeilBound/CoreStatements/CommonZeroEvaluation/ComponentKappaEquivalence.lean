import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GeoRead
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.NefRR
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ModelSmall
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.VolumeInputs
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.OverLaUnique
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginGenericFrame
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianMapLieModelFieldPoint
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianMapLieModelEigenFrameStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericLuDecompositionUnique
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LuFactorsGenerateSameField
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AlgIndepOfSameAdjoin
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericFlagTriangularChange
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FramePointBorelSectionScaling
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginComponentGenericPoint
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.FrameNormsContinuousAlongEmbeddingFamilies
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.FrMapComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ExpBCChart
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TowerComponentsCompatibleLaws

open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi
open AlgebraicGeometry CategoryTheory Limits
open scoped Matrix

namespace ModelDimension

theorem component_kappa_equivalence : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Z : Comp Xo c) (ψ : kap Z ≃+* Or.𝔐.Ω₀), spMap ψ.toRingHom ≫ genSp Z ≫ Y.j = Or.𝔐.ξ₀ → ∀ (y₀ : FrPt Xo c (kap Z)), y₀.x = xGen Z → letI := Small.cstAlg Or; ∀ (χ : kap Z →ₐ[c.F] RM.Ω) (y₂ : FrPt Xo c RM.Ω), χ.toRingHom = Or.𝔐.fn.comp ψ.toRingHom → FrMap χ y₀ y₂ → Small.ptY Y y₂ = Or.𝔐.ξ ≫ Or.𝔐.f ∧ ∀ s, ∃ e : Fin (labelRk Dw s) → Or.Fl.Li₀, (∀ k, e k ∈ Or.Fl.V₀ s) ∧ (LinearIndependent RM.Ω fun k => Or.Fl.j (e k)) ∧ ∀ k, (Or.𝔐.M.pt (Or.Fl.j (e k))).left ≫ Or.𝔐.m.φ = Small.tanY Y y₂ (Small.labelC s) (Small.labelFin Dw s k) := by
  intro E _ _ _ H Dw l Xo c Y SS RM Sys Fx Or Z ψ hψ y₀ hy₀
  letI algΩ := Small.cstAlg Or
  intro χ y₂ hχ hFr
  have hc : ∀ a : c.F, Or.𝔐.fn (ψ (algebraMap c.F (kap Z) a)) = Or.𝔐.cst a := fun a =>
    (RingHom.congr_fun hχ _).symm.trans (χ.commutes a)
  have hp0 : Small.ptF y₀ = genSp Z := by
    apply pullback.hom_ext
    · rw [Small.ptF_fst, hy₀]; rfl
    · rw [Small.ptF_snd]; exact Spec.map_preimage _
  have hpt : Small.ptY Y y₂ = Or.𝔐.ξ ≫ Or.𝔐.f := by
    have hfn : Or.𝔐.ξ ≫ Or.𝔐.f = spMap Or.𝔐.fn ≫ Or.𝔐.ξ₀ := Or.𝔐.fn_over
    rw [Small.ptY_map Y hFr, hfn, ← hψ, hχ, ← ReadEx.spc, Small.ptY, hp0, Category.assoc]
  refine ⟨hpt, fun s => ?_⟩
  obtain ⟨Fr⟩ := GlobalTheory.CompanionTheory.Ar.GenEx.exists_genFrame Or
  have hpF : Small.ptF y₂ = Small.ptF Fr.y₀ := Small.ptF_eq_of_ptY_eq Y (hpt.trans Fr.pt_eq.symm)
  letI alg₀ : Algebra c.F Or.𝔐.Ω₀ := ((ψ.toRingHom).comp (algebraMap c.F (kap Z))).toAlgebra
  let ψA : kap Z →ₐ[c.F] Or.𝔐.Ω₀ := { ψ.toRingHom with commutes' := fun _ => rfl }
  obtain ⟨y₁, h₁⟩ := GlobalTheory.FrameNorm.exists_frMap_along ψA y₀
  have hz₀ : Small.ptF y₁ ≫ Y.j = Or.𝔐.ξ₀ := by
    rw [Small.ptF_map h₁, hp0, Category.assoc]; exact hψ
  have hx₂ : y₂.x = Fr.y₀.x := by
    rw [← Small.ptF_fst y₂, hpF, Small.ptF_fst]
  obtain ⟨M₁, e₁⟩ := (GlobalTheory.CompanionTheory.Ar.LiePull.lieModel_pullback _ _ _ _ _ _ Or.𝔐.m.cart RM.Ω Or.𝔐.ξ Or.𝔐.Li).2 Or.𝔐.M
  obtain ⟨N, hN, hNa⟩ := ReadEx.exists_univ_model Y (Small.ptF Fr.y₀) Fr.pt_eq M₁ (Small.ptF_fst Fr.y₀)
  obtain ⟨N₀, hN₀, -⟩ := ReadEx.exists_univ_model Y (Small.ptF y₁) hz₀ Or.Fl.M₀ (Small.ptF_fst y₁)
  have hex : ∀ τ k, ∃ e, (N₀.pt e).left = y₁.u τ k := fun τ k => ReadEx.exists_pt N₀ (y₁.tan τ k)
  choose ec hec using hex
  have hM₀ : ∀ τ k, Small.tanY Y y₁ τ k = (Or.Fl.M₀.pt (ec τ k)).left := fun τ k =>
    (ReadEx.pt_eq_u_iff Y y₁ rfl hN₀ τ k _).1 (hec τ k)
  have hcomp : spMap (GlobalTheory.CompanionTheory.Ar.dualMap χ.toRingHom) =
      spMap (GlobalTheory.CompanionTheory.Ar.dualMap Or.𝔐.fn) ≫ spMap (GlobalTheory.CompanionTheory.Ar.dualMap ψA.toRingHom) := by
    rw [ReadEx.spc, hχ]
    exact congrArg spMap (ReadEx.dualMap_comp₂ ψ.toRingHom Or.𝔐.fn)
  have ht : ∀ τ k, (Or.𝔐.M.pt (Or.Fl.j (ec τ k))).left ≫ Or.𝔐.m.φ = Small.tanY Y y₂ τ k := fun τ k => by
    rw [Or.Fl.j_pt, ← hM₀, Small.tanY_map Y h₁, Small.tanY_map Y hFr, hcomp, Category.assoc]
  have hy₂ : ∀ τ k, (N.pt (Or.Fl.j (ec τ k))).left = y₂.u τ k := fun τ k =>
    (ReadEx.pt_eq_u_iff Y y₂ hpF hN τ k _).2 ((ht τ k).symm.trans (e₁ _))
  refine ⟨fun k => ec (Small.labelC s) (Small.labelFin Dw s k), fun k => ?_,
    (ReadEx.indep_of_basis y₂ hx₂ N _ _ (hy₂ (Small.labelC s))).comp (Small.labelFin Dw s) (Fin.cast_injective (Small.mult_labelC Dw s).symm),
    fun k => ht _ _⟩
  refine (Or.Fl.V₀_mem s _).2 ?_
  have hρ : ∀ (a : 𝓞 E) (e : Or.𝔐.Li), (M₁.pt (Or.𝔐.ρ a e)).left = (M₁.pt e).left ≫ (Y.t.act.act a).left := fun a e => by
    rw [← e₁, ← e₁, Or.𝔐.act a e, CategoryTheory.Over.comp_left, Category.assoc, Or.𝔐.m.act, Category.assoc]
  have hact := hNa (fun a e => Or.𝔐.ρ a e) hρ
  show _ ∈ eigSp Or.𝔐.ρ (Or.𝔐.emb s)
  simp only [eigSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
  intro a
  apply N.inj
  apply CategoryTheory.Over.OverMorphism.ext
  have h3 := y₂.eig (Small.labelC s) (Small.labelFin Dw s k) a
  rw [hact a, hy₂, h3, LinearMap.smul_apply, LinearMap.id_apply, N.smul, hy₂, Small.embK_labelC]
  rfl

end ModelDimension
