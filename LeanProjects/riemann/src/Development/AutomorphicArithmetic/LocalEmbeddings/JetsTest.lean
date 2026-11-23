import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.JetsGlue
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsRealFnNeZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRealModelSq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspidalListedTopForms
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselPeriodCorankConvergesColumn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsFunForm

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.DefStep
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsOpenCompactLevel IsDefiniteSpace)
open scoped ComplexOrder Topology

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.JetsOne

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem fp_eq (V : HSp D) (g : GA D V) : GlobalTheory.IndefiniteRowSideFullHecke.BasisPolynomialParabolics.fp V g = finOf V g :=
  ClassFin.finG_injective V ((GlobalTheory.SuppLevO.finE_finPartG V g).trans (finG_finOf V g).symm)

theorem frame_real {L : LevCh D T} {sc : Consts} {G : GridData L sc} {U : Set T} (θ : InfFam D) (N : Std G U) (X : Node)
    (g : GA D (G.V X)) (v : VV ℂ (wt G X)) :
    rhoVr (tauE D) (wt G X) (N.fr X) (realAct θ N.fr X g (rhoVr (tauE D) (wt G X) (N.fr X)⁻¹ v)) =
      rhoK (wt G X) (invTrK (GlobalTheory.CoefModel.realGL θ (G.V X) g)) v := by
  have e' : realAct θ N.fr X = GlobalTheory.RealType.rhoAt θ N X := rfl
  rw [e', GlobalTheory.RealType.rhoVr_rhoAt, ← Module.End.mul_apply (rhoVr _ _ _), ← map_mul, mul_inv_cancel, map_one,
    Module.End.one_apply, GlobalTheory.RealType.rhoFr_one]

theorem col_real (ch : Choice R) : ∃ Λ : Module.Dual ℂ (VV ℂ (wt ch.G (.top 0))), ∀ a,
    IsFinReal (realAct ch.W.θ ch.S.N.fr (.top 0)) (colFn ch a) Λ
      fun x => rhoVr (tauE D) _ (ch.S.N.fr (.top 0))⁻¹ (psiC (ch.Psi a) x) := by
  obtain ⟨Λ, h⟩ := RealTypeOf.colFn_realType ch
  refine ⟨Λ ∘ₗ rhoVr (tauE D) _ (ch.S.N.fr (.top 0)), fun a g => ?_⟩
  rw [h, fp_eq, LinearMap.comp_apply, frame_real]

theorem form_real (ch : Choice R) (hc : R.cX.Is) : ∃ Λ : Module.Dual ℂ (VV ℂ (wt ch.G (.grid 0 D.R.m))), ∀ t y,
    IsFinReal (realAct ch.W.θ ch.S.N.fr (.grid 0 D.R.m)) (formTop ch t y) Λ
      fun x => rhoVr (tauE D) (wt ch.G (.grid 0 D.R.m)) (ch.S.N.fr (.grid 0 D.R.m))⁻¹
        (funOf (listedWt ch.G (.grid 0 D.R.m)) (ch.S.formC t y x)) := by
  obtain ⟨Λ, h⟩ := RealTypeOf.formTop_realType ch hc
  let φ := GlobalTheory.FunObj.funEquiv (K := ℂ) (listedWt ch.G (.grid 0 D.R.m))
  have hφ : ∀ F, funOf (listedWt ch.G (.grid 0 D.R.m)) F = φ F := fun F =>
    (GlobalTheory.FunObj.isFunForm_iff_eq _ _ _).1 ((readOK_of_equiv _ φ (GlobalTheory.FunObj.isFunForm_funEquiv _)).1 F)
  refine ⟨Λ ∘ₗ φ.symm.toLinearMap ∘ₗ rhoVr (tauE D) (wt ch.G (.grid 0 D.R.m)) (ch.S.N.fr (.grid 0 D.R.m)), fun t y g => ?_⟩
  rw [h, fp_eq]
  have e1 := frame_real ch.W.θ ch.S.N (.grid 0 D.R.m) g⁻¹
    (funOf (listedWt ch.G (.grid 0 D.R.m)) (ch.S.formC t y (finOf _ g)))
  have e2 := GlobalTheory.FunObj.funEquiv_rhoK (K := ℂ) (listedWt ch.G (.grid 0 D.R.m))
    (GlobalTheory.CoefModel.realGL ch.W.θ (ch.G.V (.grid 0 D.R.m)) g⁻¹) (ch.S.formC t y (finOf _ g))
  have e3 := e2.trans ((congrArg _ (hφ _).symm).trans e1.symm)
  exact congrArg Λ ((φ.symm_apply_apply _).symm.trans (congrArg φ.symm e3))

theorem psiC_right (ch : Choice R) (a : Fin ch.n) (x k : FinPt ch.G (.top 0)) (hk : finG (ch.G.V (.top 0)) k ∈ ch.G.Kplus) :
    psiC (ch.Psi a) (x * k) = psiC (ch.Psi a) x := by
  have e : ch.Psi a (finG (Xp ch.G) (x * k)) = ch.Psi a (finG (Xp ch.G) x) := by
    rw [show finG (Xp ch.G) (x * k) = finG (Xp ch.G) x * finG (Xp ch.G) k from map_mul _ _ _]
    exact psi_right _ _ a _ hk
  exact Subtype.ext (congrArg (fun z => (GlobalTheory.CoefModel.mapVV D.what₂.embLL (LaP ch.G) z).1) e)

theorem col_left (ch : Choice R) (a : Fin ch.n) : ∀ γ ∈ GQ (ch.G.V (.top 0)), ∀ g, colFn ch a (γ * g) = colFn ch a g :=
  fun γ hγ g => GlobalTheory.RowBplus.pairVec_left ch.G ch.W.θ ch.ξ (col_mem ch a) hγ g

theorem real_right {V : HSp D} {M : Type} [AddCommGroup M] [Module ℂ M] {ρ : GA D V →* Module.End ℂ M}
    (hρ : ∀ g ∈ GfC V, ρ g = 1) {F : GA D V → ℂ} {Λ : Module.Dual ℂ M} {v : GfC V → M} (h : IsFinReal ρ F Λ v)
    (k : GfC V) (hk : ∀ x, v (x * k) = v x) (g : GA D V) : F (g * k) = F g := by
  rw [h, h, finOf_mul_fin, hk, mul_inv_rev, map_mul, hρ _ (inv_mem k.2), one_mul]

theorem col_fix (ch : Choice R) (a : Fin ch.n) (hK : IsOpenCompactLevel (ch.G.V (.top 0)) ch.G.Kplus) :
    ∀ᶠ k in 𝓝 (1 : GA D (ch.G.V (.top 0))), k ∈ GfC _ → ∀ g, colFn ch a (g * k) = colFn ch a g := by
  obtain ⟨Λ, h⟩ := col_real ch
  filter_upwards [hK.1.mem_nhds (one_mem _)] with k hk hf g
  exact real_right (fun g hg => realAct_fin _ _ _ hg) (h a) ⟨k, hf⟩ (fun x => congrArg _ (psiC_right ch a x ⟨k, hf⟩ hk)) g

theorem aut_cast' {Λ : Submodule (𝓞 D.host.E) (Fin D.sp.X'.rank → D.host.E)} (X : LSp D) (h : X = ⟨D.sp.X', Λ⟩)
    (φ : GA D D.sp.X' → ℂ) (hφ : IsAutFun D.sp.X' φ) :
    IsAutFun X.sp (fun g => φ (cast (congrArg (fun X : LSp D => GA D X.sp) h) g)) := by
  subst h
  exact hφ

theorem form_aut {large₂ : SizeData₂ D} {F : Face D A} (hS : HidaSetting large₂ R F) (ch : Choice R) (t : T) (y : (R.HX t).H) :
    (∀ γ ∈ GQ (ch.G.V (.grid 0 D.R.m)), ∀ g, formTop ch t y (γ * g) = formTop ch t y g) ∧
    ∀ᶠ k in 𝓝 (1 : GA D (ch.G.V (.grid 0 D.R.m))), k ∈ GfC _ → ∀ g, formTop ch t y (g * k) = formTop ch t y g := by
  have hm := hS.core.models
  obtain ⟨h1, -, -⟩ := GlobalTheory.EndCusp.formX_props R hm.inf hm.cX hm.prX hm.HX ch.cv t y
  have k := aut_cast' (columnBlock R.toLevCh D.R.m) (colY_m R.toLevCh) (ch.cv.formX t y) h1.toIsAutFun
  obtain ⟨U, hU, e⟩ := k.level
  refine ⟨k.left, ?_⟩
  filter_upwards [hU.mem_nhds (one_mem _)] with z hz using e z hz

end GlobalTheory.JetsOne

end
