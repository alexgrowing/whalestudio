import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RatioOKOfRootOfUnity
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ActEqTranslate
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftLowestKTypeCompatibility
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultValueLeftContLevel
import Formalism.LocalToGlobal.IndefiniteReal.LiftGoodPartComplexEqRange

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TopLevelP

theorem toMap_shift {D : D7} {V : HSp D} (c : CoefA V) (hc : c.Is) {Dm : Type} [AddCommGroup Dm] [Module ℂ Dm]
    (pr : c.W →ₗ[ℂ] Dm →ₗ[ℂ] ℂ) (κ : GA D V) (hκ : κ ∈ GfC V) (a : ℂ) (ha : a ≠ 0)
    (f f' : Bridge.Gf V → c.W) (hy : ∀ h, f' h = a⁻¹ • f (h * (finHom V).rangeRestrict κ)) (v : Dm) (h : GA D V) :
    c.toMap pr f' v h = a⁻¹ * c.toMap pr f v (h * κ) := by
  have h1 := GlobalTheory.ThetaProjEquiv.ext_shift c hc κ hκ a ha f f' hy h
  show pr (c.ext f' h) v = a⁻¹ * pr (c.ext f (h * κ)) v
  rw [← h1, map_smul, Pi.smul_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel_left₀ ha]

theorem toMap_eigen {D : D7} {V : HSp D} (c : CoefA V) (hc : c.Is) {Dm : Type} [AddCommGroup Dm] [Module ℂ Dm]
    (pr : c.W →ₗ[ℂ] Dm →ₗ[ℂ] ℂ) (κ : GA D V) (hκ : κ ∈ GfC V) (a : ℂ) (ha : a ≠ 0) (b : ℂ)
    (f : Bridge.Gf V → c.W) (hy : ∀ h, (b • f) h = a⁻¹ • f (h * (finHom V).rangeRestrict κ)) (v : Dm) (h : GA D V) :
    a⁻¹ * c.toMap pr f v (h * κ) = b * c.toMap pr f v h :=
  (toMap_shift c hc pr κ hκ a ha f (b • f) hy v h).symm.trans
    (congrFun (LinearMap.congr_fun ((c.toMap pr).map_smul b f) v) h)

theorem mem_multT_withP {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S)
    (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) (P : LevelP L.Pg L.r ℂ) (u : SmT M →ₗ[ℂ] (GA D V → ℂ))
    (hu : u ∈ MultT θ M (levS V β (flag1L L)) (levChi V β (flag1L L)))
    (hP : ∀ p : P.H, ∃ κ, IsLevelLift V β L p.1 κ ∧ ∀ v h,
      (levChi V β (flagL L) κ)⁻¹ * u v (h * κ) = ((P.chi p : ℂˣ) : ℂ) * u v h) :
    u ∈ MultT θ M (levS V β (withP L P)) (levChi V β (withP L P)) := by
  have hm := (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).1 ((mem_multT _ _ _ _ _).1 hu)
  rw [mem_multT, GlobalTheory.MultMem.mem_mult_iff]
  refine ⟨hm.aut, hm.cusp, fun v k hk g => ?_, hm.equiv, hm.cont⟩
  have hT : HasType V β (flag1L L) (PiTensorProduct.lift.symm u v) := fun k hk g => hm.lev v k hk g
  refine IsPLevel.hasType (V := V) (β := β) (L := L) (P := P) ⟨hT, fun p => ?_⟩ k hk g
  obtain ⟨κ, hl, hκ⟩ := hP p
  funext h
  exact (level_action_spec hT ⟨κ, hl⟩ κ hl h).trans (hκ (PiTensorProduct.tprod ℂ v) h)

section Package

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

theorem exists_lift_eigen (hred : R.grp_red_R) (hj : R.models_jX) (hc : R.models_cX) (t : T0) (g : G)
    (x : (A.fam.R t).S.Forms) (a : D.what₂.LL) (hx : (A.fam.R t).r g x = a • x) :
    ∃ κ, IsLevelLift D.sp.X' R.βX (R.datXt t) (R.eG g) κ ∧ ∀ v h,
      (levChi D.sp.X' R.βX (flagL (R.datXt t)) κ)⁻¹ * R.cX.toMap R.prX ((R.HX t).e (R.jX t x)) v (h * κ) =
        D.what₂.embLL a * R.cX.toMap R.prX ((R.HX t).e (R.jX t x)) v h := by
  refine (GlobalTheory.FormAction.act_eq_translate R hred hj t g x).imp fun κ hκ => ⟨hκ.1, ?_⟩
  have h3 : R.jX t ((A.fam.R t).r g x) = D.what₂.embLL a • R.jX t x :=
    (congrArg (R.jX t) hx).trans ((R.jX t).map_smulₛₗ a x)
  have h4 : (R.HX t).e (R.jX t ((A.fam.R t).r g x)) = D.what₂.embLL a • (R.HX t).e (R.jX t x) :=
    (congrArg (R.HX t).e h3).trans ((R.HX t).e.map_smul _ _)
  exact toMap_eigen R.cX hc R.prX κ hκ.1.1 _ (levChi_ne_zero (V := D.sp.X') (β := R.βX) (flagL (R.datXt t)) κ) _ _
    fun h => (congrFun h4 h).symm.trans (hκ.2 h)

theorem mem_CXP_of_good (hred : R.grp_red_R) (hj : R.models_jX) (hc : R.models_cX) (hirr : ∀ χ ∈ A.fam.X, IsAbsIrrChar χ)
    (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (t : T0) (x : (A.fam.R t).S.Forms)
    (hx : x ∈ Formalism.IndefR.Cx.BlockGood.goodR (A.fam.R t) (A.fam.lvl P ψ))
    (hu : R.cX.toMap R.prX ((R.HX t).e (R.jX t x)) ∈
      MultT R.θ R.MX (levS _ R.βX (R.datXt t)) (levChi _ R.βX (R.datXt t))) :
    R.cX.toMap R.prX ((R.HX t).e (R.jX t x)) ∈ CXP R (levPOf R.eG D.what₂.embLL P ψ) t := by
  rw [Formalism.IndefR.CxPass.LevelOperators.goodR_eq] at hx
  refine mem_multT_withP R.θ R.MX R.βX (R.datXt t) (levPOf R.eG D.what₂.embLL P ψ) _ hu fun p => ?_
  have hq : R.eG.symm p.1 ∈ P := p.2
  have ha := Formalism.IndefR.CxPass.LevelOperators.opF_goodAt_type (A.fam.R t).r A.fam.X hirr P ψ ⟨_, hq⟩ x hx
  refine (exists_lift_eigen R hred hj hc t (R.eG.symm p.1) x _ ha).imp fun κ hκ => ⟨?_, hκ.2⟩
  exact ⟨hκ.1.1, hκ.1.2.1, hκ.1.2.2.trans (R.eG.apply_symm_apply p.1)⟩

end Package

theorem topOf_mem_CXP : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), PkHyp W → ∀ t (F : Fin ((W.Q.F.fc (cxW W).zs).Df1.nV t) → D.what₂.LL), topOf W t F ∈ CXP (pk W) (lvP W) t := by
  intro D L hT Gi Gl Kc Yd cX ex W hP t F
  obtain ⟨-, -, -, hC, -⟩ := hP.bot.hyp
  obtain ⟨⟨s, hs⟩, -⟩ := hP.lev
  exact mem_CXP_of_good (pk W) hC.grp.red_R hC.models.jX hC.models.cX hs.ok2.irr W.Q.F.P1 W.Q.F.ψ1 t
    (W.Q.F.eV (cxW W).zs t F) ⟨F, rfl⟩ ((hP.hTop t).le ⟨_, rfl⟩)

end GlobalTheory.TopLevelP

end
