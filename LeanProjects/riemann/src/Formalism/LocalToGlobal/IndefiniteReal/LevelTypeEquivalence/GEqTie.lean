import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.ThFEquivOf
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.MemBlockTriangularTwoBlockSizesOfLe
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.ContinuousSplitInv

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open scoped TensorProduct InnerProductSpace

namespace Formalism.IndefR.Eqv.Act

open Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Links.RealDat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Lift

variable {D : D7} (V : HSp D)

theorem thetaC_inj {y y' : Ainf D.host.F ⊗[D.host.F] D.host.E} (h : ∀ τ, thetaC D τ y = thetaC D τ y') : y = y' :=
  (splitEquiv D).injective (funext h)

theorem infHom_infOnly (h : GA D V) : infHom V (infOnly D V h) = infHom V h := by
  apply Units.ext
  funext i j
  show infPart D (matA D V (infOnly D V h) i j) = infPart D (matA D V h i j)
  apply thetaC_inj
  intro τ
  have e := congrFun (congrFun (infMat_infOnly D V h τ) i) j
  rw [infMat_thetaC, infMat_thetaC] at e
  exact e

theorem exists_finLift (q : Bridge.Gf V) : ∃ κ ∈ GfC V, finHom V κ = q := by
  obtain ⟨κ0, hκ0⟩ := q.2
  refine ⟨(infOnly D V κ0)⁻¹ * κ0, ?_, ?_⟩
  · show infHom V ((infOnly D V κ0)⁻¹ * κ0) = 1
    rw [map_mul, map_inv, infHom_infOnly, inv_mul_cancel]
  · have h1 : finHom V (infOnly D V κ0) = 1 := infOnly_mem_GinfC D V κ0
    rw [map_mul, map_inv, h1, inv_one, one_mul, hκ0]

end Lift

section Ad

variable {G Γ W : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] (ι : Γ →* G)

theorem mem_adForms_iff (ρ : Γ →* Module.End ℂ W) (J : Subgroup G) (χ : J →* ℂˣ) (F : G → W) :
    F ∈ Bridge.AdForms ι ρ J χ ↔ ∀ (γ : Γ) (h : G) (k : J), F (ι γ * h * k) = (χ k : ℂ) • ρ γ (F h) := Iff.rfl

end Ad

section Coef

variable {D : D7} {V : HSp D} (c : CoefA V)

theorem coefExt_mul (hc : c.Is) (f : Bridge.Gf V → c.W) (h κ : GA D V) (hκ : κ ∈ GfC V) :
    c.ext f (h * κ) = c.ρ h⁻¹ (f ((finHom V).rangeRestrict h * (finHom V).rangeRestrict κ)) := by
  have e1 : (finHom V).rangeRestrict (h * κ) = (finHom V).rangeRestrict h * (finHom V).rangeRestrict κ := map_mul _ _ _
  have e2 : c.ρ (h * κ)⁻¹ = c.ρ h⁻¹ := by
    rw [_root_.mul_inv_rev, map_mul, hc.1 _ (Subgroup.inv_mem _ hκ), one_mul]
  exact congrArg₂ (fun (L : Module.End ℂ c.W) z => L (f z)) e2 e1

theorem toMap_g0Act (hc : c.Is) {Dm : Type} [AddCommGroup Dm] [Module ℂ Dm] (pr : c.W →ₗ[ℂ] Dm →ₗ[ℂ] ℂ)
    {Q : Subgroup (Bridge.Gf V)} (ch : Q →* ℂˣ) (q : Q) (κ : GA D V) (hκ : κ ∈ GfC V)
    (hκq : (finHom V).rangeRestrict κ = q) (F : Bridge.Gf V → c.W) (v : Dm) (h : GA D V) :
    c.toMap pr (Bridge.g0Act ch q F) v h = ((ch q : ℂˣ) : ℂ)⁻¹ * c.toMap pr F v (h * κ) := by
  have e : c.toMap pr (Bridge.g0Act ch q F) v h =
      pr (c.ρ h⁻¹ ((((ch q)⁻¹ : ℂˣ) : ℂ) • F ((finHom V).rangeRestrict h * q))) v := rfl
  have e2 : c.ρ h⁻¹ ((((ch q)⁻¹ : ℂˣ) : ℂ) • F ((finHom V).rangeRestrict h * q)) =
      (((ch q)⁻¹ : ℂˣ) : ℂ) • c.ρ h⁻¹ (F ((finHom V).rangeRestrict h * q)) := LinearMap.map_smul _ _ _
  have e3 : pr ((((ch q)⁻¹ : ℂˣ) : ℂ) • c.ρ h⁻¹ (F ((finHom V).rangeRestrict h * q))) =
      (((ch q)⁻¹ : ℂˣ) : ℂ) • pr (c.ρ h⁻¹ (F ((finHom V).rangeRestrict h * q))) := LinearMap.map_smul _ _ _
  have e4 : (((ch q)⁻¹ : ℂˣ) : ℂ) = ((ch q : ℂˣ) : ℂ)⁻¹ := Units.val_inv_eq_inv_val (ch q)
  have e5 := coefExt_mul c hc F h κ hκ
  have e6 : c.ext F (h * κ) = c.ρ h⁻¹ (F ((finHom V).rangeRestrict h * q)) := hκq ▸ e5
  have s1 : pr (c.ρ h⁻¹ ((((ch q)⁻¹ : ℂˣ) : ℂ) • F ((finHom V).rangeRestrict h * q))) v =
      (((ch q)⁻¹ : ℂˣ) : ℂ) * pr (c.ρ h⁻¹ (F ((finHom V).rangeRestrict h * q))) v :=
    (congrArg (fun L : Dm →ₗ[ℂ] ℂ => L v) ((congrArg pr e2).trans e3)).trans (LinearMap.smul_apply _ _ _)
  have s2 : (((ch q)⁻¹ : ℂˣ) : ℂ) * pr (c.ρ h⁻¹ (F ((finHom V).rangeRestrict h * q))) v =
      ((ch q : ℂˣ) : ℂ)⁻¹ * c.toMap pr F v (h * κ) :=
    congrArg₂ (· * ·) e4 (congrArg (fun w => pr w v) e6.symm)
  exact e.trans (s1.trans s2)

end Coef

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

theorem lift_X (hred : R.grp_red_R) (t : T) (g : G) : ∃ κ, IsLevelLift D.sp.X' R.βX (R.datXt t) (R.eG g) κ := by
  obtain ⟨q1, hq1⟩ := (R.B.R t).act_tie.red_surj g
  obtain ⟨κ1, hκ1f, hκ1q⟩ := exists_finLift D.sp.X' (q1 : Bridge.Gf D.sp.X')
  have hq : finE D.sp.X' κ1 ∈ lev D.sp.cm D.sp.X'.gram R.βX (flagL (R.datXt t)) := by
    rw [finE_eq, hκ1q]; exact q1.2
  refine ⟨κ1, hκ1f, hq.1, ?_⟩
  rw [finE_eq, hκ1q, ← hred t q1, hq1]

theorem mem_Q_of_lift (t : T) (g : G) {κ0 : GA D D.sp.X'} (hκ0 : IsLevelLift D.sp.X' R.βX (R.datXt t) (R.eG g) κ0) :
    (finHom D.sp.X').rangeRestrict κ0 ∈ (levEnv D.sp.X' R.βX (R.datXt t)).Q := by
  show Formalism.UG.bc (swapAE D) (finHom D.sp.X' κ0) ∈ lev D.sp.cm D.sp.X'.gram R.βX (flagL (R.datXt t))
  rw [← finE_eq]
  exact ⟨hκ0.2.1, Subgroup.mem_top _⟩

theorem red_of_lift (hred : R.grp_red_R) (t : T) (g : G) {κ0 : GA D D.sp.X'}
    (hκ0 : IsLevelLift D.sp.X' R.βX (R.datXt t) (R.eG g) κ0) :
    (R.B.R t).act_tie.red (⟨_, mem_Q_of_lift R t g hκ0⟩ : (levEnv D.sp.X' R.βX (R.datXt t)).Q) = g := by
  apply R.eG.injective
  rw [hred t ⟨_, mem_Q_of_lift R t g hκ0⟩]
  exact hκ0.2.2

theorem actX_apply (t : T) (g : G) (hex : ∃ κ, IsLevelLift D.sp.X' R.βX (R.datXt t) (R.eG g) κ) (F : GA D D.sp.X' → ℂ)
    (h : GA D D.sp.X') :
    actX R t g F h = (levChi D.sp.X' R.βX (flagL (R.datXt t)) hex.choose)⁻¹ * F (h * hex.choose) := by
  show actG0 D.sp.X' R.βX (R.datXt t) (R.eG g) F h = _
  unfold actG0
  rw [dif_pos hex]

theorem jX_act (hM : R.IsModels) (t : T) (g : G) (x : A.fam.amb.FR t) (q0 : (levEnv D.sp.X' R.βX (R.datXt t)).Q)
    (hred0 : (R.B.R t).act_tie.red q0 = g) :
    (R.HX t).e (R.jX t (A.fam.amb.opR t (Sum.inr g) x)) =
      Bridge.g0Act (levEnv D.sp.X' R.βX (R.datXt t)).ch q0 ((R.HX t).e (R.jX t x)) := by
  have hext := (R.B.R t).act_tie.act_eq g q0 hred0 x
  exact (hM.jX t _).trans (hext.trans (congrArg (Bridge.g0Act (levEnv D.sp.X' R.βX (R.datXt t)).ch q0) (hM.jX t x).symm))

theorem actTieXOf_holds : ActTieXOf R := by
  intro hM hred t g x
  have hex := lift_X R hred t g
  have hκ0 := hex.choose_spec
  have hmem := mem_Q_of_lift R t g hκ0
  have hred0 := red_of_lift R hred t g hκ0
  have hch : (((levEnv D.sp.X' R.βX (R.datXt t)).ch ⟨_, hmem⟩ : ℂˣ) : ℂ) =
      levChi D.sp.X' R.βX (flagL (R.datXt t)) hex.choose := rfl
  refine LinearMap.ext fun v => funext fun h => ?_
  have e1 := congrArg (fun F : Bridge.Gf D.sp.X' → R.cX.W => R.cX.toMap R.prX F v h) (jX_act R hM t g x _ hred0)
  have e2 := toMap_g0Act R.cX hM.cX R.prX (levEnv D.sp.X' R.βX (R.datXt t)).ch ⟨_, hmem⟩ hex.choose hκ0.1 rfl
    ((R.HX t).e (R.jX t x)) v h
  have e3 := actX_apply R t g hex (fX R t (R.jX t x) v) h
  exact e1.trans (e2.trans ((congrArg (fun c : ℂ => c⁻¹ * R.cX.toMap R.prX ((R.HX t).e (R.jX t x)) v (h * hex.choose))
    hch).trans e3.symm))

end Formalism.IndefR.Eqv.Act

end
