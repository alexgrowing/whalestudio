import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GEqTie
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GEqUnit

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open scoped TensorProduct InnerProductSpace

namespace Formalism.IndefR.Eqv.Act

open Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Links.RealDat Formalism.IndefR.Datum

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Kernel1

variable {D : D7} {S T : HSp D}

end Kernel1

section CoefV

variable {D : D7} {V : HSp D} (c : CoefA V)

theorem ext_g0Act (hc : c.Is) {Q : Subgroup (Bridge.Gf V)} (ch : Q →* ℂˣ) (q : Q) (κ : GA D V) (hκ : κ ∈ GfC V)
    (hκq : (finHom V).rangeRestrict κ = q) (F : Bridge.Gf V → c.W) (h : GA D V) :
    c.ext (Bridge.g0Act ch q F) h = (((ch q)⁻¹ : ℂˣ) : ℂ) • c.ext F (h * κ) := by
  have e : c.ext (Bridge.g0Act ch q F) h =
      c.ρ h⁻¹ ((((ch q)⁻¹ : ℂˣ) : ℂ) • F ((finHom V).rangeRestrict h * q)) := rfl
  have e2 : c.ρ h⁻¹ ((((ch q)⁻¹ : ℂˣ) : ℂ) • F ((finHom V).rangeRestrict h * q)) =
      (((ch q)⁻¹ : ℂˣ) : ℂ) • c.ρ h⁻¹ (F ((finHom V).rangeRestrict h * q)) := LinearMap.map_smul _ _ _
  have e6 : c.ext F (h * κ) = c.ρ h⁻¹ (F ((finHom V).rangeRestrict h * q)) := hκq ▸ coefExt_mul c hc F h κ hκ
  exact e.trans (e2.trans (congrArg _ e6.symm))

end CoefV

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

theorem mem_Q_of_liftV (i : Fin D.R.m) (t : T) (g : G) {κ0 : GA D (Vc D i)}
    (hκ0 : IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) (R.eG g) κ0) :
    (finHom (Vc D i)).rangeRestrict κ0 ∈ (levEnv (Vc D i) (R.βV i) (R.datVt i t)).Q := by
  show Formalism.UG.bc (swapAE D) (finHom (Vc D i) κ0) ∈ lev D.sp.cm (Vc D i).gram (R.βV i) (flagL (R.datVt i t))
  rw [← finE_eq]
  exact ⟨hκ0.2.1, Subgroup.mem_top _⟩

theorem red_of_liftV (hred : R.grp_red_L) (i : Fin D.R.m) (t : T) (g : G) {κ0 : GA D (Vc D i)}
    (hκ0 : IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) (R.eG g) κ0) :
    (R.B.L i t).act_tie.red (⟨_, mem_Q_of_liftV R i t g hκ0⟩ : (levEnv (Vc D i) (R.βV i) (R.datVt i t)).Q) = g := by
  apply R.eG.injective
  rw [hred i t ⟨_, mem_Q_of_liftV R i t g hκ0⟩]
  exact hκ0.2.2

theorem jV_act (hM : R.IsModels) (i : Fin D.R.m) (t : T) (g : G) (x : A.fam.amb.FL i t)
    (q0 : (levEnv (Vc D i) (R.βV i) (R.datVt i t)).Q) (hred0 : (R.B.L i t).act_tie.red q0 = g) :
    (R.HV i t).e (R.jV i t (A.fam.amb.opL i t (Sum.inr g) x)) =
      Bridge.g0Act (levEnv (Vc D i) (R.βV i) (R.datVt i t)).ch q0 ((R.HV i t).e (R.jV i t x)) := by
  have hext := (R.B.L i t).act_tie.act_eq g q0 hred0 x
  exact (hM.jV i t _).trans (hext.trans
    (congrArg (Bridge.g0Act (levEnv (Vc D i) (R.βV i) (R.datVt i t)).ch q0) (hM.jV i t x).symm))

theorem extV_apply (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) (h : GA D (Vc D i)) :
    R.extV i t y h = (R.cV i).ext ((R.HV i t).e y) h := rfl

end Formalism.IndefR.Eqv.Act

end
