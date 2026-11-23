import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.IsMultMapUnivZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TranslateUnitaryLifts
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelGroupActionEqZeroOfNoLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftIntertwinesLiftsSmoothVectors
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftMemLevelOfDatumFlagCharacter
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlacesApart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLeviFlagOfMemParabolic
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem translate_lift_linear_isometry : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsModels → ∀ (i : Fin D.R.m) (t : T) (g0 : G0 R.Pg D.R.r) (κ : GA D (Vc D i)), IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) g0 κ → ∃ S : (R.HV i t).H →ₗ[ℂ] (R.HV i t).H, (∀ y, ‖S y‖ = ‖y‖) ∧ ∀ y h, R.extV i t (S y) h = (levChi _ (R.βV i) (flagL (R.datVt i t)) κ)⁻¹ • R.extV i t y (h * κ) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hlev hMod i t g0 κ hκ
  have hex := fun y => GlobalTheory.translate_unitary_lifts R hlev hMod.HV hMod.cV i t g0 κ hκ y
  choose S hS hSn using hex
  have hinj : Function.Injective (R.HV i t).e := (hMod.HV i t).1
  refine ⟨{ toFun := S, map_add' := ?_, map_smul' := ?_ }, hSn, ?_⟩
  · intro y z
    apply hinj
    funext h
    simp only [map_add, Pi.add_apply, hS, smul_add]
  · intro a y
    apply hinj
    funext h
    simp only [map_smul, Pi.smul_apply, hS, RingHom.id_apply]
    exact smul_comm _ _ _
  · intro y h
    have hk : (R.cV i).ρ κ⁻¹ = 1 := (hMod.cV i).1 _ (inv_mem hκ.1)
    have hrr : (finHom (Vc D i)).rangeRestrict (h * κ) =
        (finHom (Vc D i)).rangeRestrict h * (finHom (Vc D i)).rangeRestrict κ := map_mul _ _ _
    show (R.cV i).ρ h⁻¹ ((R.HV i t).e (S y) ((finHom (Vc D i)).rangeRestrict h)) =
      (levChi _ (R.βV i) (flagL (R.datVt i t)) κ)⁻¹ •
        (R.cV i).ρ (h * κ)⁻¹ ((R.HV i t).e y ((finHom (Vc D i)).rangeRestrict (h * κ)))
    have hρ : (R.cV i).ρ (h * κ)⁻¹ = (R.cV i).ρ h⁻¹ := by
      rw [mul_inv_rev, MonoidHom.map_mul, hk, one_mul]
    refine (congrArg ((R.cV i).ρ h⁻¹) (hS y _)).trans ?_
    refine (LinearMap.map_smul _ _ _).trans (congrArg (fun w => (levChi _ (R.βV i) (flagL (R.datVt i t)) κ)⁻¹ • w) ?_)
    exact congrArg₂ (fun (f : Module.End ℂ (R.cV i).W) w => f w) hρ.symm (congrArg ((R.HV i t).e y) hrr.symm)

end GlobalTheory
