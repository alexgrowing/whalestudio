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

noncomputable section

namespace GlobalTheory.ThetaGoodEquiv

theorem thG_equiv : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsModels → R.IsThP → R.grp_record → A.v0 = InfinitePlace.mk D.what₂.embLL → ∀ (i : Fin D.R.m) (t : T) (g0 : G0 R.Pg D.R.r) (κ : GA D (Vc D i)) (κ' : GA D (Wc D i)), IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) g0 κ → IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) g0 κ' → ∀ S : (R.HV i t).H →ₗ[ℂ] (R.HV i t).H, (∀ y h, R.extV i t (S y) h = (levChi _ (R.βV i) (flagL (R.datVt i t)) κ)⁻¹ • R.extV i t y (h * κ)) → ∀ y, R.thG i t (S y) = R.gW i (sg0 D A) (R.eG.symm g0) (R.thG i t y) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hL hM hP hgr _ i t g0 κ κ' hκ hκ' S hS y
  have hinj := (hM.HW i (sg0 D A)).1
  apply hinj
  have hX := hP.thF_mem i t y
  have hsh := GlobalTheory.ThetaShiftSmooth.thF_shift_all R hL hM hP i t g0 κ κ' hκ hκ' y (S y) (hS y)
  have hcomm := (GlobalTheory.ProjComm.proj_comm R hL hgr).2
  have e1 := hP.thG i t (S y)
  have e2 := hM.gW i (sg0 D A) (R.eG.symm g0) (R.thG i t y)
  have e3 := hP.thG i t y
  have hκ'' : IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG (R.eG.symm g0)) κ' := by
    rw [MulEquiv.apply_symm_apply]; exact hκ'
  have hT : ∀ v, HasType (Wc D i) (R.βW i) (R.datWp i R.triv) (R.thF i t y v) := fun v k hk h =>
    (GlobalTheory.mult_value_left_cont_level R.θ (R.MW i (sg0 D A)) _ _ (R.thF i t y) hX v).2.2 k hk h
  have h2 := GlobalTheory.ThetaShiftSmooth.levChi_flag_eq_one R i κ'
  have hUe : ∀ v, R.thF i t (S y) v =
      actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG (R.eG.symm g0)) (R.thF i t y v) := fun v => by
    funext z
    have h1 := level_action_spec (V := Wc D i) (β := R.βW i) (L := R.datWp i R.triv) (hT v) ⟨κ', hκ''⟩ κ' hκ'' z
    have h3 := congrArg (fun c : ℂ => c⁻¹ * R.thF i t y v (z * κ')) h2
    have h4 : (1 : ℂ)⁻¹ * R.thF i t y v (z * κ') = R.thF i t y v (z * κ') := by simp
    exact (hsh v z).trans (h1.trans (h3.trans h4)).symm
  have key : postOn _ (R.eWf i (sg0 D A)) (R.thF i t (S y)) =
      postOn _ (actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG (R.eG.symm g0)))
        (postOn _ (R.eWf i (sg0 D A)) (R.thF i t y)) := by
    refine MultilinearMap.ext fun v => ?_
    exact (congrArg (R.eWf i (sg0 D A)) (hUe v)).trans (hcomm i (sg0 D A) (R.eG.symm g0) (R.thF i t y v) (hT v))
  exact e1.trans (key.trans ((congrArg _ e3).symm.trans e2.symm))

end GlobalTheory.ThetaGoodEquiv

end
