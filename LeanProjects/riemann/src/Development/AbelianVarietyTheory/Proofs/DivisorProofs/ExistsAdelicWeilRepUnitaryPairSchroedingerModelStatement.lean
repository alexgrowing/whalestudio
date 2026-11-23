import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicWeilRepUnitaryPairSchroedingerModel
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adelicWeilRep_unitaryPair_schroedingerModel : ∀ (D : D7) (B : Base D.host.F D.host.E), B.IsGood D.sp.cm.sig →
    ∀ (n d : ℕ) (X : Spc D.host.F D.host.E n) (Y : Spc D.host.F D.host.E d) (r s r' s' : ℕ),
      X.IsHerm D.sp.cm.sig B r s → Y.IsSkew D.sp.cm.sig B r' s' →
      ∀ Mo : Model D.sp.cm.sig X Y, Mo.IsGood B.ψ →
      ∀ χX χW : Chr D.host.F D.host.E, GlobalTheory.LFun.IsHecke D.host.F D.host.E χX → GlobalTheory.LFun.IsHecke D.host.F D.host.E χW →
        GlobalTheory.WeilM.ResEtaPow (Units.map (algebraMap D.host.F (AF D.host.F)).toMonoidHom).range χX n →
        GlobalTheory.WeilM.ResEtaPow (Units.map (algebraMap D.host.F (AF D.host.F)).toMonoidHom).range χW d →
        ∃ om, Mo.IsWeil B.ψ χX χW om := by
  first | exact @GlobalTheory.WeilSchrodinger.exists_isWeil | exact GlobalTheory.WeilSchrodinger.exists_isWeil | (intros; apply GlobalTheory.WeilSchrodinger.exists_isWeil <;> assumption)
