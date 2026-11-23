import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockOfApply
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdjointThetaKillsReferenceTuple
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodProjectorThetaLiftOfBaseLevelLaw
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftFormLvlOp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

noncomputable section

namespace GlobalTheory.PlaceLift

theorem eMt_fix (D : D7) (μ : D.what₂.Tup) (j : ℕ) (x : D.what₂.MtL μ j) (hx : x ∈ Idx.TjV D μ j) :
    D.what₂.eMt μ j (D.what₂.jMt μ j x) = D.what₂.jMt μ j x := by
  have hL : ∀ y ∈ Idx.TjL D μ j, D.what₂.eMt μ j (D.what₂.jMt μ j y) = D.what₂.jMt μ j y := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨v, -, hv⟩ := hz
      rw [← hv]
      exact LinearMap.congr_fun (D.what₂.eMt_idem μ j) _
    | zero => rw [map_zero, map_zero]
    | add a b _ _ ha hb => rw [map_add, map_add, ha, hb]
    | smul c a _ ha => rw [Idx.smul_def, LinearMap.map_smulₛₗ, map_smul, ha]
  induction hx using Submodule.span_induction with
  | mem z hz => exact hL z hz
  | zero => rw [map_zero, map_zero]
  | add a b _ _ ha hb => rw [map_add, map_add, ha, hb]
  | smul c a _ ha => rw [LinearMap.map_smulₛₗ, map_smul, ha]

variable {D : D7} {X : RealSide D} {X0 : BaseLevelRowSide D} (Y : GlobalTheory.Mem.R3.Read (A3 := X.A3) X.R.toRealDat X.F.lv2 X0)

theorem extV_formOf_eMt (j : Fin D.R.m) (t : X.T) (hμ : Used0 D (Y.tup t)) (c) :
    X.R.toRealDat.extV j (Y.tupT (Y.tup t)) (formOf Y hμ j (D.what₂.jMt (Y.tup t) (j.1 + 1) (Y.eMt j t c))) =
      X.R.toRealDat.extV j t (X.R.jV j t (GlobalTheory.Mem.R3.liftForm X.A3.A X.F.P0 X.F.ψ0 j t c)) :=
  (extV_formOf Y hμ j _).trans (Y.mtRead j t hμ c)

theorem idem_fix (hH : GlobalTheory.Mem.R3.Holds X.R X.F) (j : Fin D.R.m) (t : X.T) (hμ : Used0 D (Y.tup t)) (c)
    (hc : D.what₂.eMt (Y.tup t) (j.1 + 1) (D.what₂.jMt (Y.tup t) (j.1 + 1) (Y.eMt j t c)) =
      D.what₂.jMt (Y.tup t) (j.1 + 1) (Y.eMt j t c)) :
    X.R.jV j t (GlobalTheory.Mem.R3.liftForm X.A3.A X.F.P0 X.F.ψ0 j t c) =
      X.R.jV j t (∑ g, (idemOf X.A3.A.X).coeff g • (X.A3.A.fam.L j t).r g (GlobalTheory.Mem.R3.liftForm X.A3.A X.F.P0 X.F.ψ0 j t c)) := by
  have e2 := GlobalTheory.CenTranslate.liftForm_lvlOp (A3 := X.A3) (F := X.F.lv2) hH.ok.ok2 j t (idemOf X.A3.A.X)
    (fun b => idemOf_central X.A3.A.X hH.ok.ok2.irr b) c
  have e1 := (Y.formsL j t).op_eq c
  have e3 : D.what₂.jMt (Y.tup t) (j.1 + 1) (Y.eMt j t c) =
      D.what₂.jMt (Y.tup t) (j.1 + 1) (Y.eMt j t ((lE D X.A3.A X.F.P0 X.F.ψ0 j t).mulVec c)) := hc.symm.trans e1
  refine Y.hinj j t ?_
  refine (Y.mtRead j t hμ c).symm.trans ?_
  refine (congrArg (fun y => (Y.IL.jMt (Y.tup t) hμ j y).1) e3).trans ?_
  refine (Y.mtRead j t hμ _).trans ?_
  exact congrArg (fun v => X.R.toRealDat.extV j t (X.R.jV j t v)) e2

theorem isAlgV_self (j : Fin D.R.m) (t : X.T) (u : (X.A3.A.fam.L j t).S.Forms)
    (hu : X.R.jV j t u = X.R.jV j t (∑ g, (idemOf X.A3.A.X).coeff g • (X.A3.A.fam.L j t).r g u))
    (κ : X.Γ → (GlobalTheory.IndefiniteRowSideFullHecke.CommutingRationalGroups.levV X.R.toRealDat j t).Q) (hκ : ∀ g, GlobalTheory.IndefiniteRowSideFullHecke.CommutingRationalGroups.IsLiftV X.R.toRealDat j t g (κ g)) :
    GlobalTheory.IndefiniteRowSideFullHecke.CommutingRationalGroups.IsAlgV X.R.toRealDat j t (RealDat.eC (A := X.A3.A) (sg0 D X.A3.A)) κ (X.R.jV j t u) (X.R.jV j t u) := by
  have hs : sg0 D X.A3.A = D.what₂.embLL := sgAt_mk _ X.R.hv0
  refine (congrArg (X.R.HV j t).e hu).trans ?_
  have e3 := map_sum (X.R.jV j t) (fun g => (idemOf X.A3.A.X).coeff g • (X.A3.A.fam.L j t).r g u) Finset.univ
  have e4 := map_sum (X.R.HV j t).e (fun g => (X.R.jV j t) ((idemOf X.A3.A.X).coeff g • (X.A3.A.fam.L j t).r g u)) Finset.univ
  refine ((congrArg (X.R.HV j t).e e3).trans e4).trans ?_
  refine Finset.sum_congr rfl fun g _ => ?_
  have e5 := map_smulₛₗ (X.R.jV j t) ((idemOf X.A3.A.X).coeff g) ((X.A3.A.fam.L j t).r g u)
  have e6 := LinearMap.map_smul (X.R.HV j t).e (D.what₂.embLL ((idemOf X.A3.A.X).coeff g)) (X.R.jV j t ((X.A3.A.fam.L j t).r g u))
  refine ((congrArg (X.R.HV j t).e e5).trans e6).trans ?_
  have hT := GlobalTheory.RationalFormsAction.isTranslate_act_V X.R.toRealDat X.char.grp.red_L X.char.models.jV j t g u
  have e7 : (X.R.HV j t).e (X.R.jV j t ((X.A3.A.fam.L j t).r g u)) =
      Bridge.g0Act (GlobalTheory.IndefiniteRowSideFullHecke.CommutingRationalGroups.levV X.R.toRealDat j t).ch (κ g) ((X.R.HV j t).e (X.R.jV j t u)) :=
    funext fun h => hT.2 (κ g) (hκ g) h
  have e8 : D.what₂.embLL ((idemOf X.A3.A.X).coeff g) = RealDat.eC (A := X.A3.A) (sg0 D X.A3.A) g := by
    rw [RealDat.eC, hs]
  rw [e7, e8]

theorem lift_read (hP : GlobalTheory.Mem.R3.Pins X.R X.F X.cG) (hH : GlobalTheory.Mem.R3.Holds X.R X.F) (j : Fin D.R.m) (μ : D.what₂.Tup) (hμ : Used0 D μ)
    (x : D.what₂.MtL μ (j.1 + 1)) (hx : x ∈ Idx.TjV D μ (j.1 + 1)) (v : (X.R.MW j (sg0 D X.A3.A)).Vec) :
    (X.R.HW j (sg0 D X.A3.A)).e (Y.mj.eW j (D.what₂.thetaP μ (j.1 + 1) (D.what₂.jMt μ (j.1 + 1) x))) v =
      X.R.thF j (Y.tupT μ) (formOf Y hμ j (D.what₂.jMt μ (j.1 + 1) x)) v := by
  obtain ⟨t, rfl⟩ : ∃ t, Y.tup t = μ := ⟨_, Y.tupTie μ hμ⟩
  obtain ⟨c, rfl⟩ := (Y.eMt j t).surjective x
  have hC : GlobalTheory.Hk3.Core X.R.toRealDat X.F.lv2 :=
    ⟨X.char.lev, X.char.grp, X.char.fam, X.char.models, X.char.chain, X.char.thP⟩
  choose κ hκ using GlobalTheory.ProjLiftLaw.liftV_exists_core hC j t
  have h1 := GlobalTheory.Mem.ThetaRead3.thetaP_read_plain D X.Γ X.Pl0 X.I0 X.T X.A3 X.core.Q.c.F X.R X.F X.cG X0 Y hP hH j t c
  have h2 := GlobalTheory.ProjLiftLaw.thG_apply_eq hC j t κ hκ _ _
    (isAlgV_self j t _ (idem_fix Y hH j t hμ c (eMt_fix D _ _ _ hx)) κ hκ) v
  have h3 := GlobalTheory.Mem.ThetaRead3.thF_congr X.R.toRealDat Y.hinj j t (Y.tupT (Y.tup t)) (Y.tupT_tup t) _ _ (extV_formOf_eMt Y j t hμ c)
  exact ((congrArg (fun y => (X.R.HW j (sg0 D X.A3.A)).e y v) h1).trans h2).trans (congrArg (fun U => U v) h3).symm

theorem lift_read_at : ∀ (D : D7) (X : RealSide D) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := X.A3) X.R.toRealDat X.F.lv2 X0) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS X.R X.cG S) (Z : ExportTie YS X.geo.v₀) (c : NChoice D) (w : D.what₂.places.Pl) (j : Fin D.R.m) (H : AtPlace Y Z c w j),
  ∀ x ∈ Idx.TjV D (D.what₂.muTw w) (j.1 + 1),
  (X.R.HW j (sg0 D X.A3.A)).e (Y.mj.eW j (D.what₂.thetaP (D.what₂.muTw w) (j.1 + 1) (D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) x))) (X.geo.v₀ j (sg0 D X.A3.A)) =
    X.R.thF j (Y.tupT (D.what₂.muTw w)) (formOf Y (used_of_tw H.tw) j (D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) x)) (X.geo.v₀ j (sg0 D X.A3.A)) :=
  fun _ _ _ Y _ _ _ _ _ j H x hx => lift_read Y H.pins H.intersectionNumber_baseChange j _ (used_of_tw H.tw) x hx _

end GlobalTheory.PlaceLift

end
