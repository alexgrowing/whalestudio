import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RegularisedSiegelWeilFirstTerm
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.EisRegularAtOfEisPoleLE
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SimplePoleTwistedLift
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConjugateAdjointDagger
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply

noncomputable section

namespace GlobalTheory.Core.Rk.Exh

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

open Classical in

def under (Z : Finset (Formalism.L2.DIV.Pl D.host.E)) : Finset (FinPl D) := Z.image fun PP => PP.under (𝓞 D.host.F)

def prinDat (A : HSp D) (Z : Finset (Formalism.L2.DIV.Pl D.host.E)) : Formalism.L2.DIV.LevDat D.host.E ℂ A.rank :=
  Formalism.IndefR.Lev.datW A.rank Z (Formalism.L2.DIV.LevelP.triv _ _ _) Formalism.IndefR.Lev.Frm.B

def prin (A : HSp D) (β : GL (Fin A.rank) (Formalism.IndefR.Lev.EAf D)) (Z : Finset (Formalism.L2.DIV.Pl D.host.E)) : Subgroup (GA D A) :=
  Formalism.IndefR.Lev.levG A β (prinDat A Z)

def prinInf (A : HSp D) (β : GL (Fin A.rank) (Formalism.IndefR.Lev.EAf D)) (Z : Finset (Formalism.L2.DIV.Pl D.host.E)) : Set (GA D A) :=
  {g | Formalism.IndefR.Lev.finE A g ∈ Formalism.L2.DIV.lev D.sp.cm A.gram β (prinDat A Z)}

def NoLift (ψ : AddChar (AF D.host.F) ℂ) {A W : HSp D} (om : WRep A W) (m : Measure (GA D A)) (u : GA D A → ℂ) : Prop :=
  ∀ f, IsThetaFunO ψ A W f → ∀ h, up om m f u h = 0

def Kills (ψ : AddChar (AF D.host.F) ℂ) {A W : HSp D} (χ : (AE D)ˣ →* Circle) (omh : WRep (dblSp A) W) (m : Measure (GA D A))
    (u : GA D A → ℂ) : Prop :=
  ∀ φ, IsThetaFunO ψ (dblSp A) W φ → ∀ h,
    Eis.dblInt A χ⁻¹ m (fun g => thetaKO omh g h φ) (fun g => conj (u g)) (fun g => conj (u g)) = 0

structure Defin (θ : InfFam D) (A : HSp D) (cA : CptF A) (a : GL (Fin A.rank) (AE D)) : Prop where
  inf : IsInfFam θ
  sig : HSpace.SigOK A
  pos : HSpace.IsPosDef A
  cart : IsCartanFrame A cA
  one : ∀ τ, IsCartanInv (gramAt D A τ) 1
  cA_eq : ∀ τ, cA τ * (1 : Matrix (Fin A.rank) (Fin A.rank) ℂ) = Formalism.UG.Jpq (A.sig (tauE D τ)).1 (A.sig (tauE D τ)).2 * cA τ
  maj : IsMaj A a
  maj_eq : ∀ τ, (compAt θ τ a.1)ᴴ * (gramAt D A τ * 1) * compAt θ τ a.1 = 1

structure Places (A : HSp D) (β : GL (Fin A.rank) (Formalism.IndefR.Lev.EAf D)) (Z : Finset (Formalism.L2.DIV.Pl D.host.E)) : Prop where
  frame : Formalism.L2.DIV.IsFrame β (frameLat A)
  idem : ∃ e : AE D, IsIdemSum e Z
  two : ∀ v : FinPl D, (2 : 𝓞 D.host.F) ∈ v.asIdeal → Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v

structure Form (θ : InfFam D) (A : HSp D) (cA : CptF A) (β : GL (Fin A.rank) (Formalism.IndefR.Lev.EAf D))
    (Z : Finset (Formalism.L2.DIV.Pl D.host.E)) (χW : (AE D)ˣ →* Circle) (r t : ℕ) (u : GA D A → ℂ) (par : LFun.Fam D.host.E) : Prop where
  mem : u ∈ A0 θ A cA
  fix : ∀ κ ∈ prin A β Z, ∀ g, u (g * κ) = u g
  param : LFun.IsParamFun D.sp.cm.sig A.gram (frameLat A) (under Z : Set (FinPl D)) u par
  unr : LFun.UnrOff χW (under Z : Set (FinPl D))
  str : ∃ c, GlobalTheory.IndefiniteRowSideFullHecke.SimplePoleTwistedLift.Hyp (under Z : Set (FinPl D)) r t c par (LFun.val (F := D.host.F) χW) (LFun.val (F := D.host.F) χW)

structure Occ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) {A W : HSp D} (sW : RealMat W) (om : WRep A W) (m : Measure (GA D A))
    (β : GL (Fin A.rank) (Formalism.IndefR.Lev.EAf D)) (Z : Finset (Formalism.L2.DIV.Pl D.host.E)) (u : GA D A → ℂ) (Φ : WO A W → ℂ) : Prop where
  cart : ∀ τ, IsCartanInv (gramAt D W τ) (sW τ)
  fock : IsFockVec ψ θ A W (fun _ => 1) sW Φ
  sph : IsSphOff ψ A W (frameLat A) (frameLat W) (under Z) Φ
  fix : ∀ κ ∈ prin A β Z, om (κ, 1) Φ = Φ
  real : ∀ ν 𝓕, IsCovolOne (ratL W A) ν 𝓕 → ∀ mR : Measure (GinfC A), mR.IsHaarMeasure →
    ∫ b : GinfC A, wcoef om ν 𝓕 Φ Φ b * rcoef m u u b ∂mR ≠ 0

def DownNe (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A W : HSp D) (t : ℕ) (χA χW : (AE D)ˣ →* Circle) (om : WRep A W)
    (cA : CptF A) (a : GL (Fin A.rank) (AE D)) (β : GL (Fin A.rank) (Formalism.IndefR.Lev.EAf D)) (Z : Finset (Formalism.L2.DIV.Pl D.host.E))
    (m : Measure (GA D A)) (u : GA D A → ℂ) (par : LFun.Fam D.host.E) (sW : RealMat W) (Φ : WO A W → ℂ),
    Defin θ A cA a → HSpace.SigOK W → 0 < W.rank → A.rank = W.rank + t → (∃ η, GlobalTheory.WeilParts.IsEtaTilde D η) →
    IsWeilDatumO ψ A W χA χW om → Places A β Z → m.IsHaarMeasure → Form θ A cA β Z χW W.rank t u par →
    Occ ψ θ sW om m β Z u Φ → ¬ NoLift ψ om m u

example (ψ : AddChar (AF D.host.F) ℂ) {A W : HSp D} (om : WRep A W) (m : Measure (GA D A)) : NoLift ψ om m 0 := by
  intro f _ h
  simp [up, AutomorphicL2Unitary.descend]

end GlobalTheory.Core.Rk.Exh

end
