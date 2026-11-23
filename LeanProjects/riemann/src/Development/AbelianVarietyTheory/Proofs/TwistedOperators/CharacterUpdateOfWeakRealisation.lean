import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.IndefiniteReal.LinksExist
import Formalism.LocalToGlobal.IndefiniteReal.LinksExistW
import Formalism.LocalToGlobal.IndefiniteReal.CutTuples2
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR.Links Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CharRealise

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def toCx3One (R : RealDat3 D A3 Ks) (F : Face3 D A3) : CxData A3.fam3.amb3 where
  FC t := Tw (twAt D.what₂.embLL A3.A.v0) (R.HX t).H
  jR t := Tw.semi _ R.toRealDat.emb0 (R.jX t)
  EE := Tw (twAt D.what₂.embLL A3.A.v0) R.HE.H
  Θ t := Tw.map _ (R.Th t)
  EEp p := Tw.sub _ (R.EEp3 p)
  EEl b := Tw.sub _ ((R.toRealDat.EEat (R.toRealDat.levR F.lv2 b)).comap R.HE.e)
  FLC i t := Tw (twAt D.what₂.embLL A3.A.v0) (R.HV i t).H
  jL i t := Tw.semi _ R.toRealDat.emb0 (R.jV i t)
  W i := Tw (twAt D.what₂.embLL A3.A.v0) (R.HW i (sg0 D A3.A)).H
  θ' i t := Tw.map _ (R.thG i t)
  Wp i p := Tw.sub _ (R.Wp3 i p)
  dW b i := Module.finrank D.what₂.LL (R.toRealDat.WL F.lv2 b i)
  WC b i v := Tw (twAt D.what₂.embLL v) (R.toRealDat.WS F.lv2 b i (sgAt D.what₂.embLL v))
  bW b i _ k := Tw.mk _ ⟨R.toRealDat.bC F.lv2 b i _ k, Submodule.subset_span ⟨k, rfl⟩⟩
  eW b i := Tw.map _ (((Real.sqrt (RealDat.nP F.lv2 b) : ℝ) : ℂ) • (R.toRealDat.WS F.lv2 b i (sg0 D A3.A)).subtype)
  M b i := (R.FW i).Mcoord (F.lv2.lvl b).P (F.lv2.lvl b).ψ⁻¹ (fun g => (idemOf A3.A.X).coeff g) (R.toRealDat.bL F.lv2 b i)
  nP := RealDat.nP F.lv2
  μ := R.mu
  Tw := R.twPl
  κ _ := R.kap
  lam := R.lam3
  err0 := R.err0

theorem toCx3_eq_one (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hph : ∀ i, R.phs i = 1) : R.toCx3 F = toCx3One R F := by
  unfold RealDat3.toCx3 toCx3One
  congr 1
  funext i t
  simp only [hph, one_smul]

end GlobalTheory.CharRealise
