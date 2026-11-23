import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ThetaSeriesTies
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalToGlobal.Columns.CoefColLemmas

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Lev GlobalTheory.OnTies
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TraceIncl

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)

abbrev Ser : Type := (∀ ρ, lowT (R.MW i (sg0 D A)) ρ) → GA D (Wc D i) → ℂ

def kernA (t : T0) (h : GA D (Vc D i)) : (R.cV i).W →ₗ[ℂ] Ser R i where
  toFun w v := singleSeries R i (R.ωP i t) (R.vP i t) h ((R.cV i).ρ h⁻¹ w) v
  map_add' w w' := by
    funext v g
    simp [singleSeries, Datum.thetaKO]
  map_smul' c w := by
    funext v g
    simp [singleSeries, Datum.thetaKO]

def kern (t : T0) (h : Bridge.Gf (Vc D i)) : (R.cV i).W →ₗ[ℂ] Ser R i :=
  kernA R i t (MonoidHom.mem_range.1 h.2).choose

def DatumType (t : T0) : Prop :=
  ∀ (g0 : G0 R.Pg D.R.r) κ κ', IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) g0 κ →
    IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) g0 κ' →
    R.ωP i t (κ, κ') (R.vP i t) = (levChi _ (R.βV i) (flagL (R.datVt i t)) κ)⁻¹ • R.vP i t

def GoodLiftOnto (t : T0) (U : Subgroup G) (ψ : U →* D.what₂.LLˣ) (ph : ℂ) : Prop :=
  ∀ θ, OnTies.IsClassSum R i t U ψ ph θ →
    (R.FW i).Wgood U ψ (fun g => (idemOf A.X).coeff g) ≤
      LinearMap.range ((R.FW i).eOp (fun g => (idemOf A.X).coeff g) ∘ₗ θ)

end GlobalTheory.TraceIncl
