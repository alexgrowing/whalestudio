import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTuplesOfLaws
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowAtOfRatStep

set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries GlobalTheory.ConjTwist Formalism.IndefR.Lev
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BigOn.Exp.TwConj
section Lev
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
end Lev
section Laws
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
variable {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)}
  {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec} {O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)} {j : Fin D.R.m}
end Laws
section Point
open Classical in
def TwLevAtAlt : Prop := _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i p w j => ∀ ρ ρ' : Setup (Fm.D x i).ntw, ρ.Good → ρ'.Good → RealPin p.R p.cG ρ →
  SameBut ρ ρ' → (Adapted p w ρ ∨ Adapted p w ρ') →
  ∃ (χ χ' : Formalism.L2.Host.HChar (Fm.D x i).host.E) (xiR xiR' : ∀ PP : Pl (Fm.D x i).host.E, (kP PP)ˣ →* ℂˣ),
    TwLev p.R.toRealDat χ ((baseW (Fm.ex x hx i) w j ρ).de.chi * (twW (Fm.ex x hx i) w ρ).chi)
      ((baseW (Fm.ex x hx i) w j ρ).de.Q ∪ (twW (Fm.ex x hx i) w ρ).Q) xiR ∧
    TwLev p.R.toRealDat χ' ((baseW (Fm.ex x hx i) w j ρ).de.chi * (twW (Fm.ex x hx i) w ρ').chi)
      ((baseW (Fm.ex x hx i) w j ρ).de.Q ∪ (twW (Fm.ex x hx i) w ρ').Q) xiR' ∧
    χ ≠ 1 ∧ χ' ≠ 1 ∧ (χ ≠ χ' ∨ (baseW (Fm.ex x hx i) w j ρ).de.chi * (twW (Fm.ex x hx i) w ρ).chi =
      (baseW (Fm.ex x hx i) w j ρ).de.chi * (twW (Fm.ex x hx i) w ρ').chi)
end Point
end GlobalTheory.BigOn.Exp.TwConj
end
end
