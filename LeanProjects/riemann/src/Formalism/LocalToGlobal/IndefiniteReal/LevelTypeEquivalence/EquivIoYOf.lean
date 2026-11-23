import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.PrincipalLevelAction

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open scoped TensorProduct InnerProductSpace

namespace Formalism.IndefR.Eqv.Act

open Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Links.RealDat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

def SpanY : Prop :=
  ∀ t k, k + 1 < D.R.m → ∀ u : R.CC t k,
    (∀ φ v, (u : SmT (R.MY k) →ₗ[ℂ] (GA D (Yc D k) → ℂ)) (R.ItY k φ v) = 0) → u = 0

def KerDiagY : Prop :=
  ∀ t k, k + 1 < D.R.m →
    ∀ κS ∈ levG (Yc D k) (R.βY k) (flagL (R.datYt t k R.triv)),
    ∀ κT ∈ levG (Yc D (k + 1)) (R.βY (k + 1)) (flagL (R.datYt t (k + 1) R.triv)),
      rTup (R.βY k) (R.datYt t k R.triv) (finE (Yc D k) κS) =
          rTup (R.βY (k + 1)) (R.datYt t (k + 1) R.triv) (finE (Yc D (k + 1)) κT) →
        ∀ φ, R.ωY t k (κS, κT) (R.ptY t k φ) =
          (levChi (Yc D k) (R.βY k) (flagL (R.datYt t k R.triv)) κS *
            (levChi (Yc D (k + 1)) (R.βY (k + 1)) (flagL (R.datYt t (k + 1) R.triv)) κT)⁻¹) • R.ptY t k φ

def EquivIoYOf : Prop :=
  R.IsModels → R.IsChain → LiftsAll R → (∀ j, Formalism.IndefR.Eqv.UnimodGA (Yc D j)) → SpanY R → KerDiagY R → EquivIoY R

end Formalism.IndefR.Eqv.Act

end
