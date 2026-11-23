import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.EquivIoYOf

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open scoped TensorProduct InnerProductSpace

namespace Formalism.IndefR.Eqv.Act

open Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Links.RealDat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

def ActTieXOf : Prop := R.IsModels → R.grp_red_R → ActTieX R

def SpanX : Prop :=
  ∀ t (u : R.CC t (D.R.m - 1)),
    (∀ φ v, (u : SmT (R.MY (D.R.m - 1)) →ₗ[ℂ] (GA D (Yc D (D.R.m - 1)) → ℂ)) (R.ItX φ v) = 0) → u = 0

def KerDiagX : Prop :=
  ∀ t, ∀ κS ∈ levG (Yc D (D.R.m - 1)) (R.βY (D.R.m - 1)) (flagL (R.datYt t (D.R.m - 1) R.triv)),
    ∀ κT ∈ levG D.sp.X' R.βX (flagL (R.datXt t)),
      rTup (R.βY (D.R.m - 1)) (R.datYt t (D.R.m - 1) R.triv) (finE (Yc D (D.R.m - 1)) κS) =
          rTup R.βX (R.datXt t) (finE D.sp.X' κT) →
        ∀ φ, R.ωX t (κS, κT) (R.ptX t φ) =
          (levChi (Yc D (D.R.m - 1)) (R.βY (D.R.m - 1)) (flagL (R.datYt t (D.R.m - 1) R.triv)) κS *
            (levChi D.sp.X' R.βX (flagL (R.datXt t)) κT)⁻¹) • R.ptX t φ

def EquivIoXOf : Prop :=
  R.IsModels → R.IsChain → R.grp_red_R → LiftsAll R → Formalism.IndefR.Eqv.UnimodGA D.sp.X' → SpanX R → KerDiagX R → EquivIoX R

def SpanP : Prop :=
  ∀ i, ∀ S ∈ R.Wall i (sg0 D A), (∀ v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ, S (fun ρ => v ρ) = 0) → S = 0

def KerDiagP : Prop :=
  ∀ i t, ∀ κV ∈ levG (Vc D i) (R.βV i) (flagL (R.datVt i t)),
    ∀ κW ∈ levG (Wc D i) (R.βW i) (flagL (R.datWp i R.triv)),
      rTup (R.βV i) (R.datVt i t) (finE (Vc D i) κV) = rTup (R.βW i) (R.datWp i R.triv) (finE (Wc D i) κW) →
        ∀ P, R.ωP i t (κV, κW) (R.ptP i t P) =
          ((levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) κV)⁻¹ *
            levChi (Wc D i) (R.βW i) (flagL (R.datWp i R.triv)) κW) • R.ptP i t P

def ThFEquivOf : Prop :=
  R.IsModels → R.IsThP → R.grp_red_L → LiftsAll R → (∀ i, Formalism.IndefR.Eqv.UnimodGA (Vc D i)) → SpanP R → KerDiagP R →
    ThFEquiv R

end Formalism.IndefR.Eqv.Act

end
