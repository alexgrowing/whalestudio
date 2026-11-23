import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.EvTieP
import Formalism.LocalToGlobal.IndefiniteReal.LiftGoodPartComplexEqRangeFamily

noncomputable section

open scoped InnerProductSpace
open Formalism.BasicNotions Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Links

namespace GlobalTheory.MiS
open Formalism Formalism.IndefR

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section FreeSingleHomotopyEquivDiscreteChains

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def MidData (R : RealDat3 D A3 Ks) (F : Face3 D A3)
    (sEE : (R.toCx3 F).EE →ₗ⋆[ℂ] (F.fc (R.toCx3 F).zs).Sp.HH) (d : (R.toCx3 F).MIDat F.fc) : Prop :=
  (R.toCx3 F).MIUnit d ∧ (R.toCx3 F).MIid (F.eV (R.toCx3 F).zs) sEE d

def PtNZ (R : RealDat3 D A3 Ks) (F : Face3 D A3) : Prop :=
  ∀ u, ∃ t, ∃ φ, ∃ v : Fin ((F.fc (R.toCx3 F).zs).Df1.nV t) → D.what₂.LL, (F.fc (R.toCx3 F).zs).Dc.Pt u t φ v ≠ 0

open scoped InnerProductSpace in

def PairZeroAt (R : RealDat3 D A3 Ks) (F : Face3 D A3)
    (sEE : (R.toCx3 F).EE →ₗ⋆[ℂ] (F.fc (R.toCx3 F).zs).Sp.HH) (d : (R.toCx3 F).MIDat F.fc)
    (u : (F.fc (R.toCx3 F).zs).Dc.Mem) : Prop :=
  ∀ t (φ : Fin ((F.fc (R.toCx3 F).zs).Dc.a u) → D.what₂.LL) (v : Fin ((F.fc (R.toCx3 F).zs).Df1.nV t) → D.what₂.LL),
    ⟪sEE (d.V ((R.toCx3 F).Θ t ((R.toCx3 F).jR t (F.eV (R.toCx3 F).zs t v)))),
      (F.fc (R.toCx3 F).zs).Sp.Pu u ((d.U u).mulVec (cpt A3.fam3.F.v0.embedding φ))⟫_ℂ = 0

def AltAt (R : RealDat3 D A3 Ks) (F : Face3 D A3)
    (sEE : (R.toCx3 F).EE →ₗ⋆[ℂ] (F.fc (R.toCx3 F).zs).Sp.HH) (d : (R.toCx3 F).MIDat F.fc) : Prop :=
  ∀ u, (∃ t, ∃ φ, ∃ v : Fin ((F.fc (R.toCx3 F).zs).Df1.nV t) → D.what₂.LL, (F.fc (R.toCx3 F).zs).Dc.Pt u t φ v ≠ 0) ∨
    PairZeroAt R F sEE d u

end FreeSingleHomotopyEquivDiscreteChains

section Gen

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A)
  {fc : DefSub A → DefFace Bs} (cr : Crd A fc) (cv : CrdV A)

def OpsUnit (V : X.EE →ₗ[ℂ] X.EE) (U : ∀ u, Matrix (Fin ((fc X.zs).Dc.a u)) (Fin ((fc X.zs).Dc.a u)) ℂ) : Prop :=
  (∀ e ∈ X.EEl true, V e ∈ X.EEl true ∧ ‖V e‖ = ‖e‖) ∧
    ∀ u x, fnorm ((fc X.zs).Dc.Xc u Bs.v0) ((U u).mulVec x) = fnorm ((fc X.zs).Dc.Xc u Bs.v0) x

def IdBase (eV : ∀ t, (Fin ((fc X.zs).Df1.nV t) → K) →ₗ[K] A.FR t) (sEE : X.EE →ₗ⋆[ℂ] (fc X.zs).Sp.HH)
    (V : X.EE →ₗ[ℂ] X.EE) (a : (fc X.zs).Dc.Mem → ℂ)
    (U : ∀ u, Matrix (Fin ((fc X.zs).Dc.a u)) (Fin ((fc X.zs).Dc.a u)) ℂ) : Prop :=
  ∀ u (φ : Fin ((fc X.zs).Dc.a u) → K) (F : Fin ((fc X.zs).Df1.nV Bs.μ0) → K),
    Bs.v0.embedding ((fc X.zs).Dc.Pt u Bs.μ0 φ F) =
      a u * ⟪sEE (V (X.Θ Bs.μ0 (X.jR Bs.μ0 (eV Bs.μ0 F)))), (fc X.zs).Sp.Pu u ((U u).mulVec (cpt Bs.v0.embedding φ))⟫_ℂ

def IdTup (ζ : (fc X.zs).Dc.Mem → Bs.Tup → K) : Prop :=
  (∀ u, ζ u Bs.μ0 = 1) ∧ (∀ u t, ∃ n : ℕ, 0 < n ∧ ζ u t ^ n = 1) ∧ X.MatrixIdentityOffBase cr ζ

def CxTies (eV : ∀ t, (Fin ((fc X.zs).Df1.nV t) → K) →ₗ[K] A.FR t) : Prop :=
  (fc X.zs).Df1.WF ∧ X.H2 cr true ∧ X.RATmu cr true ∧ X.JIsoR cv ∧ X.RatLev cr cv true ∧ X.DnLev cv true ∧
    X.UpLev cv true ∧ X.CoordinatesInGoodPart cr cv true ∧ X.EVTie cr cv eV

def datOf (V : X.EE →ₗ[ℂ] X.EE) (a : (fc X.zs).Dc.Mem → ℂ)
    (U : ∀ u, Matrix (Fin ((fc X.zs).Dc.a u)) (Fin ((fc X.zs).Dc.a u)) ℂ) (ζ : (fc X.zs).Dc.Mem → Bs.Tup → K) :
    X.MIDat fc :=
  ⟨V, a, U, fun u t => Bs.v0.embedding (ζ u t)⟩

variable {X cr cv}

end Gen

end GlobalTheory.MiS

end
