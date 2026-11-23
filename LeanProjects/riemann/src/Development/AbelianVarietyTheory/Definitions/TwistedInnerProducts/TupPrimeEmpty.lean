import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
import Formalism.LocalToGlobal.ProjectiveLattices.CompHt

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistField

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

def tupPrime {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (t : T0) : ℕ :=
  ∏ q ∈ (R.Q t).image (fun PP => Nat.card (kP PP)), q

def XiVal {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) : Prop :=
  ∀ t x, ((R.xi t x : Circle) : ℂ) ∈ D.what₂.embLL.fieldRange

def RatG {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (ph : Fin D.R.m → ℂ) : Prop :=
  ∀ (i : Fin D.R.m) (t : T0) (x : A.fam.amb.FL i t), ∃ y : Fin (R.nW i) → D.what₂.LL,
    (R.FW i).j (sg0 D A) y = ph i • R.thG i t (R.jV i t x)

variable (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F)

def CoverField : Prop :=
  ∀ (i : Fin D.R.m) (t : T0) (l₂ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level T.Q.H), T.Q.l.Dvd l₂ → l₂.M = T.Q.l.M * tupPrime R t → l₂.A = 1 →
    ∀ (Xo₂ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli (T.Q.Dw ((i : ℕ) + 1)) l₂) (c₂ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l₂),
      c₂.F = D.what₂.embLL.toRatAlgHom.fieldRange → FnAlgClosed Xo₂ c₂

variable (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)

def PinsOverL (i : Fin D.R.m) : Prop :=
  ∃ O' : OMDat T.toCore R i T0 id, O'.c'.F = D.what₂.embLL.toRatAlgHom.fieldRange ∧
    O'.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O'.s0)

def OneMapOverL (ph : ℂ) (i : Fin D.R.m) : Prop :=
  ∃ O' : OMDat T.toCore R i T0 id, O'.c'.F = D.what₂.embLL.toRatAlgHom.fieldRange ∧
    O'.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O'.s0) ∧
      O'.OneMapOf (κ i) (v₀ i (sg0 D A)) (T.cE ((i : ℕ) + 1) O'.s0) ph

theorem OneMapOverL.pins {ph : ℂ} {i : Fin D.R.m} (h : OneMapOverL T R κ v₀ ph i) : PinsOverL T R κ v₀ i :=
  h.imp fun _ h => ⟨h.1, h.2.1⟩

end GlobalTheory.TwistField
