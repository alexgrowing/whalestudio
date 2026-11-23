import Formalism.LocalRingCardinality.DataAmbForm
import Formalism.LocalRingCardinality.DataDIV
import Formalism.LocalRingCardinality.DataParams₂

noncomputable section

namespace Formalism.BasicNotions

open NumberField

namespace DV

variable {D : D7}

def UL (A : AmbForm D (RowSide.sharp D)) : Set (A.MtH D.what₂.mu0).V :=
  {u | A.jAmb D.what₂.mu0 u ∈ (RowSide.sharp D).Usp D.what₂.mu0}

def quotNorm (A : AmbForm D (RowSide.sharp D)) (v : InfinitePlace D.what₂.LL) (x : (A.MtH D.what₂.mu0).V) : ℝ :=
  ⨅ u : UL A, Formalism.HermitianLatticesTheory.normAt (A.MtH D.what₂.mu0).b (A.MtH D.what₂.mu0).X v (x + u)

end DV

structure EigIdx (D : D7) (X : DivX D) where
  Pi : Type
  [fin : Fintype Pi]
  [dec : DecidableEq Pi]
  cOf : D.what₂.FT → Pi
  lam_const : ∀ j ∈ SizeData₂.lifts D, ∀ π π' e, D.what₂.isot j π ≠ ⊥ → D.what₂.isot j π' ≠ ⊥ → cOf π = cOf π' →
    X.logLam j π e = X.logLam j π' e

attribute [instance] EigIdx.fin EigIdx.dec

def DV.ftP {D : D7} {X : DivX D} (E : EigIdx D X) (σ : Fin D.what₂.Drows) : E.Pi := E.cOf (D.what₂.ft σ)

def DV.sum₃ {D : D7} {X : DivX D} (E : EigIdx D X) (j : ℕ) (c : E.Pi) : Submodule ℂ (D.what₂.Mj j) :=
  ⨆ π, ⨆ (_ : E.cOf π = c), D.what₂.isot j π

def DV.EEcpart (D : D7) {X : DivX D} (E : EigIdx D X) (c : E.Pi) : Submodule ℂ D.what₂.EE :=
  Submodule.span ℂ (D.what₂.onb '' {σ | E.cOf (D.what₂.ft σ) = c})

open Classical in

def DV.logLamC {D : D7} {X : DivX D} (E : EigIdx D X) (j : ℕ) (c : E.Pi) (e : D.what₂.LL →+* ℂ) : ℝ :=
  if h : ∃ π, E.cOf π = c ∧ D.what₂.isot j π ≠ ⊥ then X.logLam j h.choose e else 0

def RRMetricDef (D : D7) (X : DivX D) (A : AmbForm D (RowSide.sharp D)) (E : EigIdx D X) : Prop :=
  ∀ v : InfinitePlace D.what₂.LL, v ≠ InfinitePlace.mk D.what₂.embLL →
    ∀ (x : E.Pi → D.div.RR.V) (q : E.Pi → (A.MtH D.what₂.mu0).V),
      (∀ c, A.jAmb D.what₂.mu0 (q c) ∈ (RowSide.sharp D).V0 D.what₂.mu0) →
      (∀ c, D.jEE (x c) = (RowSide.sharp D).iota D.what₂.mu0 (A.jAmb D.what₂.mu0 (q c))) →
      (∀ c, D.jEE (x c) ∈ DV.EEcpart D E c) →
        Formalism.HermitianLatticesTheory.normAt D.div.RR.b D.div.RR.X v (∑ c, x c) ^ 2 =
          ∑ c, X.kapR v.embedding * Real.exp (∑ j ∈ SizeData₂.lifts D, DV.logLamC E j c v.embedding) *
            DV.quotNorm A v (q c) ^ 2

def DV.RowsRational (D : D7) {X : DivX D} (A : AmbForm D (RowSide.sharp D)) (E : EigIdx D X) : Prop :=
  Submodule.span ℂ (A.jAmb D.what₂.mu0 '' {x | A.jAmb D.what₂.mu0 x ∈ (RowSide.sharp D).V0 D.what₂.mu0}) =
    (RowSide.sharp D).V0 D.what₂.mu0 ∧
  Submodule.span ℂ (A.jAmb D.what₂.mu0 '' DV.UL A) = (RowSide.sharp D).Usp D.what₂.mu0 ∧
  (∀ x : (A.MtH D.what₂.mu0).V, A.jAmb D.what₂.mu0 x ∈ (RowSide.sharp D).V0 D.what₂.mu0 →
    ∃ y : D.div.RR.V, D.jEE y = (RowSide.sharp D).iota D.what₂.mu0 (A.jAmb D.what₂.mu0 x)) ∧
  ∀ c : E.Pi, Submodule.span ℂ (D.jEE '' {y | D.jEE y ∈ DV.EEcpart D E c}) = DV.EEcpart D E c

end Formalism.BasicNotions

end
