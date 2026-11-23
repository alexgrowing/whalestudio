import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDeltaDelAtOwnAt

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT

namespace GlobalTheory.BigOn

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Any

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def scalOf (R : RealDat D A Ks) (F : Face D A) : (type_of% R.lam) × ℝ :=
  haveI : Nonempty ((type_of% R.lam) × ℝ) := ⟨(R.lam, 0)⟩
  Classical.epsilon fun q => (reScal R q.1 q.2).Char F

def charOf (R : RealDat D A Ks) (F : Face D A) : RealDat D A Ks := reScal R (scalOf R F).1 (scalOf R F).2

end Any

variable {J : CoreJ D} [Algebra J.Q.c.F D.what₂.LL] {R : RealDat D A J.Q.c.F}
  {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}

set_option maxHeartbeats 1000000 in

def reFw (fw : FWTie J R κ v₀) (F : Face D A) : FWTie J (charOf R F) κ v₀ := { fw with }

set_option maxHeartbeats 1000000 in

def reOM {i : Fin D.R.m} (O : OMDat J.toCore R i Unit (fun _ => A.μ0)) (F : Face D A) :
    OMDat J.toCore (charOf R F) i Unit (fun _ => A.μ0) := { O with }

end GlobalTheory.BigOn

end
