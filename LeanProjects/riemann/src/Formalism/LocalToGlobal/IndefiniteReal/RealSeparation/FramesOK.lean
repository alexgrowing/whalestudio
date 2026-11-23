import Formalism.LocalToGlobal.IndefiniteReal.RealSeparation.NormalFrame0
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Datum Formalism.IndefR.Links NumberField

namespace Formalism.IndefR.Mi

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def betaY (Rl : RealDat3 D A3 Ks) (j : ℕ) : GL (Fin (D.sp.Y j).rank) (EAf D) :=
  if h : j ≤ D.R.m then
    (show GL (Fin (Yc D j).rank) (EAf D) = GL (Fin (D.sp.Y j).rank) (EAf D) by
      show GL (Fin (D.sp.Y (min j D.R.m)).rank) (EAf D) = _
      rw [Nat.min_eq_left h]) ▸ Rl.βY j
  else 1

def IsDPlaces (Sd : Finset (Pl D.host.E)) : Prop :=
  (∀ PP ∈ Sd, ¬ Lev.IsConjPl (D := D) PP PP ∧ ((D.host.d : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) ∧
  (∀ PP ∈ Sd, ∀ PP' ∈ Sd, Lev.IsConjPl (D := D) PP PP' → PP = PP') ∧
  ∀ PP : Pl D.host.E, ¬ Lev.IsConjPl (D := D) PP PP → ((D.host.d : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal →
    PP ∈ Sd ∨ ∃ PP' ∈ Sd, Lev.IsConjPl (D := D) PP PP'

open Classical in

def FramesOK (Rl : RealDat3 D A3 Ks) (Sd : Finset (Pl D.host.E)) : Prop :=
  ∃ (e ev : ∀ j : ℕ, ℕ → Fin (D.sp.Y j).rank → D.host.E) (z : ∀ j : ℕ, Fin (D.sp.Y j).rank → D.host.E)
    (κ : ℕ → ℕ → D.host.E) (s : ℕ → D.host.E),
    (∀ t : T, NormalFrames (betaY Rl) e ev z κ s (Rl.Pg ∪ Rl.Q t ∪ Sd) Rl.Pg ∧
      NormalFrame0 (betaY Rl 0) (Rl.Pg ∪ Rl.Q t ∪ Sd) Rl.Pg) ∧
    ∀ i : Fin D.R.m, ∃ (eW : Fin (D.sp.Y 0).rank ≃ Fin (D.sp.W ((i : ℕ) + 1)).rank)
      (ι : GL (Fin (D.sp.W ((i : ℕ) + 1)).rank) (EAf D)),
      VertexAt ((i : ℕ) + 1) (betaY Rl 0) (Rl.βW i) eW ι Rl.Pg

end Formalism.IndefR.Mi

end
