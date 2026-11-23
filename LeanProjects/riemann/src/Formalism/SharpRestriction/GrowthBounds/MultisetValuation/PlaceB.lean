import Formalism.SharpRestriction.GrowthBounds.FormalGroupSystem

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (Y : Pend X)

def EntB (j : ℕ) (i0 : X.Pl → ℕ) (g : ℝ) : Prop :=
  ∀ (La : X.Lt j) (La' : X.Lt (j + 1)), (X.Pj j).IsLatTup La.2 → (X.Pj (j + 1)).IsLatTup La'.2 →
    ∀ (φ : Y.Frm j La La') (I : X.ColCh j) (n : X.FrI j →₀ ℕ),
      Y.geC (MvPolynomial.coeff n (applyD (X.PI j I i0) (X.ThZA Y.Kc j (Y.ThA j La La' φ)))) g

def TtL (j : ℕ) (i0 : X.Pl → ℕ) (vs : List X.Pl) (F : X.Fm j) : X.Fm j :=
  vs.foldr (fun v F' => X.Tt v (i0 v) j F') F

def FormB : Prop :=
  ∀ j < X.mm, ∀ (i0 : X.Pl → ℕ) (vs : List X.Pl) (g : ℝ), vs.Nodup → (∀ v, i0 v ≤ X.G.P.r) →
    (∀ v, v ∉ vs → i0 v = 0) → EntB X Y j i0 g →
    ∀ G ∈ X.Int j, X.vGe (j + 1) (TtL X (j + 1) i0 vs (X.Kz j G)) (g - X.dG j)

def PlaceB (j : ℕ) (v : X.Pl) (i : ℕ) (g : ℝ) : Prop :=
  (i = 0 ∧ (Y.LowAt j v g ∨ g ≤ X.gv v (j + 1) - X.alEven v)) ∨ (1 ≤ i ∧ i ≤ X.G.P.r ∧ g ≤ X.gv v (j + 1))

end Formalism.MainNotions.FormalGroupSystem.Pf
