import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AuxiliaryPrimeMemAvoidedPrimes
import Development.AutomorphicArithmetic.CharacterBoxes.TwistForm

noncomputable section

namespace UpperTheory.Top

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.HC GlobalTheory.EX

abbrev FReq : Type 1 := ∀ (_ : Scale) (φ : Frame) (_ : HostAx φ) (_ : Finset φ.A) (_ : ℕ), Prop

namespace FReq

variable (G : FReq)

def req : HostReq := fun _ s R H _ => G s R.toFrame H.toHostAx H.TT R.t

def At {D : D7} (L : SizeData₂ D) : Prop := G L.sc D.R.toFrame D.host.toHostAx D.host.TT D.R.t

def pt : PtProp := fun _ L _ _ _ _ _ _ _ => G.At L

def cls (la : ℝ) : FamClass := fun Fm =>
  Fm.toFamCore.Windows la ∧ ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, G.At (Fm.L x i)

theorem at_of_from {C : FC} {p : Pt C} {R : Ranks} {H : Host R} {a b : R.A → ℤ} {M : ℕ} {c : Fin M → Fin (R.k - 2) → Bool}
    {u0 : ℕ} (h : p.From H a b c u0) (hG : G p.L.sc R.toFrame H.toHostAx H.TT R.t) : G.At p.L := by
  have h1 := h.1
  have h2 := h.field
  have h3 := h.2.1
  subst h1
  have h4 : p.D.host.TT = H.TT := Finset.image_injective (Formalism.HC.Frame.A.val_injective _) h3
  unfold At
  rw [eq_of_heq h2, h4]
  exact hG

end FReq

def ExD (𝒜 : FamClass) (cT : ℝ → ℝ → ℝ) : Prop :=
  ∀ (la : ℝ) (G : FReq), 1 < la → HostExW la G.req →
    DC.DesignChoices (DC.WithTw fun Fm => 𝒜 Fm ∧ G.cls la Fm) 3 cT

def GChi (ψ : PChar) : FReq := fun s _ H TT t =>
  EAtH (Level.cyc ψ) H.toHostRaw TT s.x s.eps 4 ∧ VVle H.E t (Real.sqrt s.b)

end UpperTheory.Top

end
