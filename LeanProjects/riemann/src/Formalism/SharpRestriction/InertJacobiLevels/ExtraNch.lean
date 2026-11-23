import Formalism.LocalRingCardinality.DataNChoice

noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal

structure NChEmb (D : D7) where
  twI : D.what₂.places.Pl → D.ntw.Tw
  twI_l : ∀ w, D.ntw.l (twI w) = D.what₂.places.resChar w
  sd : D.what₂.places.Pl → Bool
  embW : ∀ w, D.what₂.LL →+* FractionRing (D.ntw.Ok (twI w) 1)
  embW_w : ∀ w (x : D.what₂.LL), 0 ≤ D.what₂.places.val w x ↔
    embW w x ∈ (algebraMap (D.ntw.Ok (twI w) 1) (FractionRing (D.ntw.Ok (twI w) 1))).range

set_option synthInstance.maxHeartbeats 400000 in

def nchZero (D : D7) [∀ μ j, Subsingleton (D.what₂.MtL μ j)]
    [∀ i j b k Q ψ, Subsingleton (D.nexp.MtV i j b k Q ψ)] (N : NChEmb D) : NChoice D :=
  NChoice.ofOk D N.twI N.twI_l N.sd (fun _ => ∅) (fun _ => 1) (fun _ => 1) N.embW N.embW_w (fun _ _ => 0)
    (fun w j _ _ _ b => by
      have : IsEmpty (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j)) :=
        ⟨fun i => b.ne_zero i (Subsingleton.elim _ _)⟩
      exact ⟨linearIndependent_empty_type, Subsingleton.elim _ _⟩)
    (fun _ _ _ _ _ => Subsingleton.elim _ _)

end Formalism.MainNotions.Inhab

end
