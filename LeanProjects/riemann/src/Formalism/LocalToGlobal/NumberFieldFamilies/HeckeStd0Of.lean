import Formalism.LocalToGlobal.NumberFieldFamilies.IsLocalizedOfSpan

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Module Polynomial

namespace Formalism.L2.Fam.NPC.LatticeFinitenessFree

open Formalism.L2.Fam.NPC

set_option synthInstance.maxHeartbeats 400000

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (B : LocBase0 H what₂)

def latJ (j : ℕ) (w : what₂.places.Pl) : Set (what₂.MtL (what₂.muTw w) j) :=
  {x | what₂.jMt (what₂.muTw w) j x ∈ (what₂.MtLat (what₂.muTw w) j).gen}

def HeckeCommL : Prop := ∀ j w, 1 ≤ j → j ≤ R.m → ∀ v k v' k', GenAt0 H (what₂.places.resChar w) (B.Qw w) v k →
  GenAt0 H (what₂.places.resChar w) (B.Qw w) v' k' → Commute (B.hL j w v k) (B.hL j w v' k')

def HeckeInt : Prop := ∀ j w, 1 ≤ j → j ≤ R.m → ∀ v k, GenAt0 H (what₂.places.resChar w) (B.Qw w) v k → ∀ x ∈ latJ j w,
  ∃ (F : Finset (what₂.MtL (what₂.muTw w) j)) (c : what₂.MtL (what₂.muTw w) j → what₂.LL), (↑F ⊆ latJ j w) ∧
    (∀ y ∈ F, 0 ≤ what₂.places.val w (c y)) ∧ B.hL j w v k x = ∑ y ∈ F, c y • y

variable {B}

theorem span_latJ (j : ℕ) (w : what₂.places.Pl) : Submodule.span what₂.LL (latJ j w) = ⊤ := by
  have hb := what₂.jMt_basis (what₂.muTw w) j (Module.Free.chooseBasis what₂.LL _)
  refine span_top_of_image what₂.embLL (what₂.jMt (what₂.muTw w) j) _ hb.1 hb.2 _ ?_
  have h := (what₂.MtLat (what₂.muTw w) j).span_top
  refine le_antisymm le_top (h ▸ Submodule.span_mono fun v hv => ?_)
  obtain ⟨x, rfl⟩ := what₂.MtLat_sub _ _ v hv
  exact ⟨x, hv, rfl⟩

theorem span_iV (j : ℕ) (w : what₂.places.Pl) :
    Submodule.span (FractionRing (B.Oc j w)) (B.iV j w '' latJ j w) = ⊤ :=
  span_image_top (B.ec j w) (B.iV j w) (Module.Free.chooseBasis what₂.LL _) (B.iV_basis j w _).2 _ (span_latJ j w)

def latN (j : ℕ) (w : what₂.places.Pl) : Submodule (B.Oc j w) (B.V j w) := Submodule.span (B.Oc j w) (B.iV j w '' latJ j w)

end Formalism.L2.Fam.NPC.LatticeFinitenessFree
