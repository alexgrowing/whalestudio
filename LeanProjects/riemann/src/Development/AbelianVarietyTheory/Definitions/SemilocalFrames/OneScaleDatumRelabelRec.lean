import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SecondLabelsNonempty

noncomputable section

namespace GlobalTheory.Diag.PG

open Formalism.BasicNotions

set_option maxHeartbeats 1000000 in

def relabelRec (D : D7) (Lw : ℕ) (h : 2 ≤ Lw) : D7 :=
  { D with
    host := relabel D.host Lw h
    nd := { D.nd with }
    ntw := { D.ntw with }
    naut := { D.naut with }
    nbc := { D.nbc with }
    nexp := { D.nexp with }
    ntypes := { D.ntypes with }
    nth := { D.nth with }
    jet := { D.jet with } }

variable {D : D7} {Lw : ℕ} {h : 2 ≤ Lw}

theorem glob_relabelRec {x eps CD Cg CT : ℝ} : Glob (relabelRec D Lw h) x eps CD Cg CT ↔ Glob D x eps CD Cg CT :=
  ⟨fun G => ⟨G.1, G.2, G.3, G.4, G.5, G.6, G.7⟩, fun G => ⟨G.1, G.2, G.3, G.4, G.5, G.6, G.7⟩⟩

theorem nodes_relabelRec {x eps : ℝ} : Nodes (relabelRec D Lw h) x eps ↔ Nodes D x eps :=
  ⟨fun G => ⟨G.1, G.2, G.3⟩, fun G => ⟨G.1, G.2, G.3⟩⟩

theorem oneScale_relabelRec {x eps eta : ℝ} : OneScale (relabelRec D Lw h) x eps eta ↔ OneScale D x eps eta :=
  ⟨fun G => ⟨G.1, G.2, G.3, G.4⟩, fun G => ⟨G.1, G.2, G.3, G.4⟩⟩

theorem oneScaleDatum_relabelRec {x eps eta : ℝ} {J : ℕ} :
    OneScaleDatum (relabelRec D Lw h) x eps eta J ↔ OneScaleDatum D x eps eta J :=
  ⟨fun G => ⟨oneScale_relabelRec.1 G.1, ⟨G.2.1, G.2.2, G.2.3⟩, G.3, G.4, G.5⟩,
    fun G => ⟨oneScale_relabelRec.2 G.1, ⟨G.2.1, G.2.2, G.2.3⟩, G.3, G.4, G.5⟩⟩

theorem exists_labels_relabelRec {x eps CG : ℝ} (L : LiveLabels D x eps CG) :
    ∃ (Lw : ℕ) (h : 2 ≤ Lw), Labels (relabelRec D Lw h) x eps CG := by
  obtain ⟨Lw, h, hd⟩ := exists_deadLabels D.host
  exact ⟨Lw, h, (labels_iff _ _ _ _).2 ⟨hd, L.1, L.2, L.3⟩⟩

end GlobalTheory.Diag.PG

end
