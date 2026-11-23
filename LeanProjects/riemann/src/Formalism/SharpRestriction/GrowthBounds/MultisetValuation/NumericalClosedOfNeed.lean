import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.NcModsub

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.BasicNotions Finset

variable {D : Formalism.BasicNotions.D7} {L : SizeData₂ D}

open Classical in
theorem nc_loc (X : Formalism.MainNotions.G.Inst D L) (Y : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts) (hT : GatTies D)
    (hL : Formalism.MainNotions.G.LatTied hT X Y) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (t0 : Formalism.MainNotions.G.HH D)
    (ht0 : t0 ∈ Formalism.MainNotions.G.reps X (D.what₂.places.resChar w)) (j : ℕ) (hj : j ∈ SizeData₂.lifts D) :
    nc_Loc D L X Y K hT u w hg t0 j := by
  obtain ⟨hal, hal0, hcap, hcap0⟩ := nc_ties X Y hT hL u w hg t0 ht0 j hj
  exact ⟨nc_gU_eq X Y hT hL u w hg t0 ht0 K j, growth_exclusion_sum_eq X Y hT hL u w hg t0 ht0 K j,
    hal, hal0, hcap, hcap0, fun s _ e he => nc_excl X Y hT hL u w hg t0 ht0 s e he⟩

def nc_Need2 (C₀ : ℝ) : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (L : SizeData₂ D) (X : Formalism.MainNotions.G.Inst D L) (Y : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts),
    C₀ ≤ K.dl1 → C₀ ≤ K.dl2 → C₀ ≤ K.Pr1 → (Formalism.MainNotions.G.rG L.sc < D.R.k ∧ 2 ≤ L.sc.x) → Formalism.MainNotions.SizesAt L →
    ∀ hT : GatTies D, Formalism.MainNotions.G.LatTied hT X Y → ∀ (u : D.what₂.Word) (w : D.what₂.places.Pl)
      (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
      1 ≤ Real.logb (D.what₂.places.resChar w) (2 * L.sc.a) →
      ∀ t0 ∈ Formalism.MainNotions.G.reps X (D.what₂.places.resChar w), ∀ j ∈ SizeData₂.lifts D,
        nc_De D L X Y K u w hg t0 j ∧
        Formalism.MainNotions.FormalGroupSystem.Pr (Y.Fl u w hg).t (D.gat u w hg).P.r ((D.gat u w hg).P.lam0 (Y.vOf u w hg t0))
          ((Y.Fl u w hg).w (Y.vOf u w hg t0)) j ≤
          Formalism.MainNotions.G.Pr X K (Formalism.MainNotions.G.bL L) (D.what₂.places.resChar w) j t0

theorem nc_need_of (C₀ : ℝ) (h : nc_Need2 C₀) : nc_Need C₀ := by
  intro D L X Y K h1 h2 h3 h4 h5 hT hL u w hg hlog t0 ht0 j hj
  obtain ⟨hde, hpr⟩ := h D L X Y K h1 h2 h3 h4 h5 hT hL u w hg hlog t0 ht0 j hj
  exact ⟨nc_loc X Y K hT hL u w hg t0 ht0 j hj, hde, hpr⟩

theorem numerical_closed_of_need (C₀ : ℝ) (h : nc_Need2 C₀) : Formalism.MainNotions.FormalGroupSystem.NumericalComparisonUniform :=
  stmtNumE_of C₀ (nc_need_of C₀ h)

end Formalism.MainNotions.FormalGroupSystem.Pf
