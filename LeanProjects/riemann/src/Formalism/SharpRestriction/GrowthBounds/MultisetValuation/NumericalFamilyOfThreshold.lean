import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.NcSize

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.BasicNotions Finset

def nc_Need3 (C₀ : ℝ) : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (L : SizeData₂ D) (X : Formalism.MainNotions.G.Inst D L) (Y : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts),
    C₀ ≤ K.dl1 → C₀ ≤ K.dl2 → C₀ ≤ K.Pr1 → (Formalism.MainNotions.G.rG L.sc < D.R.k ∧ 2 ≤ L.sc.x) → Formalism.MainNotions.SizesAt L →
    ∀ hT : GatTies D, Formalism.MainNotions.G.LatTied hT X Y → ∀ (u : D.what₂.Word) (w : D.what₂.places.Pl)
      (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
      1 ≤ Real.logb (D.what₂.places.resChar w) (2 * L.sc.a) →
      ∀ t0 ∈ Formalism.MainNotions.G.reps X (D.what₂.places.resChar w), ∀ j ∈ SizeData₂.lifts D,
        nc_Size D L Y u w hg t0 j ∧
        Formalism.MainNotions.FormalGroupSystem.Pr (Y.Fl u w hg).t (D.gat u w hg).P.r ((D.gat u w hg).P.lam0 (Y.vOf u w hg t0))
          ((Y.Fl u w hg).w (Y.vOf u w hg t0)) j ≤
          Formalism.MainNotions.G.Pr X K (Formalism.MainNotions.G.bL L) (D.what₂.places.resChar w) j t0

theorem numerical_closed_of_threshold (C₀ : ℝ) (h9 : 9 ≤ C₀) (h : nc_Need3 C₀) : Formalism.MainNotions.FormalGroupSystem.NumericalComparisonUniform :=
  numerical_closed_of_need C₀ fun D L X Y K h1 h2 h3 hr hs hT hL u w hg hlog t0 ht0 j hj =>
    have H := h D L X Y K h1 h2 h3 hr hs hT hL u w hg hlog t0 ht0 j hj
    ⟨nc_de X Y K hT hL u w hg t0 ht0 j hj (h9.trans h1) (h9.trans h2) hlog H.1, H.2⟩

theorem numerical_family_of_threshold (C₀ : ℝ) (h9 : 9 ≤ C₀) (h : nc_Need3 C₀) {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) :
    ∃ C₀, Formalism.MainNotions.FormalGroupSystem.NumericalComparisonFamily Fm C₀ := by
  obtain ⟨C, hC⟩ := numerical_closed_of_threshold C₀ h9 h
  exact ⟨C, fun x i => hC _ _ _ _⟩

end Formalism.MainNotions.FormalGroupSystem.Pf
