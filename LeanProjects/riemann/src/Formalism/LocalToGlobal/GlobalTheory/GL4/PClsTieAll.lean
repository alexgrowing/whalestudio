import Formalism.LocalToGlobal.GlobalTheory.GL4.PClsTieP

noncomputable section

open NumberField Formalism.BasicNotions

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def FramesP {D : D7} (X : Formalism.L2.Herm.FullTied D) (u : D.what₂.Word) : Prop :=
  ∃ e : (D.fm u).clsP → Fin (D.R.N D.R.m - 1) → D.sp.X'.V,
    (∀ c a, e c a ∈ Formalism.MainNotions.flipTwoThree.dualSub D.sp.X' ((X.atT u).lattice₂ c)) ∧
    ∀ c c', Formalism.MainNotions.flipTwoThree.SameCls D.sp.X' (Formalism.MainNotions.flipTwoThree.Tu D u * D.host.g 0 * D.host.g 1) ((X.atT u).lattice₂ c)
      ((X.atT u).lattice₂ c') (e c) (e c') → c = c'

theorem clauseP_of_framesP {D : D7} (X : Formalism.L2.Herm.FullTied D) (u : D.what₂.Word) (hF : FramesP X u) : ClauseP D u :=
  ⟨(X.atT u).lattice₂, fun c => localLattice_selfDual X u c, hF⟩

theorem clsTie_of_frames {D : D7} (X : Formalism.L2.Herm.FullTied D) (u : D.what₂.Word)
    (hF : ∀ i ≤ D.R.m, FramesStep D u i) (hP : FramesP X u) : Formalism.MainNotions.flipTwoThree.ClsTie D u :=
  clsTie_of X u hF (clauseP_of_framesP X u hP)

theorem ClsTieOfTied_of_frames
    (hF : ∀ D : D7, Formalism.L2.Herm.FullTied D → ∀ u i, i ≤ D.R.m → FramesStep D u i)
    (hP : ∀ (D : D7) (X : Formalism.L2.Herm.FullTied D) u, FramesP X u) : ClassCompatibilityOfRowCompatibility :=
  fun D X u => clsTie_of_frames X u (fun i hi => hF D X u i hi) (hP D X u)

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
