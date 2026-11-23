import Formalism.LocalToGlobal.GlobalTheory.GL4.PClsTieIdx
import Formalism.LocalToGlobal.GlobalTheory.GL4.PClsTieInt
import Formalism.LocalToGlobal.GlobalTheory.GL4.PClsTieSep

noncomputable section

open NumberField Formalism.BasicNotions

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem latT_step {D : D7} (X : Formalism.L2.Herm.FullTied D) (u : D.what₂.Word) (i : ℕ) (hi : i ≤ D.R.m)
    (c : (D.mem u).C.cls i) :
    Formalism.MainNotions.flipTwoThree.LatT (D.sp.X i) (Formalism.MainNotions.flipTwoThree.Tu D u ^ (2 * D.R.f)) (D.clsLat u i c) :=
  ⟨clsLat_int X u i hi c, clsLat_index X u i hi c⟩

def FramesStep (D : D7) (u : D.what₂.Word) (i : ℕ) : Prop :=
  ∃ e : (D.mem u).C.cls i → Fin (D.R.N i) → (D.sp.X i).V,
    (∀ c a, e c a ∈ Formalism.MainNotions.flipTwoThree.dualSub (D.sp.X i) (D.clsLat u i c)) ∧
    ∀ c c', Formalism.MainNotions.flipTwoThree.SameCls (D.sp.X i) (Formalism.MainNotions.flipTwoThree.Tu D u * D.host.g 0 * D.host.g 1) (D.clsLat u i c)
      (D.clsLat u i c') (e c) (e c') → c = c'

def ClauseP (D : D7) (u : D.what₂.Word) : Prop :=
  ∃ LP : (D.fm u).clsP → Submodule (𝓞 D.host.E) D.sp.X'.V,
    (∀ c, Submodule.IsLattice D.host.E (LP c) ∧ Formalism.MainNotions.flipTwoThree.LatT D.sp.X' 1 (LP c)) ∧
    ∃ e : (D.fm u).clsP → Fin (D.R.N D.R.m - 1) → D.sp.X'.V,
      (∀ c a, e c a ∈ Formalism.MainNotions.flipTwoThree.dualSub D.sp.X' (LP c)) ∧
      ∀ c c', Formalism.MainNotions.flipTwoThree.SameCls D.sp.X' (Formalism.MainNotions.flipTwoThree.Tu D u * D.host.g 0 * D.host.g 1) (LP c) (LP c') (e c) (e c') →
        c = c'

theorem clsTie_of {D : D7} (X : Formalism.L2.Herm.FullTied D) (u : D.what₂.Word)
    (hF : ∀ i ≤ D.R.m, FramesStep D u i) (hP : ClauseP D u) : Formalism.MainNotions.flipTwoThree.ClsTie D u :=
  ⟨fun i hi => ⟨fun c => latT_step X u i hi c, hF i hi⟩, hP⟩

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
