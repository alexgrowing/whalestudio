import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RootsOfUnityRingLeWittIntegers
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.OntoAlong
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.FinalJoin2 GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.Plug GlobalTheory.PlugPt

namespace GlobalTheory.ExpTiesOfLayer

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem hasExp_of_layer : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL), HasExp (GlobalTheory.HeightCounting.NE hL) ∧ ∀ (E : NExt hL), (∀ K B f T w Z Wt p0 t nch n xd c, E K B f T w Z Wt p0 t nch n xd c → Nonempty (GlobalTheory.HeightCounting.NE hL K B f T w Z Wt p0 t nch n xd c)) → HasExp E := by
  intro hL
  have hNE : HasExp (GlobalTheory.HeightCounting.NE hL) := by
    intro K B f T w Z Wt p0 t nch n xd c y
    have hg := c.row.grp
    refine ⟨⟨⟨⟨⟨y.ser.ex⟩, ⟨fun g => (hg.lvl0 g).symm, ?_⟩, ?_⟩⟩, PUnit.unit⟩⟩
    · intro i b u hu
      obtain ⟨x, hx, hx'⟩ := hg.psi0 u hu i b
      exact ⟨x, hx, hx'⟩
    · intro i j b a _
      rw [y.xd i ((j : ℕ) + 1) b (by omega) (by omega)]
      exact Set.mem_univ _
  exact ⟨hNE, fun E hE K B f T w Z Wt p0 t nch n xd c e => by
    obtain ⟨y⟩ := hE K B f T w Z Wt p0 t nch n xd c e
    exact hNE K B f T w Z Wt p0 t nch n xd c y⟩

end GlobalTheory.ExpTiesOfLayer
