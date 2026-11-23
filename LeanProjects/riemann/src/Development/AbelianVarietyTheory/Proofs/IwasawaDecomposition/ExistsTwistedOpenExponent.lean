import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RootsOfUnityRingLeWittIntegers
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideMultiplicityCharacter
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.HeightCounting.FitTwExp

set_option maxHeartbeats 8000000 in

theorem exists_twOpen_expRel : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D' : D7) (b : NBuilt hL D'), Elem b.D → GlobalTheory.RowTie.ChebSplit b.D.nd → ∃ Tw : TwOpen (withLoc b.L) (chL b.L b.C) (cfL b.L b.cf) (tpL b.L b.tp) (mtL b.L b.M) b.low, ExpRel b.L b.Bs.exp Tw.exp := by
  intro hL D' b hE hC
  obtain ⟨Tw⟩ := GlobalTheory.HeightCounting.FitTw.nonempty_twOpen b.D b.cf b.jE b.A b.low b.Pq b.S b.hL b.eig b.θ b.Bs b.M b.C b.tp b.ch b.mt hE.star hE.int hE.split hC b.big b.L b.Sp b.Au
  refine ⟨{ Tw with exp := GlobalTheory.HeightCounting.FitTw.expL b.L b.Bs.exp, ch := GlobalTheory.HeightCounting.FitTw.chSideL b.Sp b.ch }, ?_⟩
  exact
    { tau := fun h => h
      pl := fun _ _ _ _ _ _ _ _ _ => rfl
      reads := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ h => h }

end GlobalTheory.HeightCounting.FitTwExp

end
