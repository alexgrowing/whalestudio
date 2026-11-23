import Mathlib
import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsDefs
import GroundTheory.ProfiniteCohomology.PoitouTate.PoitouTateNineTermGs

noncomputable section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global GroundTheory.LocalField
  ReciprocityTheory.Gal Formalism.ConjugateSelfDual GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion

namespace PositivityTheory.Lit1.PTN

attribute [local instance 2000] Rep.hV2

def urChar (K Ω : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field Ω] [Algebra K Ω] [HasUnramifiedRoots K Ω] (N : ℕ+) (σ : Gal(Ω/K)) : ZMod (N : ℕ) :=
  GroundTheory.LocalField.Abstract.ProfiniteInteger.proj N (Multiplicative.toAdd (unramifiedDegree K Ω σ))

theorem zmodToQZ_eq_nsmul {n : ℕ} [NeZero n] (c : ZMod n) :
    zmodToQZ n c = c.val • zmodToQZ n 1 := by
  conv_lhs => rw [← ZMod.natCast_zmod_val c]
  rw [← nsmul_one, map_nsmul]

end PositivityTheory.Lit1.PTN
