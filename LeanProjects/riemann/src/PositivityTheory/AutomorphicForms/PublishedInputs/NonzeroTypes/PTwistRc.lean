import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.ScalarOnInertiaProp

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.TNZ

theorem step_twistRc : TwistRestrictionProp := by
  intro E Ω _ _ _ _ _ A w h a ha ε rc H d X _ _ σ hs hi η hη
  refine ⟨isSmooth_twist hs hη.detChar, isIrreducible_twist hi _, ?_⟩
  rw [← IrrGL.tw_of (hχ := hη), H.twist, H.one]

end UpperTheory.TNZ
