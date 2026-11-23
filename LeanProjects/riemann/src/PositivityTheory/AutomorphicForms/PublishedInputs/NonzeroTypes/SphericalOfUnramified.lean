import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.ScalarOnInertiaProp

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.TNZ

theorem step_sphOfUnr : SphericalOfUnramifiedProp := by
  intro E Ω _ _ _ _ _ A w h a ha ε rc H d v hv hd
  obtain ⟨⟨n, c⟩, rfl⟩ := H.bij.2 v
  have hn : n = d := by rw [← hd, H.dim]
  subst hn
  exact ⟨c.rep.V, inferInstance, inferInstance, c.rep.ρ, c.rep.smooth, c.rep.irr, (H.sph ⟨n, c⟩).2 hv,
    congrArg rc (IrrGL.of_rep ⟨n, c⟩)⟩

end UpperTheory.TNZ
