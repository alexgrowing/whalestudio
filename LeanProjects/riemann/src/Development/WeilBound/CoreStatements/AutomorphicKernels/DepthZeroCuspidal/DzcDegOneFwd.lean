import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.DepthZeroCuspidal.DegOneOfChar
import Development.WeilBound.CoreStatements.AutomorphicKernels.DepthZeroCuspidal.FixedOfCharNeBotIff
import Development.WeilBound.CoreStatements.AutomorphicKernels.DepthZeroCuspidal.TameLpOfCharIff
import Development.WeilBound.CoreStatements.AutomorphicKernels.DepthZeroCuspidal.LeviInductionForms

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.LocalParametersCuspidal.DZC

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem dzc_deg_one_fwd (rc : IrrGL (w.adicCompletion E) → WD h) (hrc : IsRecLit h rc)
    (x : IrrGL (w.adicCompletion E)) (hx : x.1 = 1) :
    fixed x.rep (KOne (w.adicCompletion E) (Fin x.1)) ≠ ⊥ → IsTameWD (rc x) := by
  obtain ⟨a, ha, ε, -, H⟩ := hrc
  obtain ⟨χ, hχ, rfl⟩ := deg_one_ofChar x hx
  rw [ofChar_fixed_iff, H.one, tame_lpOfChar_iff]
  exact fun h1 σ hσ => h1 _ (wild_to_unitsOne a ha σ hσ)

end PositivityTheory.LocalParametersCuspidal.DZC

end
