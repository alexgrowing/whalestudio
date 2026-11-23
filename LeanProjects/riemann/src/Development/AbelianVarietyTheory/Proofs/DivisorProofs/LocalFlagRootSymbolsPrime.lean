import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsAtOfNorms
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalFramesGiveFlagStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootSymbolLocalFrames

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx
open scoped Classical

namespace GlobalTheory.TrivFlag

theorem locFlag_rootSym : Hypotheses2 → HypothesesH → ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (Φ : s.Flag) (c : s.Comp) (hm : Mets (Φ.C c) (cxSt D.what₂.LL)) (p : ℕ), p.Prime → ∀ (a : ℕ → Bool), a p = true → ∀ (R : Option ℝ) (τ : D.what₂.Tau), LocFlag (fun i : Fin N => adlOf (Φ.C c) hm (rootSym S.Dw a R (DV.tauEmb D τ) i)) p := fun h2 hH D A N j S κ s Φ c hm p hp a ha R τ =>
  GlobalTheory.T.local_frames_give_flag _ p (GlobalTheory.T.root_symbol_local_frames h2 hH D A N j S κ s Φ c hm p hp a ha R τ)

end GlobalTheory.TrivFlag
