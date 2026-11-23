import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalFlagRootSymbolsPrime
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsAtOfNorms
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_flag_root_symbols_prime : Hypotheses2 → HypothesesH → ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (Φ : s.Flag) (c : s.Comp) (hm : Mets (Φ.C c) (cxSt D.what₂.LL)) (p : ℕ), p.Prime → ∀ (a : ℕ → Bool), a p = true → ∀ (R : Option ℝ) (τ : D.what₂.Tau), LocFlag (fun i : Fin N => adlOf (Φ.C c) hm (rootSym S.Dw a R (DV.tauEmb D τ) i)) p := by
  first | exact @GlobalTheory.TrivFlag.locFlag_rootSym | exact GlobalTheory.TrivFlag.locFlag_rootSym | (intros; apply GlobalTheory.TrivFlag.locFlag_rootSym <;> assumption)
