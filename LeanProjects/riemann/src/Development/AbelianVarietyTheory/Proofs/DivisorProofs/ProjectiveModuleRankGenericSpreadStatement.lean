import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveModuleRankGenericSpread
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplitting
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.ArLieBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projective_module_rank_generic_spread : ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (g M r D : ℕ) (P : Matrix (Fin g) (Fin g) R) (h : Fin M → Fin g → R), D ≠ 0 → P * P = (D : R) • P → (∀ (K : Type) [Field K] [CharZero K] (ψ : R →+* K), (P.map ψ).rank = r) → (∃ n : ℕ, n ≠ 0 ∧ ∀ i, Pi.single i (n : R) ∈ Submodule.span R (Set.range h)) → ∃ (n m : ℕ) (A : Fin m → R), n ≠ 0 ∧ (n : R) ∈ (Ideal.span (Set.range A)).radical ∧ ∀ (R' : Type) [CommRing R'] [IsDomain R'] [CharZero R'] (ψ : R →+* R'), (∃ k, ∀ k', ψ (A k) ∣ ψ (A k')) → ∃ (N : ℕ) (U : Matrix (Fin g) (Fin r) R') (I : Fin r → Fin M), N ≠ 0 ∧ IsSplitting D (P.map ψ) (fun j i => ψ (h j i)) N U I := by
  first | exact @GlobalTheory.ArLieBase.MaxMinor.maxMinors_split | exact GlobalTheory.ArLieBase.MaxMinor.maxMinors_split | (intros; apply GlobalTheory.ArLieBase.MaxMinor.maxMinors_split <;> assumption)
