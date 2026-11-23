import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefCombinationOfPartialIndicators
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemConeOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.CoverNorm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nef_combination_of_partial_indicators : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {d : ℕ}, IsArithVar p d → ∀ (T : Type) [Fintype T] (N : ℕ) (M : T × Fin N → HermLB p) (l : ℕ), (∀ τ : T, ∀ i : ℕ, i < N → NefOver (ArInt.comb M fun x => if x.1 = τ ∧ x.2.val < i then -1 else 0) l) → (∀ τ : T, NefOver (ArInt.comb M fun x => if x.1 = τ then 1 else 0) l ∧ NefOver (ArInt.comb M fun x => if x.1 = τ then -1 else 0) l) → ∀ n : T → Fin N → ℤ, (∀ τ, Antitone (n τ)) → NefOver (ArInt.comb M fun x => -n x.1 x.2) l := by
  first | exact @GlobalTheory.HtNefAbel.nefOver_comb_of_antitone | exact GlobalTheory.HtNefAbel.nefOver_comb_of_antitone | (intros; apply GlobalTheory.HtNefAbel.nefOver_comb_of_antitone <;> assumption)
