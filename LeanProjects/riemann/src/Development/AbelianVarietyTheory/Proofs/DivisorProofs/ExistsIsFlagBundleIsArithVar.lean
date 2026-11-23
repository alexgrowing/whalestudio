import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialFlagSmoothArithmetic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellVarietyDimensionCounts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkStepMono
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalSubbundleRankStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoInclLastStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagVarietyLiftUniqueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagVarietyLiftExistsStatement

noncomputable section

open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open GlobalTheory.QCoh (freeModule)

namespace GlobalTheory.FlagZ.Univ

variable (ι : Type) [Fintype ι] (N : ℕ)

def flag (τ : ι) : Vert.Flag ((Scheme.Modules.pullback (flStr ι N)).obj (freeModule (Sp ℤ) (Fin N))) N where
  F := F ι N τ
  ι := incl ι N τ
  isSubbundle i := (GlobalTheory.T.tautological_subbundle_rank ι N τ i).2
  isVB i := (GlobalTheory.T.tautological_subbundle_rank ι N τ i).1
  step := step ι N τ
  step_ι := step_incl ι N τ
  isIso_last := GlobalTheory.T.isIso_incl_last' ι N τ

theorem isFlagBundle_flag :
    IsFlagBundle (flStr ι N) (fun _ : ι => freeModule (Sp ℤ) (Fin N)) (fun _ => N) (flag ι N) :=
  fun T g fl' =>
    have ⟨g', h⟩ := GlobalTheory.T.flag_variety_lift_exists ι N T g fl'
    ⟨g', h, fun _ h' => GlobalTheory.T.flag_variety_lift_unique ι N T g fl' _ _ h' h⟩

end GlobalTheory.FlagZ.Univ
