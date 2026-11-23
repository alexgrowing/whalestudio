import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmAbelianFieldDataOfToricRatio
import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SizeAt
import Development.AbelianVarietyTheory.Definitions.Divisors.TieTest
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NuHTwisted
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop NumberField IsDedekindDomain
open GlobalTheory.FunObj.SqNum (nuH halfRank IsTor)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_abelian_field_data_of_toric_ratio : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (CF : ℝ) (d : FunIn p CF), p.Rows → Fitted (@Comparison₂) p CF d → GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.ToricRatioConjugates → (∃ (_ : IsCMField D.host.E) (_ : IsAbelianGalois ℚ D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData D.host.d (GlobalTheory.FunObj.SqNum.cmPhi D) ∧
    GlobalTheory.CMVal.IsBaseCond (GlobalTheory.FunObj.SqNum.condF d.G.pl) ∧ ∃ Λ, GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice D.host.d Λ) → (∀ (i j : Fin D.R.m) (s : ℕ), 1 ≤ s → s ≤ halfRank D i j → ∀ c : Option Bool,
    ∃ x, IsTor d.G i j s (fam d.G p.P.A3.A.μ0 i j c) x ∧ x ≠ 0 ∧ (∀ Λ, GlobalTheory.CMVal.IsHeckeL (fam d.G p.P.A3.A.μ0 i j c) Λ → x = Λ s) ∧
      ∀ Λ, GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice D.host.d Λ → IsAlgebraic ℚ (GlobalTheory.CMVal.beta D.host.E D.host.d s (GlobalTheory.FunObj.SqNum.kap D 1 i j s) Λ x)) →
  ∀ w : D.what₂.places.Pl, TwistedAt D w → ∀ (i j : Fin D.R.m) (s : ℕ) (Λ Λd : ℂ → ℂ) (z : D.what₂.LL), 1 ≤ s → s ≤ halfRank D i j →
    GlobalTheory.CMVal.IsHeckeL (nuH d.G p.P.A3.A.μ0 i j * p.R.C.delAt (D.what₂.places.resChar w) * p.Tp.psi w) Λ →
    GlobalTheory.CMVal.IsHeckeL (nuH d.G p.P.A3.A.μ0 i j * p.R.C.delAt (D.what₂.places.resChar w)) Λd →
    D.what₂.embLL z * Λd s = Λ s →
    (Formalism.DivisionValues.vw (D.plEq w) z : ℝ) ≤ (Formalism.DivisionValues.vw (D.plEq w) ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) : ℝ) / ((D.what₂.places.resChar w : ℕ) : ℝ) ^ 2 := by
  first | exact @GlobalTheory.ThmAUpper.val_bound_twisted | exact GlobalTheory.ThmAUpper.val_bound_twisted | (intros; apply GlobalTheory.ThmAUpper.val_bound_twisted <;> assumption)
