import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelationFlagsDualAdeles
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNonarchimedeanW
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag GlobalTheory.WholeFlag GlobalTheory.ConstLat
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relation_flags_dual_adeles : ∀ {F : Type} [Field F] [NumberField F] {Y : Var F} {C : CxSt F} {g : ℕ} (A A' B B' : Fin g → Adl C Y) (p n : ℕ),
    p.Prime → n ≠ 0 → DualAt A B p → DualAt A' B' p → (∀ k, RelData A A' p n k) →
    ∀ k, RelFlag (fun i : Fin (g + g) => Sum.elim A B (finSumFinEquiv.symm i))
      (fun i : Fin (g + g) => Sum.elim A' B' (finSumFinEquiv.symm i)) p n k := by
  first | exact @GlobalTheory.RelGlue.relFlag_glue | exact GlobalTheory.RelGlue.relFlag_glue | (intros; apply GlobalTheory.RelGlue.relFlag_glue <;> assumption)
