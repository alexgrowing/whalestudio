import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReversedFlagLocalHeightLogFormula
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HalfFlag
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag GlobalTheory.WholeFlag
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reversed_flag_local_height_log_formula : ∀ {F : Type} [Field F] [NumberField F] {Y : Var F} {C : CxSt F} {g N : ℕ} (h : N = g + g)
    (A B : Fin g → Adl C Y) (p : ℕ),
    (∀ k x, UnitAt x (genAt (B k).D x * genAt (A (Fin.rev k)).D x)) →
    (∀ k v, resP v = p → ∀ (e : Ext v) (y : AlgPt Y), (B k).lg v e y = -(A (Fin.rev k)).lg v e y +
      Real.log (e.w (GlobalTheory.TrueGeo.valAt y.1 (genAt (B k).D (below y.1) * genAt (A (Fin.rev k)).D (below y.1))))) →
    HalfFlag A p →
    LocFlag (fun i : Fin N => Sum.elim A B (finSumFinEquiv.symm (finCongr h i))) p := by
  first | exact @GlobalTheory.HalfGlue.locFlag_of_halfFlag | exact GlobalTheory.HalfGlue.locFlag_of_halfFlag | (intros; apply GlobalTheory.HalfGlue.locFlag_of_halfFlag <;> assumption)
