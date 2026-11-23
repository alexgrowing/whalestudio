import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedFramePartitionFormula
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieBaseIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieBaseAt
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adapted_frame_partition_formula : ∀ (D : D7) (O : Setup D) (c : O.s.Comp) (R : ℝ) (Gm : ∀ σ', EigMet O.s.T.Z σ')
    (hmet : ∀ σ n, O.met.hm c (some R) σ n = (O.Φ.C c).met (Gm (embOf O.κ.e σ)) n)
    (w : GlobalTheory.ShFam.Pad.Sym D.host.E →₀ ℤ), GlobalTheory.ShFam.Pad.parOf w = some R → ∀ (σ : D.what₂.LL →+* ℂ) (y : Pts (O.var c) σ)
    (t : ∀ τ : D.host.E →+* ℂ, Fin (O.S.Dw.mult τ) → (O.var c).Fnˣ) (g : (O.Φ.C c).FrameAt y),
    (O.Φ.C c).Adapted y t g 1 →
    (Real.exp (-(2 * ((adlOf (O.Φ.C c) (O.met.hm c) w).n : ℕ) * (adlOf (O.Φ.C c) (O.met.hm c) w).ci (InfinitePlace.mk σ))) *
        (cxSt D.what₂.LL).pn (O.var c) σ (adlOf (O.Φ.C c) (O.met.hm c) w).D ((adlOf (O.Φ.C c) (O.met.hm c) w).m σ)
          ((cxSt D.what₂.LL).cx (O.var c) σ (genAt (adlOf (O.Φ.C c) (O.met.hm c) w).D (under y))) y) ^ 1 =
      ‖ratVal (genAt (adlOf (O.Φ.C c) (O.met.hm c) w).D (under y) *
          ((prodPow t (GlobalTheory.ShFam.Pad.expo O.S.Dw w) : (O.var c).Fnˣ) : (O.var c).Fn)) y‖ ^ 2 *
        (O.Φ.C c).genSq (Gm (embOf O.κ.e σ)) (GlobalTheory.ShFam.Pad.expo O.S.Dw w) g := by
  first | exact @GlobalTheory.CovTop.pn_adlOf_genAt_of_adapted | exact GlobalTheory.CovTop.pn_adlOf_genAt_of_adapted | (intros; apply GlobalTheory.CovTop.pn_adlOf_genAt_of_adapted <;> assumption)
