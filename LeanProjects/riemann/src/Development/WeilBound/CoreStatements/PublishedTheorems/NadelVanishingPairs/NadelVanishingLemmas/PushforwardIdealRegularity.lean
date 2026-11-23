import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOrdSubOneLeOrdWedgeDifferentials
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberPullbackProportionalOfProporti
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PushforwardIdealRegularity
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.pushforward_ideal_regularity : ∀ (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (s : Y ⟶ X) [IsDominant s], Function.Bijective (functionFieldMap s) → ∀ (D : CartierDiv Y) (J : X.IdealSheafData), (∀ (U : X.affineOpens) (f : Γ(X, U.1)), f ∈ J.ideal U ↔ ∀ (y : Y) (hy : s y ∈ U.1), D.RegularAt y (functionFieldMap s (fnOf U.1 (gen_mem hy) f))) → (∀ (x : X) (f : X.functionField), (∀ y : Y, s y ⤳ x → D.RegularAt y (functionFieldMap s f)) → RegAt x f) → Nonempty ((Scheme.Modules.pushforward s).obj (twist (GlobalTheory.structureModule Y) (toLB D)) ≅ idealModule J) := by
  first | exact @_root_.GlobalTheory.pushforward_twist_iso_idealModule | exact _root_.GlobalTheory.pushforward_twist_iso_idealModule | (intros; apply _root_.GlobalTheory.pushforward_twist_iso_idealModule <;> assumption)
