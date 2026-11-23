import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadFnCInfAtOfSmooth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PnPosOfGeneratesAt
open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CxPts GlobalTheory.Mean4O.CombForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.readFn_cInfAt_of_smooth : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (e : ℕ) (M : Man e) (I : ManIs M Y) (f : M.Fun), M.Smooth f → ∀ σ y, CInfAt (readFn I f σ) y := by
  first | exact @GlobalTheory.Adopt.readFn_cInfAt_of_smooth | exact GlobalTheory.Adopt.readFn_cInfAt_of_smooth | (intros; apply GlobalTheory.Adopt.readFn_cInfAt_of_smooth <;> assumption)
