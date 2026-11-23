import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MetWeightIsCInfOfPotential
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PnPosOfGeneratesAt
open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CxPts GlobalTheory.Mean4O.CombForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.metWeight_isCInf_of_potential : ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F) (Y : Var F) (e : ℕ) (M : Man e) (I : ManIs M Y) (Δ : Y.Dv) (m : ∀ σ, C.Met Y σ Δ) (hm : ∀ σ y, PosAt (m σ) y) (Q : ∀ a, LocPot (M.X a)), (∀ a, IsPot (I.pt a) (m (I.ε a)) (Q a) ∧ IsPotential (M.A a) (Q a)) → ∀ σ, (metWeight Δ (m σ) (hm σ)).IsCInf := by
  first | exact @GlobalTheory.Adopt.metWeight_isCInf_of_potential | exact GlobalTheory.Adopt.metWeight_isCInf_of_potential | (intros; apply GlobalTheory.Adopt.metWeight_isCInf_of_potential <;> assumption)
