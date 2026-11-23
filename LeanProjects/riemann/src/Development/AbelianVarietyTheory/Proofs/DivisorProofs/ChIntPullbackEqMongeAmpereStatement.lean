import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChIntPullbackEqMongeAmpere
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HessRelFnB
open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.Mean4 GlobalTheory.Mean4O
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chInt_pullback_eq_monge_ampere : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (e : ℕ) (M : Man e) (I : ManIs M Y) (ε : (𝓞 F →+* ℂ) → Fin (M.n + 1)) (π : ∀ σ, CxPts V.p σ → M.X (ε σ)), Y.dim = e → V.IsDown I ε π → ∀ (L : HermLB V.p) (P : M.Pot), (∀ a, ReciprocityTheory.AnForm.M.IsPotential (M.A a) (P a)) → HessRel ε π L P → ∀ f : M.Fun, M.Smooth f → ArInt.chInt L e (M.pull ε π f) = V.ν * M.int (fun _ => P) f := by
  first | exact @GlobalTheory.Mean4O.CoverInt.chInt_pull | exact GlobalTheory.Mean4O.CoverInt.chInt_pull | (intros; apply GlobalTheory.Mean4O.CoverInt.chInt_pull <;> assumption)
