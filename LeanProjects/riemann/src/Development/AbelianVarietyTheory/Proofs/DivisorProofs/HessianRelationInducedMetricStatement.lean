import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HessianRelationInducedMetric
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HessRelFnB
open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.Mean4 GlobalTheory.Mean4O
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hessian_relation_induced_metric : ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F) (Y : Var F) (V : Cover Y) (e : ℕ) (M : Man e) (I : ManIs M Y) (ε : (𝓞 F →+* ℂ) → Fin (M.n + 1)) (π : ∀ σ, CxPts V.p σ → M.X (ε σ)), V.IsDown I ε π → ∀ (A : Adl C Y) (L : HermLB V.p) (k : ℕ) (Q : M.Pot), V.Induces A L k → (∀ a, IsPot (I.pt a) (A.m (I.ε a)) (Q a) ∧ ReciprocityTheory.AnForm.M.IsPotential (M.A a) (Q a)) → HessRel ε π L fun a => (Q a).rsmul k := by
  first | exact @GlobalTheory.Mean4O.HessInd.hessRel_of_induces | exact GlobalTheory.Mean4O.HessInd.hessRel_of_induces | (intros; apply GlobalTheory.Mean4O.HessInd.hessRel_of_induces <;> assumption)
