import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HessianRelationLinearCombination
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HessRelFnB
open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.Mean4 GlobalTheory.Mean4O
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hessian_relation_linear_combination : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (e : ℕ) (M : Man e) (I : ManIs M Y) (ε : (𝓞 F →+* ℂ) → Fin (M.n + 1)) (π : ∀ σ, CxPts V.p σ → M.X (ε σ)), V.IsDown I ε π → ∀ (ι : Type) [Fintype ι] (L : ι → HermLB V.p) (P : ι → M.Pot) (n : ι → ℤ) (R : M.Pot), (∀ i a, ReciprocityTheory.AnForm.M.IsPotential (M.A a) (P i a)) → (∀ a, ReciprocityTheory.AnForm.M.IsPotential (M.A a) (R a)) → (∀ i, HessRel ε π (L i) (P i)) → (∀ a j, ∀ y ∈ ((M.A a).chart j).target, ∀ w, leviAt (M.A a) (R a) j y w = ∑ i, (n i : ℝ) * leviAt (M.A a) (P i a) j y w) → HessRel ε π (ArInt.comb L n) R := by
  first | exact @GlobalTheory.Mean4O.HessComb.hessRel_comb | exact GlobalTheory.Mean4O.HessComb.hessRel_comb | (intros; apply GlobalTheory.Mean4O.HessComb.hessRel_comb <;> assumption)
