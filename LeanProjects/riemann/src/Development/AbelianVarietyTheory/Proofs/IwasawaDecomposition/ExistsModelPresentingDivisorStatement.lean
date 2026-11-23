import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsModelPresentingDivisor
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LineModel
import Development.AbelianVarietyTheory.Statements.HeightBoundStatement.HTBoundSt
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier
open Formalism.MainNotions.DIV.Cons (intO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_model_presenting_divisor : HTBoundSt → ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (fl : s.Flag), AdmEx S κ → ∀ (k : s.Comp) (w : Sym D.host.E →₀ ℤ), (∀ a ∈ w.support, {q | a.1 q = true}.Finite) → ∃ (M : GlobalTheory.TrueGeo.Model (fl.C k).Y) (L : LB M.X) (m : ℕ+) (r : (L.pull M.j).ι → (fl.C k).Y.Fnˣ), L.IsLB ∧ Presents ((m : ℕ) • divOf (fl.C k) (expo S.Dw w)) (L.pull M.j) r ∧ ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (e : Ext v) (y : AlgPt (fl.C k).Y) (yt : Sp e.O ⟶ M.X) (i : (L.pull M.j).ι), spMap e.O.subtype ≫ yt = y.1 ≫ M.j → ⊤ ≤ yt ⁻¹ᵁ L.U (i PUnit.unit) → ((m : ℕ) : ℝ) * lgOf (fl.C k) w v e y = Real.log (e.w (valAt y.1 (((eqn (divOf (fl.C k) (expo S.Dw w)) (below y.1))⁻¹ ^ (m : ℕ) * r i : (fl.C k).Y.Fnˣ) : (fl.C k).Y.Fn))) := by
  first | exact @GlobalTheory.LineNorm.exists_model_lgOf | exact GlobalTheory.LineNorm.exists_model_lgOf | (intros; apply GlobalTheory.LineNorm.exists_model_lgOf <;> assumption)
