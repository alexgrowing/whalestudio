import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLocalDataPrescribedPointsFlag
import Formalism.LocalToGlobal.ProjectiveLattices.HasDataCondition
import Formalism.LocalToGlobal.ProjectiveLattices.LatPAddRight
import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
import Formalism.LocalToGlobal.ProjectiveLattices.ParCanon
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.LocalToGlobal.ProjectiveLattices.DepLaws
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain IsLocalRing ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.MainNotions.DIV.Cons
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_localData_prescribed_points_flag : ∀ (D : D7) (Pt : ℕ → ℕ → Type) (fld : ∀ j p, Pt j p → ModuliIntegralCharts.CF p) (L : ∀ j p, Pt j p → LatB D.host.E), (∀ j p y, (∀ a b, (L j p y).beta a b = (L j p y).beta b a) ∧ (∀ a a' b, (L j p y).beta (a + a') b = (L j p y).beta a b + (L j p y).beta a' b) ∧ (∀ (x x' : 𝓞 D.host.E), (x' : D.host.E) = D.host.conj (x : D.host.E) → ∀ a b, (L j p y).beta (x • a) b = (L j p y).beta a (x' • b)) ∧ (∃ (ι : Type) (_ : Fintype ι) (b : Module.Basis ι ℤ (L j p y).Y), ∀ x : ι → ℝ, x ≠ 0 → 0 < ∑ i, ∑ k, x i * x k * (L j p y).beta (b i) (b k)) ∧ ∃ ρ : ℕ, Module.finrank ℤ (L j p y).Y = 2 * D.R.f * ρ ∧ ρ ≤ (D.R.sigW j).1 ∧ ρ + (D.R.sigW j).1 ≤ D.R.r) → ∃ (P : ModuliIntegralCharts.Prov D) (dat : ℕ → P.Dat), ∀ j, 1 ≤ j → j < D.R.m → (P.rk (dat j) = D.R.r ∧ P.jj (dat j) = (D.R.sigW j).1) ∧ ∀ p y, ∃ η : (P.loc (dat j) p).Pt (P.loc (dat j) p).YY, (P.loc (dat j) p).fld η = fld j p y ∧ ∃ e : (P.loc (dat j) p).Ylat η ≃ₗ[𝓞 D.host.E] (L j p y).Y, ∀ a b, (L j p y).beta (e a) (e b) = (P.loc (dat j) p).be η a b := by
  first | exact @GlobalTheory.exists_prov_prescribed_points | exact GlobalTheory.exists_prov_prescribed_points | (intros; apply GlobalTheory.exists_prov_prescribed_points <;> assumption)
