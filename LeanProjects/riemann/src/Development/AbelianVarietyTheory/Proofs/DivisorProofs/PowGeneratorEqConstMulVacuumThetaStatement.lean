import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowGeneratorEqConstMulVacuumTheta
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pow_generator_eq_const_mul_vacuum_theta : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → 1 ≤ r → l.A = 1 → ∀ (k : U.Comp) (n g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] (U.X k).Λ) (idx : Fin g ≃ (U.X k).Ψ × Fin r) (e : Fin g ≃ Lt1 Dw), Even n → IsSympl (U.X k) bas → IdxIs c σ (U.X k) idx e → ∀ v : TF n g, IsVac (U.X k) bas (H.w0 : E) (tens (stdL E n) (U.X k).Λ) v → ∃ C : ℂ, C ≠ 0 ∧ ∀ x : (U.X k).dom, IsUnitFr (U.X k) x.1 → (∃ ϑ, GenReads U k bas idx e x ϑ) ∧ ∀ ϑ, GenReads U k bas idx e x ϑ → IsTheta1 (U.X k) bas idx (H.w0 : E) x.1 (U.X k).Λ ϑ ∧ MeanOne (U.X k) bas idx x.1 (U.X k).Λ ϑ ∧ ∀ z : Fin n → Fin g → ℂ, ∏ b, ϑ (z b) = C * thA (U.X k) bas idx v x.1 z := by
  first | exact @GlobalTheory.AdTh.prod_gen_eq_const_mul_thA | exact GlobalTheory.AdTh.prod_gen_eq_const_mul_thA | (intros; apply GlobalTheory.AdTh.prod_gen_eq_const_mul_thA <;> assumption)
