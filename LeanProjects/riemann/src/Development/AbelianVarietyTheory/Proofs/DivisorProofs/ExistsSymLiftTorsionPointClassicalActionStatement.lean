import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymLiftTorsionPointClassicalAction
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
import Development.AbelianVarietyTheory.Definitions.Divisors.ToricPeriodBlockIsSymm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_symLift_torsionPoint_classical_action : ∀ (g : ℕ) (x : KeyIn ℂ) (hg : x.P.g = g) (u : HolUnif x.P.A x.P.L g) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (c : ℂ) (W : Fin g → Fin g → ℂ), NF x hg u τ a b c W → ∀ m : ℕ, Odd m → ∀ (M N : Fin g → ℤ) (pt : (baseOver (Sp ℂ)) ⟶ x.P.A), pt.left = (u.ex (((m : ℂ) ^ 2)⁻¹ • perV τ M N)).left → ∃ U : ThetaGrp x.P.A x.P.L ((m ^ 2 : ℕ) : ℤ) (baseOver (Sp ℂ)), SymLift x.P.A x.P.L ((m ^ 2 : ℕ) : ℤ) (m ^ 2) pt U ∧ ∀ s f, FnT u (m ^ 2) s f → ∃ t, IsActOf x.P.A x.P.L ((m ^ 2 : ℕ) : ℤ) U s t ∧ FnT u (m ^ 2) t fun z => trFac τ a b m M N z * f (z + ((m : ℂ) ^ 2)⁻¹ • perV τ M N) := by
  first | exact @GlobalTheory.MBLow.Cl.exists_symLift_act_classical | exact GlobalTheory.MBLow.Cl.exists_symLift_act_classical | (intros; apply GlobalTheory.MBLow.Cl.exists_symLift_act_classical <;> assumption)
