import Mathlib
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.UniversalSymLiftMulOdd
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.universal_symLift_mul_odd : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (N : ℕ), Odd N → ∀ (T : Over Xo.X) (a b : T ⟶ Xo.univ.t.G) (Ua Ub Uab : ThetaGrp Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) T) (e : Γ(T.left, ⊤)ˣ), SymLift Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (N ^ 2) a Ua → SymLift Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (N ^ 2) b Ub → SymLift Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (N ^ 2) (a * b) Uab → WeilIs Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) a b e → ∃ r : Γ(T.left, ⊤)ˣ, r ^ 2 = e ∧ r ^ (N ^ 2) = 1 ∧ ∀ s s₁ s₂ s₃ : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) T), IsActOf Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) Ub s s₁ → IsActOf Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) Ua s₁ s₂ → IsActOf Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) Uab s s₃ → ∀ j, s₂.f j = liftFun Xo.univ.t.G _ (r : Γ(T.left, ⊤)) * s₃.f j := by
  first | exact @GlobalTheory.moduli_univ_symLift_mul | exact GlobalTheory.moduli_univ_symLift_mul | (intros; apply GlobalTheory.moduli_univ_symLift_mul <;> assumption)
