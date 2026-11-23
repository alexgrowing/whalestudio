import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaTraceOrthogonality
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsTranslSum
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_orth_pull_isTranslSum_of_isThetaTrace : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (K : Type) [Field K] (x x' : Sp K ⟶ Xo.X) (f : Fib Xo x ⟶ Fib Xo x') (f' : Fib Xo x' ⟶ Fib Xo x) (p : ℕ) (s : LB.Sec (PPx x)) (s₀ s' : LB.Sec (PPx x')) (a : K), p.Prime → IsPair (p ^ 2) f f' → AllRat Xo x' (p ^ 3) → a ≠ 0 → (∀ i, s'.f i = scal x' a i * s₀.f i) → IsThetaTrace Xo.univ.t.G Xo.univ.t.PP (conj x x' f.left) p s s' → ∃ (b ζ : K) (m : ℕ), ζ ^ p = 1 ∧ a * b = (p : K) ^ m * ζ ∧ ∃ f₂ : Fib Xo x' ⟶ Fib Xo x, IsMonHom f₂ ∧ f ≫ f₂ = 𝟙 _ ^ (p ^ 3) ∧ ∃ t, IsPullOf (p ^ 2) f₂ b s t ∧ IsTranslSum (p ^ 2) s₀ t := by
  first | exact @GlobalTheory.TraceOrth.thetaTrace_orthogonality | exact GlobalTheory.TraceOrth.thetaTrace_orthogonality | (intros; apply GlobalTheory.TraceOrth.thetaTrace_orthogonality <;> assumption)
