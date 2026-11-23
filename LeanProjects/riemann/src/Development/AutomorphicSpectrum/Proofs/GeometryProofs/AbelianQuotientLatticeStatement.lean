import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianQuotientLattice
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GermSys
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.QQuasiCompact
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_quotient_lattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X : Scheme.{0}) (t : SAB H X) (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] (x : Sp k ⟶ X) (Q : AbQuot t x) (d d' : ℕ) (g : GermAt t x d) (gB : GermAt Q.tB (𝟙 (Sp k)) d'), ∃ (Λ : Type) (_ : AddCommGroup Λ) (_ : Module (𝓞 E) Λ) (_ : Module.Free ℤ Λ) (_ : Module.Finite ℤ Λ) (P : Matrix (Fin d') (Fin d) k) (j : TensorProduct ℤ k Λ →ₗ[k] (Fin d → k)), Q.IsDiff g gB P ∧ Function.Surjective P.mulVec ∧ Function.Injective j ∧ (∀ u, P.mulVec u = 0 ↔ u ∈ LinearMap.range j) ∧ (∀ a, P * rho g.B a = rho gB.B a * P) ∧ ∀ a v, j (LinearMap.baseChange k ((LinearMap.lsmul (𝓞 E) Λ a).restrictScalars ℤ) v) = (rho g.B a).mulVec (j v) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LieSeq.lie_seq | exact GlobalTheory.CompanionTheory.Ar.LieSeq.lie_seq | (intros; apply GlobalTheory.CompanionTheory.Ar.LieSeq.lie_seq <;> assumption)
