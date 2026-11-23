import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NormValFUnit

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
noncomputable section
namespace GlobalTheory.Ex.UnitNorm

theorem norms_of_arc_input : AllA fun {_} _ _ _ {_} {_} {_} {_} {_} {_} _ {O'} _ _ {_} a => ∀ (C : Type) [NormedField C] [IsUltrametricDist C] [Algebra (FractionRing O') C], CExt O' ⊥ C → ∀ A : Lift a C, A.ν.IntN → (∀ χ, ‖(A.N.ψ χ : C)‖ = 1) ∧ (∀ m, Odd m → ∀ (p : A.N.QT (m ^ 2)) χ, ‖A.N.txT m p χ‖ ≤ 1) ∧ ∀ u : Cˣ, ‖(u : C)‖ < 1 → ∃ q : QuadraticMap ℤ A.N.X ℝ, (A.N.twist A.be u).Int q ∧ ∀ y, q y = -Real.log ‖(u : C)‖ * (A.be.be y y / 2) := by
  intro E _ _ _ H D l Xo c W₀ Y O' _ _ _ b ϖ a _ C _ _ _ hC A ⟨S, hS, hν⟩
  obtain ⟨s, hs⟩ := exists_base hS hC.1
  have hθ := norm_θ hS hν hs
  have hσ := norm_σ hS hν hs
  have hth := norm_th hS hν hs
  have hψ := fun χ => norm_ψ hS hν hs χ (a.gen _)
  exact ⟨hψ, fun m hm p χ => norm_txT A.N hθ hσ hψ hth hm.pos.ne' p χ, twist_int A.N hθ hσ hψ hth A.be⟩

end GlobalTheory.Ex.UnitNorm
end
