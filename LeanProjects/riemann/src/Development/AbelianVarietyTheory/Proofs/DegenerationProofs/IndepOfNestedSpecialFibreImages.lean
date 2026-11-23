import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsClassicalLiftOfSmoothStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory.ZJ

theorem Core.indep_of_special_fibres : ∀ C : Core, C.HasTests → (∀ (p : ℕ) [Fact p.Prime] (y y' : Sp (OO p) ⟶ C.Z), C.Cl y → C.Cl y' → rPt p ≫ y = rPt p ≫ y' → ∃ (τ : C.Test y) (τ' : C.Test y'), ∀ c : Sp (kb p) ⟶ τ.H.left, c ≫ τ.H.hom = rPt p ≫ spMap τ.j → ∃ c' : Sp (kb p) ⟶ τ'.H.left, c' ≫ τ'.H.hom = rPt p ≫ spMap τ'.j ∧ c' ≫ τ'.f = c ≫ τ.f) → C.Indep := by
  intro C _ h p _ y y' hy hy' hr b hb
  obtain ⟨τ, τ', hτ⟩ := h p y y' hy hy' hr
  obtain ⟨c, hc, hcb⟩ := τ.lift b hb
  obtain ⟨c', hc', hcf⟩ := hτ (rPt p ≫ c) (by rw [Category.assoc, hc])
  have := τ'.smooth
  have : Smooth τ'.H.hom := SmoothOfRelativeDimension.smooth C.g τ'.H.hom
  obtain ⟨d, hd, hdr⟩ := GlobalTheory.T.exists_classical_lift_of_smooth' p _ _ τ'.H.hom (spMap τ'.j) c' hc'
  refine ⟨d ≫ τ'.f, ?_, ?_⟩
  · rw [Category.assoc, τ'.f_over, ← Category.assoc, hd, τ'.fac]
  · rw [← Category.assoc, hdr, hcf, Category.assoc, hcb]

end GlobalTheory.ZJ
