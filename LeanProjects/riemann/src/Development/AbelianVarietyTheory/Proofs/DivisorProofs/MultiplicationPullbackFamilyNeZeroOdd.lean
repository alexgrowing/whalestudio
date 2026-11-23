import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.SeriesFrame
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulSecK
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.StalkMapInjectiveOfFlat
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MulAFiniteFlatSurjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.CanonicalLiftFrobenius
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem mulFam_exists_ne_zero : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (m : ℕ), Odd m → ∀ (F₁ : IntFam (maximalIdeal R) D.toPre 1) (G : IntFam (maximalIdeal R) D.toPre (m ^ 2)), MulFam m F₁ G → (∃ α j, (F₁.f α).f j ≠ 0) → ∃ α j, (G.f α).f j ≠ 0 := by
  intro R _ _ _ _ D m hm F₁ G hG ⟨α, j, hj⟩
  by_contra hcon
  push_neg at hcon
  apply hj
  obtain ⟨-, h₂, h₃⟩ := GlobalTheory.PairKernel.mulA_finite_flat_surjective _ D.toPre.P m hm.pos
  obtain ⟨u, -, -, e⟩ := hG.1 α
  refine GlobalTheory.PullLin.sec_eq_zero_of_flat D.toPre.P.isLB (F₁.f α) (mulA D.toPre.P.A m).left (fun x J hJ => ?_) j
  have e₁ := (secRel_iff D.toPre.P.isLB _ _ _ _ _ _ _ _ _ u).1 e _ (𝟙 _) x J hJ
  rw [ReciprocityTheory.ChartRestriction.G.H1.CanonicalLiftFrobenius.sval_zero _ (hcon _), Category.id_comp] at e₁
  exact (Units.mul_left_eq_zero _).1 e₁.symm

end GlobalTheory.Mum
