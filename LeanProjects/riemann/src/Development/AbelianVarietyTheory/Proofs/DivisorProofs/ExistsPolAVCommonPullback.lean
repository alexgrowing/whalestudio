import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyUWit
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabRange
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRatPointOfFiniteType
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UPoinc

theorem exists_polAV_common_pullback : ∀ (Ω : Type) [Field Ω] (T T' : Scheme.{0}) (Q : PolAV T) (P' : PolAV T') (f : Sp Ω ⟶ T) (f' : Sp Ω ⟶ T') (G' : Over (Sp Ω)) [GrpObj G'] (a₁ : G'.left ⟶ Q.A.left) (a₂ : G'.left ⟶ P'.A.left), IsGrpPullback G' Q.A f a₁ → IsGrpPullback G' P'.A f' a₂ → LBIso (Q.L.pull a₁) (P'.L.pull a₂) → ∃ (P₀ : PolAV (Sp Ω)) (a : P₀.A.left ⟶ Q.A.left) (a' : P₀.A.left ⟶ P'.A.left) (e : G'.left ⟶ P₀.A.left), IsIso e ∧ e ≫ a = a₁ ∧ e ≫ a' = a₂ ∧ IsGrpPullback P₀.A Q.A f a ∧ IsGrpPullback P₀.A P'.A f' a' ∧ LBIso P₀.L (Q.L.pull a) ∧ LBIso P₀.L (P'.L.pull a') := by
  intro Ω _ T T' Q P' f f' G' _ a₁ a₂ h₁ h₂ hL
  obtain ⟨P₀, φ, hφ, hL₀⟩ := exists_pol_baseChange Q f
  obtain ⟨e, he, hea⟩ := grpPullback_iso h₁ hφ
  haveI := he
  have hinv : IsMonHom e.symm.hom := inferInstanceAs (IsMonHom e.inv)
  have hφ' : φ = e.inv.left ≫ a₁ := by
    rw [← hea, ← Category.assoc, ← Over.comp_left, e.inv_hom_id, Over.id_left, Category.id_comp]
  have hiso : IsIso e.hom.left := ⟨⟨e.inv.left, by rw [← Over.comp_left, e.hom_inv_id, Over.id_left],
    by rw [← Over.comp_left, e.inv_hom_id, Over.id_left]⟩⟩
  refine ⟨P₀, φ, e.inv.left ≫ a₂, e.hom.left, hiso, hea, ?_, hφ, ?_, hL₀, ?_⟩
  · rw [← Category.assoc, ← Over.comp_left, e.hom_inv_id, Over.id_left, Category.id_comp]
  · exact ((isGrpPullback_of_iso e.symm).comp h₂).congr (Category.id_comp _) rfl
  · exact LBIso.trans P₀.isLB (pull_isLB Q.isLB _) (pull_isLB P'.isLB _) hL₀
      (GenSpread.lbIso_pull_comp e.inv.left hφ' rfl hL)

end GlobalTheory.UPoinc
