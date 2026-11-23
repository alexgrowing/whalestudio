import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsUniquePartner
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SecCmp
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniformisationCompleteLocalNormalDomain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGen
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniqueExpansionSectionAdmissibleBase
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EgaHolds
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpandsAtSecIsMul
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.CstDvdOfCstMulEqZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem secIsMul_cancel : ∀ (R : Type) [CommRing R] [IsDomain R] (X : Scheme.{0}) (p : X ⟶ Spec (CommRingCat.of R)), Flat p → ∀ (L : LB X) (q : R), q ≠ 0 → ∀ s t t' : LB.Sec L, ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul p q s t → ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul p q s t' → t = t' := by
  intro R _ _ X p hp L q hq s t t' h h'
  haveI := hp
  have key : ∀ j, t.f j = t'.f j := by
    intro j
    refine fn_ext fun x hx => ?_
    have e1 := GlobalTheory.secIsMul_gs h (𝟙 X) x j hx
    have e2 := GlobalTheory.secIsMul_gs h' (𝟙 X) x j hx
    rw [Category.id_comp] at e1 e2
    have h0 : cst p x q * (gs (𝟙 X) x (L.U j) (t.f j) - gs (𝟙 X) x (L.U j) (t'.f j)) = 0 := by
      rw [mul_sub, ← e1, ← e2, sub_self]
    obtain ⟨u, hu⟩ := GlobalTheory.cst_dvd_of_cst_mul_eq_zero p x (a := q) (b := 0)
      (fun c hc => by
        rcases mul_eq_zero.1 hc with h1 | h1
        · exact absurd h1 hq
        · rw [h1]) h0
    have hz : cst p x (0 : R) = 0 := by
      rw [cst, map_zero, gs_eq _ _ ⊤ trivial, map_zero, map_zero]
    rw [hz, zero_mul, sub_eq_zero] at hu
    exact hu
  cases t; cases t'
  congr 1
  exact funext key

end GlobalTheory.Mum
