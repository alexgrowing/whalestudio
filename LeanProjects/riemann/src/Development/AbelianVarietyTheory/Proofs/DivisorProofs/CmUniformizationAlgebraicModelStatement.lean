import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmUniformizationAlgebraicModel
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateOrderData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPlaceRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SzPeriodsOfTangent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullByCompAlt
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomLieEquivScalarTmul

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_uniformization_algebraic_model : GlobalTheory.Published.AbelianDualCrystal →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ) (c : Ideal (OF E))
    (L : Set E) (𝔠 : FracId (FR E)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (U : Unif φ L 0 X),
    (∀ a : orderC c, ∃ (α : X.A ⟶ X.A) (_ : IsMonHom α), ∀ w, U.u.ex (fun j ↦ φ (U.e j) (a : E) * w j) = U.u.ex w ≫ α) →
    ∀ (R₀ : Subring ℂ) (σ : R₀ →+* Qb), (∀ x, ((σ x : Qb) : ℂ) = x) →
    ∀ (G₀ : Over (Sp R₀)) [GrpObj G₀] (p₀ : X.A.left ⟶ G₀.left), IsAbelianScheme G₀ →
      IsGrpPullback X.A G₀ (spMap R₀.subtype) p₀ →
    ∃ (XQ : Obj (FR E) 𝔠 (Sp Qb)) (pQ : X.A.left ⟶ XQ.A.left) (gQ : XQ.A.left ⟶ G₀.left) (cmQ : OAct (orderC c) XQ.A),
      X.IsPullBy XQ (spMap (algebraMap Qb ℂ)) pQ ∧ IsGrpPullback XQ.A G₀ (spMap σ) gQ ∧ pQ ≫ gQ = p₀ ∧
      (∀ a : OF E, cmQ.act (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ofF c a) = XQ.rm.act a) ∧
      ∀ (a : orderC c) (α : X.A ⟶ X.A), IsMonHom α →
        (∀ w, U.u.ex (fun j ↦ φ (U.e j) (a : E) * w j) = U.u.ex w ≫ α) → α.left ≫ pQ = pQ ≫ (cmQ.act a).left := by
  first | exact @GlobalTheory.CMModel.exists_qbModel_of_subring | exact GlobalTheory.CMModel.exists_qbModel_of_subring | (intros; apply GlobalTheory.CMModel.exists_qbModel_of_subring <;> assumption)
