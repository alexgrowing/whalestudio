import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmEndomorphismPlaceIntegral
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
theorem _root_.GlobalTheory.T.cm_endomorphism_place_integral : GlobalTheory.Published.AbelianDualCrystal → GlobalTheory.Published.AbelianDeRham →
  ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (O : Type) [CommRing O] (ofO : 𝓞 F → O) (l : ℕ) [Fact l.Prime]
    (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (k₀ : IntermediateField ℚ ℂ) (R₀ : Subring ℂ), Module.Finite ℤ O →
    FiniteDimensional ℚ k₀ → IsPlaceOver l lam k₀ R₀ → (∀ x ∈ R₀, x ∈ k₀) →
    ∀ (σ : R₀ →+* Qb), (∀ x, ((σ x : Qb) : ℂ) = x) →
    ∀ (G₀ : Over (Sp R₀)) [GrpObj G₀] (P₀ : Out.PolAV (Sp R₀)) (Ψ₀ : P₀.A ⟶ G₀),
      IsAbelianScheme G₀ → IsMonHom Ψ₀ → IsFinite Ψ₀.left → Flat Ψ₀.left → Surjective Ψ₀.left →
    ∀ (XQ : Obj F 𝔠 (Sp Qb)) (gQ : XQ.A.left ⟶ G₀.left) (cmQ : OAct O XQ.A), IsGrpPullback XQ.A G₀ (spMap σ) gQ →
      (∀ a, cmQ.act (ofO a) = XQ.rm.act a) →
      Eventually l lam fun R ↦ ∀ (ic : R₀ →+* R) (j : R →+* Qb), (∀ x, ((ic x : R) : ℂ) = x) → (∀ x, ((j x : Qb) : ℂ) = x) →
        ∃ (X₀ : Obj F 𝔠 (Sp R)) (pj : XQ.A.left ⟶ X₀.A.left) (g : X₀.A.left ⟶ G₀.left) (cm : OAct O X₀.A),
          XQ.IsPullBy X₀ (spMap j) pj ∧ IsGrpPullback X₀.A G₀ (spMap ic) g ∧ pj ≫ g = gQ ∧
          (∀ a, cm.act (ofO a) = X₀.rm.act a) ∧ ∀ a, (cmQ.act a).left ≫ pj = pj ≫ (cm.act a).left := by
  first | exact @GlobalTheory.PlaceModel.exists_obj_eventually | exact GlobalTheory.PlaceModel.exists_obj_eventually | (intros; apply GlobalTheory.PlaceModel.exists_obj_eventually <;> assumption)
