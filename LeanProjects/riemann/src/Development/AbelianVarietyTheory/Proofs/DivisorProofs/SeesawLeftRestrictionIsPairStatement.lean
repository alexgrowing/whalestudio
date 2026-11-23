import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawLeftRestrictionIsPair
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

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_order_l_adic_endomorphism_integral : GlobalTheory.Published.AbelianDualCrystal → GlobalTheory.Published.AbelianDeRham →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ →
    ∀ (c : Ideal (OF E)) (y : (Af E)ˣ), c ≠ ⊥ → ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l])
    (𝔠 : FracId (FR E)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (U : Unif φ (lattice c y) 0 X),
    (∀ a : orderC c, ∃ (α : X.A ⟶ X.A) (_ : IsMonHom α), ∀ w, U.u.ex (fun j ↦ φ (U.e j) (a : E) * w j) = U.u.ex w ≫ α) →
    ∀ (k₀ : IntermediateField ℚ ℂ) (R₀ : Subring ℂ), FiniteDimensional ℚ k₀ → IsPlaceOver l lam k₀ R₀ →
    (∀ x ∈ R₀, x ∈ k₀) →
    ∀ (G₀ : Over (Sp R₀)) [GrpObj G₀] (p₀ : X.A.left ⟶ G₀.left) (P₀ : Out.PolAV (Sp R₀)) (Ψ₀ : P₀.A ⟶ G₀),
      IsAbelianScheme G₀ → IsGrpPullback X.A G₀ (spMap R₀.subtype) p₀ → IsMonHom Ψ₀ → IsFinite Ψ₀.left →
      Flat Ψ₀.left → Surjective Ψ₀.left →
      Eventually l lam fun R ↦ ∃ (X₀ : Obj (FR E) 𝔠 (Sp R)) (p : X.A.left ⟶ X₀.A.left) (cm : OAct (orderC c) X₀.A),
        X.IsPullBy X₀ (spMap R.subtype) p ∧
        (∀ a : OF E, cm.act (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ofF c a) = X₀.rm.act a) ∧
        (∀ (a : orderC c) (α : X.A ⟶ X.A), IsMonHom α →
          (∀ w, U.u.ex (fun j ↦ φ (U.e j) (a : E) * w j) = U.u.ex w ≫ α) → α.left ≫ p = p ≫ (cm.act a).left) ∧
        ∀ (v₀ : epsR R₀ ⟶ G₀) (v' : X.Lie), IsTangent v₀ →
          v'.hom.left ≫ p₀ = spMap (Chart.dualMapR R₀.subtype) ≫ v₀.left → ∃ v : X₀.Lie, Obj.LieCorr R.subtype p v v' := by
  first | exact @GlobalTheory.LatModel.exists_obj_of_isogenous_model | exact GlobalTheory.LatModel.exists_obj_of_isogenous_model | (intros; apply GlobalTheory.LatModel.exists_obj_of_isogenous_model <;> assumption)
