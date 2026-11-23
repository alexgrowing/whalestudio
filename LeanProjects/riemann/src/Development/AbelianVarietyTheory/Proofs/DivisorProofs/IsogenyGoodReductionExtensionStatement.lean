import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyGoodReductionExtension
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
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLinearOfIsMonHom

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isogeny_good_reduction_extension : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (k₁ : IntermediateField ℚ ℂ) (R₁ : Subring ℂ),
    FiniteDimensional ℚ k₁ → IsPlaceOver l lam k₁ R₁ → (∀ x ∈ R₁, x ∈ k₁) →
    ∀ (P : Out.PolAV (Sp R₁)) (A' : Over (Sp ℂ)) [GrpObj A'] (φ' : A'.left ⟶ P.A.left),
    IsGrpPullback A' P.A (spMap R₁.subtype) φ' →
    ∀ (B : Over (Sp ℂ)) [GrpObj B] (α : A' ⟶ B) (N : ℕ), IsAbelianScheme B → IsMonHom α → IsFinite α.left →
    Flat α.left → Surjective α.left → 1 ≤ N → (∀ (T : Over (Sp ℂ)) (x : T ⟶ A'), x ≫ α = 1 → x ^ N = 1) →
    ∃ (k₀ : IntermediateField ℚ ℂ) (R₀ : Subring ℂ), FiniteDimensional ℚ k₀ ∧ IsPlaceOver l lam k₀ R₀ ∧
      (∀ x ∈ R₀, x ∈ k₀) ∧
      ∃ (G₀ : Over (Sp R₀)) (_ : GrpObj G₀) (p₀ : B.left ⟶ G₀.left) (P₀ : Out.PolAV (Sp R₀)) (Ψ₀ : P₀.A ⟶ G₀),
        IsAbelianScheme G₀ ∧ IsGrpPullback B G₀ (spMap R₀.subtype) p₀ ∧ IsMonHom Ψ₀ ∧ IsFinite Ψ₀.left ∧
        Flat Ψ₀.left ∧ Surjective Ψ₀.left ∧
        ∀ (v : epsR R₁ ⟶ P.A) (v' : epsR ℂ ⟶ A'), IsTangent v →
          v'.left ≫ φ' = spMap (Chart.dualMapR R₁.subtype) ≫ v.left →
          ∃ v₀ : epsR R₀ ⟶ G₀, IsTangent v₀ ∧ (v' ≫ α).left ≫ p₀ = spMap (Chart.dualMapR R₀.subtype) ≫ v₀.left := by
  first | exact @GlobalTheory.QuotModel.exists_quotModel | exact GlobalTheory.QuotModel.exists_quotModel | (intros; apply GlobalTheory.QuotModel.exists_quotModel <;> assumption)
