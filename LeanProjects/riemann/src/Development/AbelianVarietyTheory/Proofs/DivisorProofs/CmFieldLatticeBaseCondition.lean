import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateOrderData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPlaceRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmFieldLatticeIntegralityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceRingModelPullbackStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)

set_option autoImplicit false
noncomputable section
attribute [local instance] Over.cartesianMonoidalCategory
open scoped Classical

namespace GlobalTheory.LatModel

theorem hasLatModel : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.SerreTateGoodReductionSt → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal →
  GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex.PolarisationModule →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (I : Type) [Fintype I] (d : ℕ)
    (φ : I → E →+* ℂ), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData d φ → ∀ (𝔣 : Ideal (OF E)) (Λ : PeriodPair), IsBaseCond 𝔣 → GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice d Λ →
    ∀ (l : ℕ) [Fact l.Prime] (Q : Finset (HeightOneSpectrum (OF E))), IsFinSetSplitPlacesCoprimeConductor 𝔣 Q → (∀ q ∈ Q, (l : OF E) ∉ q.asIdeal) →
    ∀ y : (Af E)ˣ, OneOver l y → ∀ (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (Ω : ℂ), Ω ^ 12 = latDisc Λ →
      GlobalTheory.LatModel.HasLatModel φ (condQ 𝔣 Q) y l lam (a0 𝔣 l) Ω := by
  intro h1 h2 h3 h4 h5 E _ _ _ _ I _ d φ hfd 𝔣 Λ h𝔣 hΛ l _ Q hQ hQl y hy lam Ω hΩ
  obtain ⟨𝔠, R, hR, X₀, X, U, p, cm, hp, hrm, hα, hb⟩ :=
    GlobalTheory.T.cm_field_lattice_integrality h1 h2 h3 h4 h5 E I d φ hfd 𝔣 Λ h𝔣 hΛ l Q hQ hQl y hy lam Ω hΩ
  have hcm : IsCMType φ := hfd.2.2.2.2.2.2.1
  refine ⟨𝔠, R, hR, X₀, X, U, p, cm, hp, hrm, hα, fun i ↦ ?_⟩
  obtain ⟨e, a, ha, hg, hgen⟩ := GlobalTheory.T.place_ring_model_pullback h3 E I φ hcm l lam 𝔠 R hR X₀ X _ U p hp i
  exact ⟨e, a, ha, hb i e a hg ha, hg, hgen⟩

end GlobalTheory.LatModel
