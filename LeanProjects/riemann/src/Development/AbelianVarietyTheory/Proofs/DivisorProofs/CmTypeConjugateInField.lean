import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateOrderData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPlaceRing
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct

namespace GlobalTheory.CMTypeThroughField

theorem comp_bar {E : Type} [Field E] [NumberField E] [IsCMField E] {K : Type} [Field K] (j : K →+* ℂ)
    (ψ : E →+* K) : j.comp (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar ψ) = ComplexEmbedding.conjugate (j.comp ψ) := by
  ext x
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar, RingHom.coe_comp, Function.comp_apply]
  exact IsCMField.complexEmbedding_complexConj E (j.comp ψ) x

theorem bar_bar {E : Type} [Field E] [NumberField E] [IsCMField E] {K : Type} [Field K]
    (ψ : E →+* K) : GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar ψ) = ψ := by
  ext x
  simp [GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar]

theorem isCMTypeIn_bar : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (K : Type) [Field K] (j : K →+* ℂ) (I : Type)
    (φ : I → E →+* ℂ) (φK : I → E →+* K), (∀ i, j.comp (φK i) = φ i) → IsCMType φ →
    GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.IsCMTypeIn (fun i ↦ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φK i)) := by
  intro E _ _ _ K _ j I φ φK hφ hcm σ
  have hinj : Function.Injective (fun ψ : E →+* K => j.comp ψ) := by
    intro a b h
    ext x
    exact j.injective (DFunLike.congr_fun h x)
  have key : ∀ i, (σ = GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φK i) ∨ σ = GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φK i))) ↔
      (j.comp σ = φ i ∨ j.comp σ = ComplexEmbedding.conjugate (φ i)) := by
    intro i
    rw [bar_bar, or_comm]
    constructor
    · rintro (h | h)
      · exact Or.inl (by rw [h, hφ])
      · exact Or.inr (by rw [h, comp_bar, hφ])
    · rintro (h | h)
      · exact Or.inl (hinj (by simp only; rw [h, hφ]))
      · exact Or.inr (hinj (by simp only; rw [h, comp_bar, hφ]))
  obtain ⟨i, hi, hu⟩ := hcm (j.comp σ)
  exact ⟨i, (key i).2 hi, fun i' hi' => hu i' ((key i').1 hi')⟩

end GlobalTheory.CMTypeThroughField
