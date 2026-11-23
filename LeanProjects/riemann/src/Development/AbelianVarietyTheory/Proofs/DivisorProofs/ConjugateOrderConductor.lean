import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateOrderData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPlaceRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationFormsCommensurableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypePeriodIntegralFirst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypePeriodIntegralSecond
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypePeriodConjugateIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmAuxiliarySetReductionGood
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgeOrdVpBaseChangeOfNeBot
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsChernExistsUniqueAndIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypePeriodProductIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypePeriodIntegralThird
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.Div.ConjugateOrderConductor
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations

theorem conj_orderC_bot {E : Type} [Field E] [NumberField E] [IsCMField E] (a : orderC (⊥ : Ideal (OF E))) :
    IsCMField.complexConj E (a : E) = (a : E) := by
  have hle : orderC (⊥ : Ideal (OF E)) ≤ RingHom.eqLocus ((IsCMField.complexConj E : E ≃ₐ[maximalRealSubfield E] E) : E →+* E) (RingHom.id E) := by
    unfold orderC
    rw [Subring.closure_le]
    rintro x (⟨b, rfl⟩ | ⟨b, hb, rfl⟩)
    · show IsCMField.complexConj E (algebraMap (OF E) E b) = algebraMap (OF E) E b
      rw [IsScalarTower.algebraMap_apply (OF E) (maximalRealSubfield E) E]
      exact IsCMField.complexConj_apply_eq_self E _
    · rw [Ideal.map_bot, Ideal.mem_bot] at hb
      subst hb
      show IsCMField.complexConj E (algebraMap (𝓞 E) E 0) = algebraMap (𝓞 E) E 0
      simp
  exact hle a.2

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)) (R : Type) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (K : Type) [Field K] [Algebra R K] [IsFractionRing R K] (H : Type) [AddCommGroup H]
    [Module R H] (I : Type) (φ : I → E →+* K) (ρ : orderC c →+* Module.End R H) (Fil : Submodule R H)
    (B : LinearMap.BilinForm R H) (e f : I → H) (N : Module.End K (K ⊗[R] H)) (i : I),
    GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.IsCMLattice φ ρ Fil B → GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.IsGens φ ρ e f →
    GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.IsLower ρ (φ i) (e i) (f i) N → c ≠ ⊥ := by
  intro E _ _ _ c R _ _ _ K _ _ _ H _ _ I φ ρ Fil B e f N i hL hG hN hc
  subst hc
  obtain ⟨hfree, -, -, hline, -⟩ := hL
  have heq : eigK ρ (φ i) = eigK ρ (bar (φ i)) := by
    unfold eigK
    congr 1
    funext a
    congr 1
    show φ i (a : E) = φ i (IsCMField.complexConj E (a : E))
    rw [conj_orderC_bot]
  have he : inK (O := R) K H (e i) ∈ eigK ρ (bar (φ i)) := by
    rw [← heq]
    show e i ∈ eigLat ρ (φ i)
    rw [(hG i).1]; exact Submodule.mem_span_singleton_self _
  have h0 : inK (O := R) K H (f i) = 0 := by
    rw [← hN.1]
    exact hN.2 _ (GlobalTheory.LowerOps.bar_ne_self _) _ he
  have hf : f i = 0 := by
    by_contra hf
    exact GlobalTheory.Div.eigen_line_bilinear.inK_ne_zero hfree hf h0
  obtain ⟨g, hg0, hg⟩ := GlobalTheory.EigenLattice.exists_ne_mem ρ (bar (φ i)) (hline _)
  rw [(hG i).2, hf, Submodule.span_singleton_eq_bot.2 rfl, Submodule.mem_bot] at hg
  exact hg0 hg

end GlobalTheory.Div.ConjugateOrderConductor
