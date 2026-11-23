import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.UnitaryDescent.NTDescent
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnramifiedNonsplitExistsConjInvolutionUniformiseStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryDoubleCosetOfGLintDoubleCoset
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceUnitaryLocalPointsEquivGL
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG UpperTheory.V UpperTheory.V.Lit UpperTheory.V.Lit.Desc

def UpperTheory.V.Lit.NTDescentU : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E],
    (∀ w : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal) →
    ∀ (p : ℕ), p.Prime → ∀ S : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield E))), S.Finite →
      (∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 (maximalRealSubfield E)) ∈ S → IsSplitAt w) →
      (∀ w : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ w.asIdeal → w.under (𝓞 (maximalRealSubfield E)) ∈ S) →
    ∀ n : ℕ, 1 ≤ n → ∀ z : E, IsZeta n z →
      (∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 (maximalRealSubfield E)) ∉ S → ¬ IsSplitAt w → w.valuation E z = 1) →
    ∀ wt : HeightOneSpectrum (𝓞 (maximalRealSubfield E)) → HeightOneSpectrum (𝓞 E),
      (∀ v, (wt v).under (𝓞 (maximalRealSubfield E)) = v) →
    ∀ g : ∀ v, GL (Fin n) ((wt v).adicCompletion E), (∀ v, IsIota z (wt v) (g v)) →
    ∀ π : CuspSub E n, (CG.mk π).IsRegAlg → GlobalTheory.ContraPair.DualIsConj π →
      (∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 (maximalRealSubfield E)) ∉ S → ∃ B, (CG.mk π).HasSat w B) →
      ∃ σ : Submodule ℂ (UA E n → ℂ), IsAutRepU σ ∧ (∀ v, v ∉ S → FixedIota σ (wt v) (g v)) ∧
        (∀ w, IsSplitAt w → ∀ τ, π.IsLocComp w τ → IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ) ∧
        ∀ φ : E →+* ℂ, ∃ lam, HasWeightAt σ φ lam ∧ π.HasInfChar φ (infOfWeight lam)

theorem UpperTheory.V.Lit.NTDescent.unit (h : NTDescent) : NTDescentU :=
  fun E _ _ _ hE p hp S hS hsp hpS n hn z hz _ => h E hE p hp S hS hsp hpS n hn z hz
