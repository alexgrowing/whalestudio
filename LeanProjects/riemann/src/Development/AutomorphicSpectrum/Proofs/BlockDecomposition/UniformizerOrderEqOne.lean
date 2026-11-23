import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNormalised
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsAlgHomMulEquivDec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPowCharPowEqSelf
import Development.WeilBound.CoreStatements.EulerCharacteristicCounts.GcohCmp
import GroundTheory.ProfiniteCohomology.LocalClassFormation.CupSymbol
import GroundTheory.ProfiniteCohomology.GaloisCohomology.IsZeroGroupCohomologyQuotientToInvariantsGalAdd
import GroundTheory.ProfiniteCohomology.GaloisCohomology.Kummer
import GroundTheory.GlobalFields.LocalFieldAtPlace
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.TransportA
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdicCompletionValuationMapUniformiser
import GroundTheory.LocalFields.UnitsBasic
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
open GroundTheory.ProfCoh GroundTheory.LocalField ValuativeRel CategoryTheory

namespace GlobalTheory.CompanionTheory.Completion

theorem valuation_eq_exp_neg_one_of_mem_of_notMem (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (ϖ : 𝓞 F) (h1 : ϖ ∈ v.asIdeal) (h2 : ϖ ∉ v.asIdeal ^ 2) :
    v.valuation F (ϖ : F) = WithZero.exp (-1 : ℤ) := by
  have hval : v.valuation F (ϖ : F) = v.intValuation ϖ := v.valuation_of_algebraMap ϖ
  rw [hval]
  have hle : v.intValuation ϖ ≤ WithZero.exp (-((1 : ℕ) : ℤ)) :=
    (v.intValuation_le_pow_iff_mem ϖ 1).2 (by simpa using h1)
  have hnle : ¬ v.intValuation ϖ ≤ WithZero.exp (-((2 : ℕ) : ℤ)) :=
    fun h => h2 ((v.intValuation_le_pow_iff_mem ϖ 2).1 h)
  have hne : v.intValuation ϖ ≠ 0 := by
    intro h
    apply hnle
    rw [h]
    exact zero_le'
  rw [← WithZero.exp_log hne] at hle hnle ⊢
  rw [WithZero.exp_le_exp] at hle hnle
  congr 1
  push_cast at hle hnle
  omega

theorem ord_algebraMap_eq_one : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (ϖ : 𝓞 F), ϖ ∈ v.asIdeal → ϖ ∉ v.asIdeal ^ 2 → ord (algebraMap F (v.adicCompletion F) (ϖ : F)) = 1 := by
  intro F _ _ v ϖ h1 h2
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[v.adicCompletion F]
  have hv : Valued.v (π : v.adicCompletion F) = WithZero.exp (-1 : ℤ) :=
    GlobalTheory.adicCompletion_valuation_map_uniformiser F v (v.adicCompletion F) (RingEquiv.refl _)
      (fun a => by
        rw [GroundTheory.Global.mem_valuationInteger_iff]
        exact Iff.rfl) π hπ
  have hx : Valued.v (algebraMap F (v.adicCompletion F) (ϖ : F)) = WithZero.exp (-1 : ℤ) := by
    exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (ϖ : F)).trans
      (valuation_eq_exp_neg_one_of_mem_of_notMem F v ϖ h1 h2)
  have heq : valuation (v.adicCompletion F) (algebraMap F (v.adicCompletion F) (ϖ : F)) =
      valuation (v.adicCompletion F) (π : v.adicCompletion F) :=
    ((ValuativeRel.isEquiv (valuation (v.adicCompletion F)) Valued.v).val_eq).2 (hx.trans hv.symm)
  have hn := (normalizedValuation_eq_iff (K := v.adicCompletion F)).2 heq
  rw [← ord_uniformizer hπ]
  simp only [ord, hn]

end GlobalTheory.CompanionTheory.Completion
