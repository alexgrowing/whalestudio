import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeVectorContentIdealExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContentIdealLocalValuationBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContentIdealLocalLatticeValuationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalNormOfValuationProfileStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealNormProductOverPlacesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinHeightSmulInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsEvEqProdNormZpow
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicCharacterFrequenciesAndConductorProduct
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLineReps
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)

open IsDedekindDomain
open scoped nonZeroDivisors

namespace GlobalTheory.LatHtFinPart

theorem finprod_normFin_eq_absNorm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), Submodule.IsLattice E L → ∀ u : Fin n → E, u ≠ 0 →
      ∃ I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E, I ≠ 0 ∧ (∀ c : E, c ∈ I ↔ c • u ∈ L) ∧
        ∏ᶠ v, (GlobalTheory.EisMidHt.normFin F L v (fun i => compFin F E v (GlobalTheory.EisMidHt.adVec F u i)) : ℝ) =
          (FractionalIdeal.absNorm I : ℝ) := by
  intro F E _ _ _ _ _ n L hL u hu
  obtain ⟨I, hI0, hI⟩ := GlobalTheory.T.lattice_vector_content_ideal_exists E n L hL u hu
  refine ⟨I, hI0, hI, ?_⟩
  have h : ∀ v : HeightOneSpectrum (𝓞 F),
      (GlobalTheory.EisMidHt.normFin F L v (fun i => compFin F E v (GlobalTheory.EisMidHt.adVec F u i)) : ℝ) =
        ∏ w ∈ Formalism.L2.Host.aboveF (L := E) F v, (Ideal.absNorm w.asIdeal : ℝ) ^ FractionalIdeal.count E w I := by
    intro v
    have e : (fun i => compFin F E v (GlobalTheory.EisMidHt.adVec F u i)) = fun i => (1 : Fv F v) ⊗ₜ[F] u i :=
      funext fun i => GlobalTheory.EisMidHtScale.compFin_adVec v u i
    rw [e]
    exact GlobalTheory.T.local_norm_of_valuation_profile F E n L v _ _ fun c =>
      ⟨GlobalTheory.T.content_ideal_local_lattice_valuation F E n L hL u hu I hI0 hI v c, GlobalTheory.T.content_ideal_local_valuation_bound F E n L hL u hu I hI0 hI v c⟩
  rw [finprod_congr h]
  exact GlobalTheory.T.ideal_norm_product_over_places F E I hI0

end GlobalTheory.LatHtFinPart
