import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyTwoNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CofinitePlacesInertOrSplitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiUnramifiedAlmostAllPlacesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeAtPlaceIntegralAlmostAllStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterUnramifiedAlmostAllPlacesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacuumEigenvectorInertCompactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceVacuumEigenvalue
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPlaceVacuumEigenvalueStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.PairVac

theorem vac_fixed_cofinite : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ᶠ v in Filter.cofinite, ∀ g ∈ GlobalTheory.InertSph.KAt σ W v, Acts (evFin F v) (om (1, g)) (M.vac v) (M.vac v) := by
  intro hK F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP
  have hgood : ∀ᶠ v in Filter.cofinite, GoodPlace B M χX v := by
    filter_upwards [GlobalTheory.T.cofinite_places_inert_or_split F E σ B n d X W M χX χW om r s r' s' hP, eventually_two_not_mem F,
      GlobalTheory.T.psi_unramified_almost_all_places F E σ B n d X W M χX χW om r s r' s' hP, hP.good.std,
      GlobalTheory.T.lattice_at_place_integral_almost_all F E σ B n d X W M χX χW om r s r' s' hP, GlobalTheory.T.character_unramified_almost_all_places F E σ B n d X W M χX χW om r s r' s' hP]
      with v h1 h2 h3 h4 h5 h6
    exact ⟨h1, h2, h3, h4, h5, h6⟩
  filter_upwards [hgood] with v hv g hg
  obtain ⟨c, hc⟩ := GlobalTheory.T.vacuum_eigenvector_inert_compact hK F E σ B n d X W M χX χW om r s r' s' hP v hv g hg
  have h1 : c = 1 := by
    rcases hv.inertOrSplit with ⟨w, hw⟩ | ht
    · exact GlobalTheory.T.inert_place_vacuum_eigenvalue hK F E σ B n d X W M χX χW om r s r' s' hP v w hw hv g hg c hc
    · exact GlobalTheory.T.split_place_vacuum_eigenvalue hK F E σ B n d X W M χX χW om r s r' s' hP v ht.some hv g hg c hc
  rw [h1, one_smul] at hc
  exact hc

end GlobalTheory.PairVac
