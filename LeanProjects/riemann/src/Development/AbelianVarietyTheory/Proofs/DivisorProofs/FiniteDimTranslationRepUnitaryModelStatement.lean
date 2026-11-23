import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimTranslationRepUnitaryModel
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFundamentalDomainMulRight
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.AdelicIsomorphismStatement
import Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.UnitaryPointsRankZeroSubsingleton
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BridgeSIsBridge
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability GlobalTheory.ThetaCplV
open Matrix
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_dim_translation_rep_unitary_model : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K : Type) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] (j : K →* G), Continuous j → ∀ H : Subgroup G, (∀ k, j k ∈ H) → ∀ T : Submodule ℂ (G → ℂ), FiniteDimensional ℂ T → (∀ t ∈ T, Continuous t) → (∀ h, ∀ t ∈ T, GlobalTheory.ThetaCplV.rt H h t ∈ T) → ∃ (m : ℕ) (τ : K → (EuclideanSpace ℂ (Fin m) →L[ℂ] EuclideanSpace ℂ (Fin m))), GlobalTheory.Dec.IsURep τ ∧ ∀ f ∈ GlobalTheory.ThetaCplV.typeSet (GlobalTheory.ThetaCplV.rt H) ⊤ T, ∃ L : EuclideanSpace ℂ (Fin m) →ₗ[ℂ] (G → ℂ), (∀ k w x, L (τ k w) x = L w (x * j k)) ∧ f ∈ LinearMap.range L := by
  first | exact @GlobalTheory.ThetaCplV.exists_isURep_of_stable | exact GlobalTheory.ThetaCplV.exists_isURep_of_stable | (intros; apply GlobalTheory.ThetaCplV.exists_isURep_of_stable <;> assumption)
