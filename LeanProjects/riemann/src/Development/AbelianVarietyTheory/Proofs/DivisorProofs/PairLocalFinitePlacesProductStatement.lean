import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairLocalFinitePlacesProduct
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pair_local_finite_places_product : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (l : List (Pl F)), l.Nodup → ∀ h : Pl F → UA σ W.J, (∀ v ∈ l, h v ∈ UAt σ W (evFin F v)) →
    ∀ (f : SInf F (Fin n × Fin d)) (φ φ₁ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ), (∀ v, φ v ∈ SB _) →
      (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
      (∀ v ∈ l, φ₁ v ∈ SB _ ∧ Acts (evFin F v) (om (1, h v)) (φ v) (φ₁ v)) → (∀ v, v ∉ l → φ₁ v = φ v) →
      om (1, (l.map h).prod) (pure f φ) = pure f φ₁ := by
  first | exact @GlobalTheory.ListProdFactor.om_listProd_pure | exact GlobalTheory.ListProdFactor.om_listProd_pure | (intros; apply GlobalTheory.ListProdFactor.om_listProd_pure <;> assumption)
