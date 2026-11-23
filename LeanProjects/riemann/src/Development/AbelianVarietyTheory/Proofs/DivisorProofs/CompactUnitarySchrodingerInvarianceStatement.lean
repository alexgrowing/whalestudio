import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactUnitarySchrodingerInvariance
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemAdelicSchwartzSpaceOfLevelCompactSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FiniteAdeleVectorAnnihilatorsCompactOpenBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelativelyCompactStabilizer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedAdelicLatticeClosure

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_open_finite_coords_mem_uniformly_on_compact : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    {n d n₁ d₁ : ℕ} (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁) (M : Model σ X W) (M₁ : Model σ X₁ W₁)
    (ι : Matrix (Fin n) (Fin n₁) E) (ι' : Matrix (Fin d) (Fin d₁) E) (K : Set (UA σ X.J)), IsCompact K →
    ∀ N ∈ 𝓝 (0 : (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) × (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F)),
      ∃ U : AddSubgroup (Fin n₁ × Fin d₁ → FiniteAdeleRing (𝓞 F) F), IsOpen (U : Set (Fin n₁ × Fin d₁ → FiniteAdeleRing (𝓞 F) F)) ∧
        ∀ k ∈ K, ∀ η ∈ U, ∃ p ∈ N, M.co.e (mat k⁻¹ * (incM F ι * M₁.co.e.symm (0, fun i => pairA F 0 (η i)) * (incM F ι')ᵀ)) =
          (fun i => pairA F 0 (p.1 i), fun i => pairA F 0 (p.2 i)) := by
  first | exact @GlobalTheory.ConeUnif.coords_small_unif | exact GlobalTheory.ConeUnif.coords_small_unif | (intros; apply GlobalTheory.ConeUnif.coords_small_unif <;> assumption)
