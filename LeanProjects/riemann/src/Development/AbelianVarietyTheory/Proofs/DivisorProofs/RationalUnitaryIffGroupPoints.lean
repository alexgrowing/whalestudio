import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability

namespace GlobalTheory.RatCorr

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem inclR_injective : Function.Injective (inclR (F := F) (E := E) (AF F)) :=
  haveI : Nontrivial (AF F) := inferInstanceAs (Nontrivial (Ainf F × Af F))
  Algebra.TensorProduct.includeRight_injective (algebraMap F (AF F)).injective

theorem sigR_inclR (σ : E →ₐ[F] E) (x : E) : sigR (AF F) σ (inclR (AF F) x) = inclR (AF F) (σ x) := by
  simp [sigR, inclR]

theorem ratU_iff (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (d : ℕ) (J : Matrix (Fin d) (Fin d) E) (c : E) (hc : c ≠ 0)
    (g : UA σ J) : g ∈ ratU σ J ↔ toGAd hσ J hc g ∈ GlobalTheory.AdelicU.ratPts σ (c • J.map σ) := by
  have hg : (g.1 : GL (Fin d) (AE F E)) ∈ HR (AF F) σ (c • J.map σ) := (toGAd hσ J hc g).2
  change g.1 ∈ (Matrix.GeneralLinearGroup.map (n := Fin d) (inclR (F := F) (E := E) (AF F))).range ↔
    g.1 ∈ (Formalism.UG.UJ (σ : E →+* E) (c • J.map σ)).map (Formalism.UG.bc (inclR (AF F)))
  constructor
  · rintro ⟨g₀, hg₀⟩
    refine ⟨g₀, ?_, hg₀⟩
    have h1 : Formalism.UG.cT (sigR (AF F) σ) ((g.1 : GL (Fin d) (AE F E)) : Matrix (Fin d) (Fin d) (AE F E)) *
        JR (AF F) (c • J.map σ) * ((g.1 : GL (Fin d) (AE F E)) : Matrix (Fin d) (Fin d) (AE F E)) =
        JR (AF F) (c • J.map σ) := hg
    have hm : ((g.1 : GL (Fin d) (AE F E)) : Matrix (Fin d) (Fin d) (AE F E)) =
        (g₀ : Matrix (Fin d) (Fin d) E).map (inclR (AF F)) := by
      rw [← hg₀]; rfl
    rw [hm] at h1
    change Formalism.UG.cT (σ : E →+* E) (g₀ : Matrix (Fin d) (Fin d) E) * (c • J.map σ) * (g₀ : Matrix (Fin d) (Fin d) E) = c • J.map σ
    apply Matrix.map_injective (inclR_injective (F := F) (E := E))
    dsimp only
    have e1 : (Formalism.UG.cT (σ : E →+* E) (g₀ : Matrix (Fin d) (Fin d) E)).map (inclR (F := F) (AF F)) =
        Formalism.UG.cT (sigR (AF F) σ) ((g₀ : Matrix (Fin d) (Fin d) E).map (inclR (AF F))) := by
      ext i j
      simp [Formalism.UG.cT, sigR_inclR]
    have e2 : (c • J.map σ).map (inclR (F := F) (AF F)) = JR (AF F) (c • J.map σ) := rfl
    rw [Matrix.map_mul, Matrix.map_mul, e1, e2]
    exact h1
  · rintro ⟨g₀, -, hg₀⟩
    exact ⟨g₀, hg₀⟩

theorem ratU_iff_ratPts : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x) (d : ℕ) (J : Matrix (Fin d) (Fin d) E) (c : E) (hc : c ≠ 0),
      ∀ g : UA σ J, g ∈ ratU σ J ↔ toGAd hσ J hc g ∈ GlobalTheory.AdelicU.ratPts σ (c • J.map σ) :=
  fun _ _ _ _ _ _ _ σ hσ d J c hc g => ratU_iff σ hσ d J c hc g

end GlobalTheory.RatCorr
