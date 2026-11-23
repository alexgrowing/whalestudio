import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OfE
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EventuallyActMemLatVIff

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Base1 GroundTheory.Global GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
open scoped TensorProduct ENNReal NNReal Matrix Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.UnitLat

theorem eventually_cV_mul_mem_latV_iff : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (y : (AF F ⊗[F] E)ˣ), ∀ᶠ v in cofinite, ∀ Y : Fin 1 → Fin 1 → Fv F v ⊗[F] E, (fun a i => cV v (y : AF F ⊗[F] E) * Y a i) ∈ latV b v ↔ Y ∈ latV b v := by
  intro F E _ _ _ _ _ σ _ d b y
  have e1 := GlobalTheory.CompanionTheory.SW.MeasProj.eventually_mem_latV b
    (projFin (fun _ _ : Fin 1 => (y : AF F ⊗[F] E)))
  have e2 := GlobalTheory.CompanionTheory.SW.MeasProj.eventually_mem_latV b
    (projFin (fun _ _ : Fin 1 => ((y⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E)))
  filter_upwards [e1, e2, GlobalTheory.CompanionTheory.SW.LatFix.eventually_mul_closed b] with v h1 h2 h3 Y
  have c1 : ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr
      (cV v (y : AF F ⊗[F] E)) k ∈ v.adicCompletionIntegers F := fun k => h1 0 0 k
  have c2 : ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr
      (cV v ((y⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E)) k ∈ v.adicCompletionIntegers F :=
    fun k => h2 0 0 k
  have hone : cV v ((y⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) * cV v (y : AF F ⊗[F] E) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  constructor
  · intro hY a i k
    have h := h3 _ _ c2 (hY a i) k
    rwa [← mul_assoc, hone, one_mul] at h
  · intro hY a i k
    exact h3 _ _ c1 (hY a i) k

end GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.UnitLat

end
