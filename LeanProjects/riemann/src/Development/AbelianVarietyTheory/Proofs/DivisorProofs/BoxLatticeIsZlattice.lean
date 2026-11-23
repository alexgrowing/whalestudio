import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenScaledInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanTracePairingBilinearNondegenerate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiFinRat

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Classical
open GlobalTheory.BoxLattice GlobalTheory.EvAdm

noncomputable section

namespace GlobalTheory.BoxLattice

theorem span_mixedEmbedding_mul_int (F : Type) [Field F] [NumberField F] (a : F) (ha : a ≠ 0) :
    Submodule.span ℝ (Set.range fun b : 𝓞 F => mixedEmbedding F (a * (b : F))) = ⊤ := by
  have h0 : Submodule.span ℝ (Set.range fun b : 𝓞 F => mixedEmbedding F (b : F)) = ⊤ := by
    rw [eq_top_iff, ← (mixedEmbedding.latticeBasis F).span_eq]
    apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    refine ⟨RingOfIntegers.basis F i, ?_⟩
    simp [mixedEmbedding.latticeBasis_apply, integralBasis_apply]
  let f : mixedEmbedding.mixedSpace F →ₗ[ℝ] mixedEmbedding.mixedSpace F :=
    LinearMap.mulLeft ℝ (mixedEmbedding F a)
  have himg : (Set.range fun b : 𝓞 F => mixedEmbedding F (a * (b : F))) =
      f '' (Set.range fun b : 𝓞 F => mixedEmbedding F (b : F)) := by
    rw [← Set.range_comp]
    congr 1
    funext b
    simp [f, map_mul]
  have hsurj : Function.Surjective f := by
    intro y
    refine ⟨mixedEmbedding F a⁻¹ * y, ?_⟩
    simp only [f, LinearMap.mulLeft_apply, ← mul_assoc, ← map_mul, mul_inv_cancel₀ ha, map_one, one_mul]
  rw [himg, ← Submodule.map_span, h0, Submodule.map_top, LinearMap.range_eq_top.mpr hsurj]

theorem span_boxLat_eq_top (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (a : F) (ha : a ≠ 0) :
    Submodule.span ℝ (boxLat F κ a : Set (κ → mixedEmbedding.mixedSpace F)) = ⊤ := by
  rw [eq_top_iff]
  intro y _
  rw [← Finset.univ_sum_single y]
  refine Submodule.sum_mem _ fun i _ => ?_
  have hi : Submodule.map (LinearMap.single ℝ (fun _ : κ => mixedEmbedding.mixedSpace F) i)
      (Submodule.span ℝ (Set.range fun b : 𝓞 F => mixedEmbedding F (a * (b : F)))) ≤
      Submodule.span ℝ (boxLat F κ a : Set (κ → mixedEmbedding.mixedSpace F)) := by
    rw [Submodule.map_span]
    apply Submodule.span_mono
    rintro _ ⟨_, ⟨b, rfl⟩, rfl⟩
    refine ⟨Pi.single i b, funext fun j => ?_⟩
    by_cases hj : j = i
    · subst hj; simp [ratInf]
    · simp [ratInf, Pi.single_apply, hj]
  apply hi
  rw [span_mixedEmbedding_mul_int F a ha]
  exact ⟨y i, trivial, rfl⟩

theorem isZLattice_boxLat : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (a : F), a ≠ 0 →
    ∀ [DiscreteTopology (boxLat F κ a)], IsZLattice ℝ (boxLat F κ a) := by
  intro F _ _ κ _ a ha _
  exact ⟨span_boxLat_eq_top F κ a ha⟩

end GlobalTheory.BoxLattice
