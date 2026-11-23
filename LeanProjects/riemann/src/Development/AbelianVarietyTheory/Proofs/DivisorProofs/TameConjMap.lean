import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjMapApply

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DoublingEv

noncomputable section

open scoped Classical

namespace GlobalTheory.DoublingEv.ConjTame

def conjSch {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D] :
    SchwartzMap D ℂ →SL[starRingEnd ℂ] SchwartzMap D ℂ :=
  SchwartzMap.mkCLM (𝕜 := ℂ) (𝕜' := ℂ) (σ := starRingEnd ℂ) (fun f x => star (f x))
    (fun f g x => by simp [star_add])
    (fun a f x => by simp [smul_eq_mul, mul_comm])
    (fun f => Complex.conjCLE.contDiff.comp (f.smooth ⊤))
    (fun n => ⟨{n}, 1, zero_le_one, fun f x => by
      have h : (fun x => star (f x)) = (Complex.conjLIE : ℂ ≃ₗᵢ[ℝ] ℂ) ∘ f := rfl
      rw [h, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left, Finset.sup_singleton, one_mul]
      exact SchwartzMap.le_seminorm ℂ n.1 n.2 f x⟩)

theorem conjSch_apply {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D] (f : SchwartzMap D ℂ) (x : D) :
    conjSch f x = star (f x) := rfl

theorem star_mem_SB {X : Type} [TopologicalSpace X] {g : X → ℂ} (hg : g ∈ SB X) : star g ∈ SB X :=
  ⟨hg.1.comp star, hg.2.comp_left (g := star) (star_zero ℂ)⟩

variable {F : Type} [Field F] [NumberField F]

theorem star_pureA {κ : Type} [Fintype κ] (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ)
    (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) :
    star (pureA F (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) g) = pureA F (conjSch f : _ → ℂ) (star g) := by
  funext x
  simp [pureA, conjSch_apply, star_mul', Pi.star_apply]

end GlobalTheory.DoublingEv.ConjTame

open GlobalTheory.DoublingEv.ConjTame in

theorem GlobalTheory.DoublingEv.isTame_conjMap : ∀ (F : Type) [Field F] [NumberField F] (κ κ' : Type) [Fintype κ] [Fintype κ']
    (T : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)), IsTame F T → IsTame F (conjMap T) := by
  intro F _ _ κ κ' _ _ T hT g hg
  obtain ⟨ι, _, P, g', hg', hP⟩ := hT (star g) (star_mem_SB hg)
  let Q : ι → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ →L[ℂ] SchwartzMap (κ' → mixedEmbedding.mixedSpace F) ℂ :=
    fun j => (conjSch.comp (P j)).comp conjSch
  refine ⟨ι, inferInstance, Q, fun j => star (g' j), fun j => star_mem_SB (hg' j), fun f => ?_⟩
  have hs : star (pureA F (f : _ → ℂ) g) = pureA F (conjSch f : _ → ℂ) (star g) := by
    rw [star_pureA]
  rw [conjMap_apply, hs, hP, star_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [star_pureA]
  rfl

end
