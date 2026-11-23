import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WordAppend
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical
open GlobalTheory.ArchDecay

noncomputable section

namespace GlobalTheory.ArchDecay

variable (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]

theorem continuous_mixedSymm : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm := by
  refine continuous_pi fun v => ?_
  rcases v.isReal_or_isComplex with hv | hv
  · rw [(InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_fst).congr fun y =>
      (congrFun (congrArg Prod.fst ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm
  · rw [(InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_snd).congr fun y =>
      (congrFun (congrArg Prod.snd ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm

theorem continuous_mixed : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
  change Continuous fun x : InfiniteAdeleRing F =>
    ((fun (v : {w : InfinitePlace F // w.IsReal}) => InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2 (x v)),
     (fun (v : {w : InfinitePlace F // w.IsComplex}) => InfinitePlace.Completion.extensionEmbedding v.1 (x v)))
  refine Continuous.prodMk (continuous_pi fun v => ?_) (continuous_pi fun v => ?_)
  · exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp (continuous_apply _)
  · exact (InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp (continuous_apply _)

theorem continuous_infAd : Continuous (infAd F) :=
  (continuous_mixedSymm F).prodMk continuous_const

theorem continuous_evI_arch : Continuous (evI F) := (continuous_mixed F).comp continuous_fst

@[simp] theorem evI_infAd (a : mixedEmbedding.mixedSpace F) : evI F (infAd F a) = a := by
  simp [evI, infAd]

theorem infAd_add (a b : mixedEmbedding.mixedSpace F) : infAd F (a + b) = infAd F a + infAd F b := by
  unfold infAd; rw [map_add, map_add]; rfl

theorem infAd_zero : infAd F 0 = 0 := by unfold infAd; rw [map_zero, map_zero]; rfl

theorem evI_add' (a b : AF F) : evI F (a + b) = evI F a + evI F b := by
  exact map_add ((InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp
    (RingHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))) a b

theorem evI_zero' : evI F 0 = 0 := by
  exact map_zero ((InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp
    (RingHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)))

abbrev dimA : ℕ := Module.finrank ℝ (κ → mixedEmbedding.mixedSpace F)

def ubasis : Module.Basis (Fin (dimA F κ)) ℝ (κ → mixedEmbedding.mixedSpace F) :=
  (Module.finBasis ℝ _).unitsSMul fun j =>
    Units.mk0 ‖Module.finBasis ℝ (κ → mixedEmbedding.mixedSpace F) j‖⁻¹
      (inv_ne_zero (norm_ne_zero_iff.2 ((Module.finBasis ℝ _).ne_zero j)))

theorem norm_ubasis (j : Fin (dimA F κ)) : ‖ubasis F κ j‖ = 1 := by
  have h := norm_ne_zero_iff.2 ((Module.finBasis ℝ (κ → mixedEmbedding.mixedSpace F)).ne_zero j)
  simp [ubasis, Module.Basis.unitsSMul_apply, norm_smul, h]

def archIn : (Fin (dimA F κ) → ℝ) →+ (κ → AF F) where
  toFun t := fun i => infAd F ((ubasis F κ).equivFun.symm t i)
  map_zero' := by funext i; rw [map_zero]; exact infAd_zero F
  map_add' s t := by funext i; rw [map_add]; exact infAd_add F _ _

def archOut : (κ → AF F) →+ (Fin (dimA F κ) → ℝ) where
  toFun x := (ubasis F κ).equivFun (arch F x)
  map_zero' := by
    have : arch F (0 : κ → AF F) = 0 := by funext i; exact evI_zero' F
    rw [this, map_zero]
  map_add' x y := by
    have : arch F (x + y) = arch F x + arch F y := by funext i; exact evI_add' F _ _
    rw [this, map_add]

theorem archIn_apply (t : Fin (dimA F κ) → ℝ) (i : κ) :
    archIn F κ t i = infAd F ((ubasis F κ).equivFun.symm t i) := rfl

theorem archOut_apply (x : κ → AF F) : archOut F κ x = (ubasis F κ).equivFun (arch F x) := rfl

@[simp] theorem archOut_archIn (t : Fin (dimA F κ) → ℝ) : archOut F κ (archIn F κ t) = t := by
  have : arch F (archIn F κ t) = (ubasis F κ).equivFun.symm t := by funext i; simp [arch, archIn_apply]
  rw [archOut_apply, this, LinearEquiv.apply_symm_apply]

theorem continuous_archIn : Continuous (archIn F κ) := by
  refine continuous_pi fun i => ?_
  show Continuous fun t => infAd F ((ubasis F κ).equivFun.symm t i)
  exact (continuous_infAd F).comp ((continuous_apply i).comp
    (LinearMap.continuous_of_finiteDimensional (ubasis F κ).equivFun.symm.toLinearMap))

theorem continuous_archOut : Continuous (archOut F κ) := by
  show Continuous fun x => (ubasis F κ).equivFun (arch F x)
  exact (LinearMap.continuous_of_finiteDimensional (ubasis F κ).equivFun.toLinearMap).comp
    (continuous_pi fun i => (continuous_evI_arch F).comp (continuous_apply i))

def perSet (m : ℕ) : Set (κ → AF F) :=
  {z | ∀ i, ∃ a : AF F, evI F a = 0 ∧ (∀ v, evFin F v a ∈ v.adicCompletionIntegers F) ∧ z i = (m : AF F) * a}

theorem per_iff (m : ℕ) (f : (κ → AF F) → ℂ) : Per F m f ↔ ∀ x, ∀ z ∈ perSet F κ m, f (x + z) = f x :=
  ⟨fun h x z hz => h x z hz, fun h x z hz => h x z hz⟩

def slab (m : ℕ) : Set (κ → AF F) := {w | w - archIn F κ (archOut F κ w) ∈ perSet F κ m}

def cube (N : ℕ) : Set (Fin N → ℝ) := Set.univ.pi fun _ => Set.Icc (0 : ℝ) 1

end GlobalTheory.ArchDecay
