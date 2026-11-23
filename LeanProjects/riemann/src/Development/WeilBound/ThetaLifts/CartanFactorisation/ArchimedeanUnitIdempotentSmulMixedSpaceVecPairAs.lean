import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegrableOfRapidDecay

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix ENNReal Classical

noncomputable section

namespace PositivityTheory.ThKF.W

section One

section Gen

variable {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {JA : Matrix α α E} {JB : Matrix β β E}

def actLin (p : GlobalTheory.WeilM.UG c JA × GlobalTheory.WeilM.UG c JB) : Matrix α β E ≃ₗ[R] Matrix α β E where
  toFun x := GlobalTheory.WeilM.actAB c p x
  invFun x := (((p.1⁻¹ : GlobalTheory.WeilM.UG c JA) : GL α E) : Matrix α α E) * x *
    (((p.2⁻¹ : GlobalTheory.WeilM.UG c JB) : GL β E) : Matrix β β E)ᵀ
  map_add' x y := by simp [GlobalTheory.WeilM.actAB, Matrix.mul_add, Matrix.add_mul]
  map_smul' r x := by simp [GlobalTheory.WeilM.actAB, Matrix.mul_smul, Matrix.smul_mul]
  left_inv x := by
    simp only [GlobalTheory.WeilM.actAB, Subgroup.coe_inv, ← Matrix.mul_assoc]
    rw [Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc, ← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one,
      Matrix.mul_one]
  right_inv x := by
    simp only [GlobalTheory.WeilM.actAB, Subgroup.coe_inv, ← Matrix.mul_assoc]
    rw [Units.mul_inv, Matrix.one_mul, Matrix.mul_assoc, ← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one,
      Matrix.mul_one]

theorem actLin_apply (p : GlobalTheory.WeilM.UG c JA × GlobalTheory.WeilM.UG c JB) (x : Matrix α β E) :
    actLin (R := R) c p x = GlobalTheory.WeilM.actAB c p x := rfl

end Gen

variable (F : Type) [Field F] [NumberField F]

def finE {κ : Type} (y : κ → FiniteAdeleRing (𝓞 F) F) : κ → AdeleRing (𝓞 F) F := fun i => (0, y i)

def finE2 {κ : Type} (m : (κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F)) :
    (κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F) := (finE F m.1, finE F m.2)

def infE {κ : Type} (z : κ → mixedEmbedding.mixedSpace F) : κ → AdeleRing (𝓞 F) F :=
  fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (z i), 0)

def mixedSpaceVecPairAsAdeles {κ : Type} (v : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) :
    (κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F) := (infE F v.1, infE F v.2)

def slice {κ : Type} (Φ : (κ → AdeleRing (𝓞 F) F) → ℂ) (y : κ → FiniteAdeleRing (𝓞 F) F) :
    (κ → mixedEmbedding.mixedSpace F) → ℂ :=
  fun z => Φ fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (z i), y i)

def schrInf (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) {κ : Type} [Fintype κ]
    (v : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F))
    (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) : (κ → mixedEmbedding.mixedSpace F) → ℂ :=
  fun z => ψ (infE F z ⬝ᵥ infE F v.2 + ⅟(2 : AdeleRing (𝓞 F) F) * (infE F v.1 ⬝ᵥ infE F v.2)) * f (z + v.1)

variable {F}

theorem dot_infE {κ : Type} [Fintype κ] (x : κ → AdeleRing (𝓞 F) F) (z : κ → mixedEmbedding.mixedSpace F) :
    x ⬝ᵥ infE F z = infE F (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1) ⬝ᵥ infE F z := by
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Prod.ext ?_ ?_
  · show (x i).1 * (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (z i) = (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1) * (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (z i)
    rw [RingEquiv.symm_apply_apply]
  · show (x i).2 * 0 = 0 * 0
    rw [mul_zero, mul_zero]

theorem pureA_schrInf (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) {κ : Type} [Fintype κ]
    (v : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F))
    (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) :
    GlobalTheory.WeilM.pureA F (schrInf F ψ v f) g = GlobalTheory.WeilM.schr ψ (mixedSpaceVecPairAsAdeles F v) (GlobalTheory.WeilM.pureA F f g) := by
  funext x
  simp only [GlobalTheory.WeilM.pureA, schrInf, GlobalTheory.WeilM.schr, mixedSpaceVecPairAsAdeles]
  rw [dot_infE x v.2, mul_assoc]
  have h1 : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1) + v.1 =
      fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F ((x + infE F v.1) i).1 := by
    funext i
    show InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1 + v.1 i =
      InfiniteAdeleRing.ringEquiv_mixedSpace F ((x i).1 + (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (v.1 i))
    rw [map_add, RingEquiv.apply_symm_apply]
  have h2 : (fun i => (x i).2) = fun i => ((x + infE F v.1) i).2 := by
    funext i
    show (x i).2 = (x i).2 + 0
    rw [add_zero]
  rw [h1, h2]

theorem pureA_add {κ : Type} (f f' : (κ → mixedEmbedding.mixedSpace F) → ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) :
    GlobalTheory.WeilM.pureA F (f + f') g = GlobalTheory.WeilM.pureA F f g + GlobalTheory.WeilM.pureA F f' g := by
  funext x
  exact add_mul _ _ _

theorem pureA_smul {κ : Type} (a : ℂ) (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) :
    GlobalTheory.WeilM.pureA F (a • f) g = a • GlobalTheory.WeilM.pureA F f g := by
  funext x
  exact mul_assoc _ _ _

theorem exists_schwartz_slice {κ : Type} [Fintype κ] (Φ : (κ → AdeleRing (𝓞 F) F) → ℂ)
    (hΦ : Φ ∈ GlobalTheory.WeilM.schA F κ) (y : κ → FiniteAdeleRing (𝓞 F) F) :
    ∃ s : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, ∀ z, s z = slice F Φ y z := by
  induction hΦ using Submodule.span_induction with
  | mem Ψ hΨ =>
    obtain ⟨f, g, -, rfl⟩ := hΨ
    refine ⟨g y • f, fun z => ?_⟩
    have hz : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (z i))) = z := funext fun i => RingEquiv.apply_symm_apply _ _
    rw [SchwartzMap.smul_apply, smul_eq_mul]
    show g y * f z = f (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (z i))) * g (fun i => y i)
    rw [hz, mul_comm]
  | zero => exact ⟨0, fun z => rfl⟩
  | add Ψ Ψ' _ _ hΨ hΨ' =>
    obtain ⟨s, hs⟩ := hΨ
    obtain ⟨s', hs'⟩ := hΨ'
    exact ⟨s + s', fun z => by rw [SchwartzMap.add_apply, hs z, hs' z]; rfl⟩
  | smul c Ψ _ hΨ =>
    obtain ⟨s, hs⟩ := hΨ
    exact ⟨c • s, fun z => by rw [SchwartzMap.smul_apply, hs z]; rfl⟩

end One

section Two

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

def infPart (w : κ → AdeleRing (𝓞 F) F) : κ → mixedEmbedding.mixedSpace F :=
  fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (w i).1

theorem infPart_infE (z : κ → mixedEmbedding.mixedSpace F) : infPart (infE F z) = z := by
  funext i
  exact RingEquiv.apply_symm_apply _ _

theorem infE_infPart (w : κ → AdeleRing (𝓞 F) F) (h : ∀ i, (w i).2 = 0) : infE F (infPart w) = w := by
  funext i
  refine Prod.ext ?_ ?_
  · exact RingEquiv.symm_apply_apply _ _
  · exact (h i).symm

def eInf : AdeleRing (𝓞 F) F := ((1 : InfiniteAdeleRing F), (0 : FiniteAdeleRing (𝓞 F) F))

theorem eInf_smul_snd (w : κ → AdeleRing (𝓞 F) F) (i : κ) : ((eInf (F := F) • w) i).2 = 0 := by
  show (0 : FiniteAdeleRing (𝓞 F) F) * (w i).2 = 0
  exact zero_mul _

theorem eInf_smul_infE (z : κ → mixedEmbedding.mixedSpace F) : eInf (F := F) • infE F z = infE F z := by
  funext i
  refine Prod.ext ?_ ?_
  · exact one_mul _
  · exact zero_mul _

theorem infE_add (z z' : κ → mixedEmbedding.mixedSpace F) : infE F (z + z') = infE F z + infE F z' := by
  funext i
  refine Prod.ext ?_ ?_
  · exact map_add _ _ _
  · exact (add_zero 0).symm

theorem infPart_add (w w' : κ → AdeleRing (𝓞 F) F) : infPart (w + w') = infPart w + infPart w' := by
  funext i
  exact map_add _ _ _

def rAd (t : ℝ) : AdeleRing (𝓞 F) F :=
  ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (t • (1 : mixedEmbedding.mixedSpace F)), 0)

theorem infE_smul (t : ℝ) (z : κ → mixedEmbedding.mixedSpace F) : infE F (t • z) = rAd (F := F) t • infE F z := by
  funext i
  refine Prod.ext ?_ ?_
  · show (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (t • z i) = (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (t • 1) * (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (z i)
    rw [← map_mul, smul_one_mul]
  · exact (mul_zero 0).symm

theorem infPart_smul (t : ℝ) (w : κ → AdeleRing (𝓞 F) F) : infPart (rAd (F := F) t • w) = t • infPart w := by
  funext i
  show InfiniteAdeleRing.ringEquiv_mixedSpace F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (t • 1) * (w i).1) = t • InfiniteAdeleRing.ringEquiv_mixedSpace F (w i).1
  rw [map_mul, RingEquiv.apply_symm_apply, smul_one_mul]

def infPart2 (w : (κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F)) :
    (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F) := (infPart w.1, infPart w.2)

theorem archimedeanPartAdeleTuplePair_mixedSpaceVecPairAsAdeles (v : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) :
    infPart2 (mixedSpaceVecPairAsAdeles F v) = v := by
  exact Prod.ext (infPart_infE _) (infPart_infE _)

theorem archimedeanUnitIdempotent_smul_mixedSpaceVecPairAsAdeles (v : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) :
    eInf (F := F) • mixedSpaceVecPairAsAdeles F v = mixedSpaceVecPairAsAdeles F v := by
  exact Prod.ext (eInf_smul_infE _) (eInf_smul_infE _)

theorem mixedSpaceVecPair_archimedeanPart_idempotent_smul (w : (κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F)) :
    mixedSpaceVecPairAsAdeles F (infPart2 (eInf (F := F) • w)) = eInf (F := F) • w := by
  exact Prod.ext (infE_infPart _ (eInf_smul_snd _)) (infE_infPart _ (eInf_smul_snd _))

theorem mixedSpaceVecPairAsAdeles_add (v v' : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) :
    mixedSpaceVecPairAsAdeles F (v + v') = mixedSpaceVecPairAsAdeles F v + mixedSpaceVecPairAsAdeles F v' := by
  exact Prod.ext (infE_add _ _) (infE_add _ _)

theorem mixedSpaceVecPairAsAdeles_real_smul (t : ℝ) (v : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) :
    mixedSpaceVecPairAsAdeles F (t • v) = rAd (F := F) t • mixedSpaceVecPairAsAdeles F v := by
  exact Prod.ext (infE_smul _ _) (infE_smul _ _)

theorem infPart2_add (w w' : (κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F)) :
    infPart2 (w + w') = infPart2 w + infPart2 w' := by
  exact Prod.ext (infPart_add _ _) (infPart_add _ _)

theorem infPart2_smul (t : ℝ) (w : (κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F)) :
    infPart2 (rAd (F := F) t • w) = t • infPart2 w := by
  exact Prod.ext (infPart_smul _ _) (infPart_smul _ _)

theorem exists_infLin (B : ((κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F)) ≃ₗ[AdeleRing (𝓞 F) F]
      ((κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F))) :
    ∃ L : ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) ≃ₗ[ℝ]
        ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)),
      ∀ v, B (mixedSpaceVecPairAsAdeles F v) = mixedSpaceVecPairAsAdeles F (L v) := by
  have key : ∀ (C : ((κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F)) ≃ₗ[AdeleRing (𝓞 F) F]
      ((κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F)))
      (v : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)),
      mixedSpaceVecPairAsAdeles F (infPart2 (C (mixedSpaceVecPairAsAdeles F v))) = C (mixedSpaceVecPairAsAdeles F v) := by
    intro C v
    have h := mixedSpaceVecPair_archimedeanPart_idempotent_smul (C (mixedSpaceVecPairAsAdeles F v))
    rw [← map_smul C eInf (mixedSpaceVecPairAsAdeles F v), archimedeanUnitIdempotent_smul_mixedSpaceVecPairAsAdeles] at h
    exact h
  refine ⟨{ toFun := fun v => infPart2 (B (mixedSpaceVecPairAsAdeles F v))
            invFun := fun v => infPart2 (B.symm (mixedSpaceVecPairAsAdeles F v))
            map_add' := fun v v' => by
              rw [mixedSpaceVecPairAsAdeles_add, map_add, infPart2_add]
            map_smul' := fun t v => by
              rw [mixedSpaceVecPairAsAdeles_real_smul, map_smul, infPart2_smul, RingHom.id_apply]
            left_inv := fun v => by
              show infPart2 (B.symm (mixedSpaceVecPairAsAdeles F (infPart2 (B (mixedSpaceVecPairAsAdeles F v))))) = v
              rw [key B v, LinearEquiv.symm_apply_apply, archimedeanPartAdeleTuplePair_mixedSpaceVecPairAsAdeles]
            right_inv := fun v => by
              show infPart2 (B (mixedSpaceVecPairAsAdeles F (infPart2 (B.symm (mixedSpaceVecPairAsAdeles F v))))) = v
              rw [key B.symm v, LinearEquiv.apply_symm_apply, archimedeanPartAdeleTuplePair_mixedSpaceVecPairAsAdeles] }, fun v => ?_⟩
  exact (key B v).symm

end Two

namespace HaarSplit

variable (F : Type) [Field F] [NumberField F] (κ : Type)

def splitE : ((κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F)) ≃+ (κ → AdeleRing (𝓞 F) F) where
  toFun p := fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (p.1 i), p.2 i)
  invFun x := (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1, fun i => (x i).2)
  left_inv p := Prod.ext (funext fun i => RingEquiv.apply_symm_apply _ _) (funext fun i => rfl)
  right_inv x := funext fun i => Prod.ext (RingEquiv.symm_apply_apply _ _) rfl
  map_add' p q := funext fun i => Prod.ext (map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (p.1 i) (q.1 i)) rfl

theorem continuous_splitE : Continuous (splitE F κ) := by
  have hs : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm := by
    refine continuous_pi fun v => ?_
    by_cases hv : v.IsReal
    · refine (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).isEmbedding.isInducing.continuous_iff.2 ?_
      have h : (InfinitePlace.Completion.extensionEmbeddingOfIsReal hv) ∘ (fun y => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm y) v) =
          fun y => y.1 ⟨v, hv⟩ := by
        funext y
        have h1 := congrArg (fun p : mixedEmbedding.mixedSpace F => p.1 ⟨v, hv⟩) ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)
        simpa only [InfiniteAdeleRing.ringEquiv_mixedSpace_apply, Function.comp_apply] using h1
      rw [h]
      exact (continuous_apply _).comp continuous_fst
    · have hc : v.IsComplex := InfinitePlace.not_isReal_iff_isComplex.mp hv
      refine (InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.isInducing.continuous_iff.2 ?_
      have h : (InfinitePlace.Completion.extensionEmbedding v) ∘ (fun y => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm y) v) =
          fun y => y.2 ⟨v, hc⟩ := by
        funext y
        have h1 := congrArg (fun p : mixedEmbedding.mixedSpace F => p.2 ⟨v, hc⟩) ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)
        simpa only [InfiniteAdeleRing.ringEquiv_mixedSpace_apply, Function.comp_apply] using h1
      rw [h]
      exact (continuous_apply _).comp continuous_snd
  show Continuous fun p : (κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F) =>
    fun i => (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (p.1 i), p.2 i) : AdeleRing (𝓞 F) F)
  exact continuous_pi fun i => (hs.comp ((continuous_apply i).comp continuous_fst)).prodMk
    ((continuous_apply i).comp continuous_snd)

theorem continuous_splitE_symm : Continuous (splitE F κ).symm := by
  have he : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
    rw [show ⇑(InfiniteAdeleRing.ringEquiv_mixedSpace F) = _ from funext (InfiniteAdeleRing.ringEquiv_mixedSpace_apply F)]
    exact (continuous_pi fun v => (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp
      (continuous_apply _)).prodMk (continuous_pi fun v =>
        (InfinitePlace.Completion.isometry_extensionEmbedding _).continuous.comp (continuous_apply _))
  show Continuous fun x : κ → AdeleRing (𝓞 F) F =>
    ((fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1, fun i => (x i).2) : (κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F))
  exact (continuous_pi fun i => he.comp (continuous_fst.comp (continuous_apply i))).prodMk
    (continuous_pi fun i => continuous_snd.comp (continuous_apply i))

theorem pureA_splitE (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ)
    (p : (κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F)) :
    GlobalTheory.WeilM.pureA F f g (splitE F κ p) = f p.1 * g p.2 := by
  show f (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (p.1 i))) * g (fun i => p.2 i) = f p.1 * g p.2
  simp only [RingEquiv.apply_symm_apply]

theorem volume_isAddHaar [Fintype κ] : (volume : Measure (κ → mixedEmbedding.mixedSpace F)).IsAddHaarMeasure := by
  haveI : MeasurableAdd (mixedEmbedding.mixedSpace F) := inferInstance
  haveI : (volume : Measure (mixedEmbedding.mixedSpace F)).IsAddHaarMeasure := inferInstance
  haveI : SigmaFinite (volume : Measure (mixedEmbedding.mixedSpace F)) := inferInstance
  exact MeasureTheory.Measure.pi.isAddHaarMeasure (fun _ => volume)

end HaarSplit

end PositivityTheory.ThKF.W

end
