import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AvgFormApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegrableOfRapidDecay

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.CompInjInt

open GlobalTheory.DiagForm
open scoped Classical

attribute [local instance] GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele
  GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField
  GlobalTheory.DiagForm.measAf GlobalTheory.DiagForm.borelAf

variable {F : Type} [Field F] [NumberField F] {κ m : Type} [Fintype κ] [Fintype m]

theorem sum_eq_mulVec {R : Type} [CommRing R] (f : F →+* R) (M : Matrix κ m F) (v : m → R) :
    (fun i => ∑ j, v j * f (M i j)) = (M.map f) *ᵥ v := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, mul_comm]

theorem mulVec_map_leftInv {R : Type} [CommRing R] (f : F →+* R) {M : Matrix κ m F} {N : Matrix m κ F}
    [DecidableEq m] (hNM : N * M = 1) (v : m → R) : (N.map f) *ᵥ ((M.map f) *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, hNM, Matrix.map_one _ (map_zero f) (map_one f), Matrix.one_mulVec]

variable (F m) in

def coordE : (m → AF F) ≃ₜ+ (Vi F m × Vf F m) where
  toFun t := ((eI F m).symm (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (t i).1), fun i => (t i).2)
  invFun p := glue p
  left_inv t := by
    funext i
    refine Prod.ext ?_ rfl
    show (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (eI F m ((eI F m).symm _) i) = (t i).1
    rw [ContinuousLinearEquiv.apply_symm_apply]
    exact RingEquiv.symm_apply_apply _ _
  right_inv p := by
    refine Prod.ext ?_ rfl
    show (eI F m).symm (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F
      ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (eI F m p.1 i))) = p.1
    simp
  map_add' t t' := by
    refine Prod.ext ?_ rfl
    show (eI F m).symm (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F ((t i).1 + (t' i).1)) = _ + _
    simp only [map_add]
    rw [← map_add]
    rfl
  continuous_toFun := by
    refine Continuous.prodMk ((eI F m).symm.continuous.comp (continuous_pi fun i => ?_))
      (continuous_pi fun i => continuous_snd.comp (continuous_apply i))
    exact (GlobalTheory.Core.Rk.RapidInt.continuous_toMixed F).comp (continuous_fst.comp (continuous_apply i))
  continuous_invFun := by
    refine continuous_pi fun i => Continuous.prodMk ?_ ((continuous_apply i).comp continuous_snd)
    exact (GlobalTheory.Core.Rk.RapidInt.continuous_ofMixed F).comp
      ((continuous_apply i).comp ((eI F m).continuous.comp continuous_fst))

variable [DecidableEq m]

variable (F) in

def archM (M : Matrix κ m F) : (m → mixedEmbedding.mixedSpace F) →L[ℝ] (κ → mixedEmbedding.mixedSpace F) :=
  LinearMap.toContinuousLinearMap ((Matrix.mulVecLin (M.map (mixedEmbedding F))).restrictScalars ℝ)

theorem archM_apply (M : Matrix κ m F) (x : m → mixedEmbedding.mixedSpace F) :
    archM F M x = (M.map (mixedEmbedding F)) *ᵥ x := rfl

theorem norm_le_archM {M : Matrix κ m F} {N : Matrix m κ F} (hNM : N * M = 1) (x : m → mixedEmbedding.mixedSpace F) :
    ‖x‖ ≤ ‖archM F N‖ * ‖archM F M x‖ := by
  calc ‖x‖ = ‖archM F N (archM F M x)‖ := by rw [archM_apply, archM_apply, mulVec_map_leftInv _ hNM]
    _ ≤ _ := ContinuousLinearMap.le_opNorm _ _

theorem norm_le_archM_eI {M : Matrix κ m F} {N : Matrix m κ F} (hNM : N * M = 1) (u : Vi F m) :
    ‖u‖ ≤ ‖(eI F m).symm.toContinuousLinearMap‖ * ‖archM F N‖ * (1 + ‖archM F M (eI F m u)‖) ^ 1 := by
  calc ‖u‖ = ‖(eI F m).symm.toContinuousLinearMap (eI F m u)‖ := by simp
    _ ≤ ‖(eI F m).symm.toContinuousLinearMap‖ * ‖eI F m u‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖(eI F m).symm.toContinuousLinearMap‖ * (‖archM F N‖ * ‖archM F M (eI F m u)‖) := by
      gcongr; exact norm_le_archM hNM _
    _ ≤ _ := by
      rw [pow_one, mul_assoc]
      gcongr
      linarith

def compA {M : Matrix κ m F} {N : Matrix m κ F} (hNM : N * M = 1) :
    SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ →L[ℂ] SchwartzMap (Vi F m) ℂ :=
  SchwartzMap.compCLM ℂ ((archM F M).comp (eI F m).toContinuousLinearMap).hasTemperateGrowth
    ⟨1, ‖(eI F m).symm.toContinuousLinearMap‖ * ‖archM F N‖, fun u => norm_le_archM_eI hNM u⟩

theorem fst_sum (x : m → AF F) : (∑ j, x j).1 = ∑ j, (x j).1 :=
  map_sum (RingHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)) x Finset.univ

theorem snd_sum (x : m → AF F) : (∑ j, x j).2 = ∑ j, (x j).2 :=
  map_sum (RingHom.snd (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)) x Finset.univ

theorem ringEquiv_algebraMap (c : F) :
    InfiniteAdeleRing.ringEquiv_mixedSpace F (algebraMap F (InfiniteAdeleRing F) c) = mixedEmbedding F c := by
  rw [InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]

theorem pureA_glue (M : Matrix κ m F) (f : (κ → mixedEmbedding.mixedSpace F) → ℂ)
    (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (p : Vi F m × Vf F m) :
    pureA F f g (fun i => ∑ j, glue p j * algebraMap F (AF F) (M i j)) =
      f (archM F M (eI F m p.1)) * g ((M.map (algebraMap F (FiniteAdeleRing (𝓞 F) F))) *ᵥ p.2) := by
  unfold pureA
  congr 1
  · congr 1
    rw [archM_apply, ← sum_eq_mulVec]
    funext i
    rw [fst_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    show InfiniteAdeleRing.ringEquiv_mixedSpace F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (eI F m p.1 j) *
      algebraMap F (InfiniteAdeleRing F) (M i j)) = _
    rw [map_mul, RingEquiv.apply_symm_apply, ringEquiv_algebraMap]
  · congr 1
    rw [← sum_eq_mulVec]
    funext i
    rw [snd_sum]
    rfl

theorem integrable_fin {M : Matrix κ m F} {N : Matrix m κ F} (hNM : N * M = 1)
    {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ} (hg : g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F)) :
    Integrable (fun v : Vf F m => g ((M.map (algebraMap F (FiniteAdeleRing (𝓞 F) F))) *ᵥ v)) Measure.addHaar := by
  have hc : Continuous fun v : Vf F m => (M.map (algebraMap F (FiniteAdeleRing (𝓞 F) F))) *ᵥ v :=
    continuous_const.matrix_mulVec continuous_id
  have hr : Continuous fun w : κ → FiniteAdeleRing (𝓞 F) F => (N.map (algebraMap F (FiniteAdeleRing (𝓞 F) F))) *ᵥ w :=
    continuous_const.matrix_mulVec continuous_id
  refine (hg.1.continuous.comp hc).integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.intro (hg.2.isCompact.image hr) fun v hv => ?_
  by_contra h
  exact hv ⟨_, subset_tsupport _ h, mulVec_map_leftInv _ hNM v⟩

theorem integrable_pure {M : Matrix κ m F} {N : Matrix m κ F} (hNM : N * M = 1)
    (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ)
    {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ} (hg : g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F)) :
    Integrable (fun p : Vi F m × Vf F m => pureA F f g (fun i => ∑ j, glue p j * algebraMap F (AF F) (M i j)))
      (mu F m) := by
  have e : (fun p : Vi F m × Vf F m => pureA F f g (fun i => ∑ j, glue p j * algebraMap F (AF F) (M i j))) =
      fun p => compA hNM f p.1 * g ((M.map (algebraMap F (FiniteAdeleRing (𝓞 F) F))) *ᵥ p.2) :=
    funext fun p => pureA_glue M f g p
  rw [e]
  exact (compA hNM f).integrable.mul_prod (integrable_fin hNM hg)

theorem integrable_schA {M : Matrix κ m F} {N : Matrix m κ F} (hNM : N * M = 1)
    {φ : (κ → AF F) → ℂ} (hφ : φ ∈ schA F κ) :
    Integrable (fun p : Vi F m × Vf F m => φ (fun i => ∑ j, glue p j * algebraMap F (AF F) (M i j))) (mu F m) := by
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, g, hg, rfl⟩ := hx
    exact integrable_pure hNM f hg
  | zero => exact integrable_zero _ _ _
  | add x y _ _ hx hy => exact hx.add hy
  | smul c x _ hx => exact hx.smul c

theorem main : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (m : Type) [Fintype m]
    [DecidableEq m] (B : (m → F) →ₗ[F] (κ → F)), Function.Injective B →
    ∀ μ : @Measure (m → AF F) (borel _), GlobalTheory.SiegelAvg.IsHaarB μ →
    ∀ φ ∈ schA F κ, (letI : MeasurableSpace (m → AF F) := borel _;
      Integrable (fun t : m → AF F => φ (fun i => ∑ j, t j * algebraMap F (AF F) (B (Pi.single j 1) i))) μ) := by
  intro F _ _ κ _ m _ _ B hB μ hμ φ hφ
  letI : MeasurableSpace (m → AF F) := borel _
  haveI : BorelSpace (m → AF F) := ⟨rfl⟩
  haveI : μ.IsAddHaarMeasure := hμ
  obtain ⟨C, hC⟩ := LinearMap.exists_leftInverse_of_injective B (LinearMap.ker_eq_bot.2 hB)
  have hNM : LinearMap.toMatrix' C * LinearMap.toMatrix' B = 1 := by
    rw [← LinearMap.toMatrix'_comp, hC, LinearMap.toMatrix'_id]
  have hM : ∀ i j, B (Pi.single j 1) i = LinearMap.toMatrix' B i j := fun i j => (LinearMap.toMatrix'_apply B i j).symm
  simp only [hM]
  haveI : (mu F m).IsAddHaarMeasure := by unfold mu; infer_instance
  haveI : (μ.map (coordE F m)).IsAddHaarMeasure := (coordE F m).isAddHaarMeasure_map μ
  have hν : μ.map (coordE F m) = Measure.addHaarScalarFactor (μ.map (coordE F m)) (mu F m) • mu F m :=
    Measure.isAddLeftInvariant_eq_smul _ _
  have h2 : Integrable (fun p : Vi F m × Vf F m =>
      φ (fun i => ∑ j, glue p j * algebraMap F (AF F) (LinearMap.toMatrix' B i j))) (μ.map (coordE F m)) := by
    rw [hν]
    exact (integrable_schA hNM hφ).smul_measure_nnreal
  have h3 := (integrable_map_equiv (coordE F m).toHomeomorph.toMeasurableEquiv _).1 h2
  refine h3.congr (ae_of_all _ fun t => ?_)
  have et : glue (coordE F m t) = t := (coordE F m).symm_apply_apply t
  simp only [Function.comp_apply]
  show φ (fun i => ∑ j, glue (coordE F m t) j * _) = _
  rw [et]

end GlobalTheory.CompInjInt
