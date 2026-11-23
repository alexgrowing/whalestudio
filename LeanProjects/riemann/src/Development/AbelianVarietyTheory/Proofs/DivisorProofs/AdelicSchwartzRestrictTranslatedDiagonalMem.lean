import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
import GroundTheory.AutomorphicForms.GL2.GJMatrixAdelic
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct FourierTransform
open MeasureTheory GroundTheory.Automorphic.GJMatrix

noncomputable section
namespace GlobalTheory.DiagShift

open scoped Classical

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

attribute [local instance] GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele
  GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField

variable (F κ) in

def diagA : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] (κ ⊕ κ → mixedEmbedding.mixedSpace F) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => Sum.elim x x
      map_add' := fun x x' => by funext i; cases i <;> simp
      map_smul' := fun c x => by funext i; cases i <;> simp }

theorem diagA_apply (x : κ → mixedEmbedding.mixedSpace F) : diagA F κ x = Sum.elim x x := rfl

theorem norm_le_diagA (x : κ → mixedEmbedding.mixedSpace F) : ‖x‖ ≤ ‖diagA F κ x‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => by
    simpa [diagA_apply] using norm_le_pi_norm (diagA F κ x) (Sum.inl j)

variable (F κ) in

def restrA : SchwartzMap (κ ⊕ κ → mixedEmbedding.mixedSpace F) ℂ →L[ℂ] SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ :=
  SchwartzMap.compCLM ℂ (diagA F κ).hasTemperateGrowth
    ⟨1, 1, fun x => by
      have := norm_le_diagA x
      have h0 := norm_nonneg (diagA F κ x)
      rw [pow_one, one_mul]; linarith⟩

theorem restrA_apply (f : SchwartzMap (κ ⊕ κ → mixedEmbedding.mixedSpace F) ℂ) (x : κ → mixedEmbedding.mixedSpace F) :
    restrA F κ f x = f (Sum.elim x x) := rfl

theorem shift_mem_finite {g : (κ ⊕ κ → FiniteAdeleRing (𝓞 F) F) → ℂ}
    (hg : g ∈ SB (κ ⊕ κ → FiniteAdeleRing (𝓞 F) F)) (b : κ → FiniteAdeleRing (𝓞 F) F) :
    (fun y : κ → FiniteAdeleRing (𝓞 F) F => g (Sum.elim (y + b) y)) ∈ finiteSchwartzBruhatPi F := by
  have hd : Continuous fun y : κ → FiniteAdeleRing (𝓞 F) F =>
      (Sum.elim (y + b) y : κ ⊕ κ → FiniteAdeleRing (𝓞 F) F) :=
    continuous_pi fun i => by
      cases i with
      | inl j => exact (continuous_apply j).add continuous_const
      | inr j => exact continuous_apply j
  have hr : Continuous fun z : κ ⊕ κ → FiniteAdeleRing (𝓞 F) F => fun j => z (Sum.inr j) :=
    continuous_pi fun j => continuous_apply _
  refine ⟨hg.1.comp_continuous hd, ?_⟩
  refine HasCompactSupport.intro (hg.2.isCompact.image hr) fun y hy => ?_
  by_contra h
  exact hy ⟨Sum.elim (y + b) y, subset_tsupport _ h, rfl⟩

theorem shift_pureA_mem (f : SchwartzMap (κ ⊕ κ → mixedEmbedding.mixedSpace F) ℂ)
    {g : (κ ⊕ κ → FiniteAdeleRing (𝓞 F) F) → ℂ} (hg : g ∈ SB (κ ⊕ κ → FiniteAdeleRing (𝓞 F) F))
    (u : κ → AdeleRing (𝓞 F) F) :
    (fun t : κ → AdeleRing (𝓞 F) F => pureA F f g (Sum.elim (t + u) t)) ∈ schwartzBruhatPi F κ := by
  have key : (fun t : κ → AdeleRing (𝓞 F) F => pureA F f g (Sum.elim (t + u) t)) =
      schwartzBruhatTensorPi
        (restrA F κ (SchwartzMap.compSubConstCLM ℂ (-Sum.elim (infPartPi u) 0) f))
        (fun y : κ → FiniteAdeleRing (𝓞 F) F => g (Sum.elim (y + finPartPi u) y)) := by
    funext t
    simp only [schwartzBruhatTensorPi, restrA_apply, SchwartzMap.compSubConstCLM_apply, sub_neg_eq_add]
    unfold pureA
    congr 1
    · congr 1
      funext i
      cases i with
      | inl j => exact map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) (t j).1 (u j).1
      | inr j => exact (add_zero _).symm
    · congr 1
      funext i
      cases i <;> rfl
  rw [key]
  exact schwartzBruhatTensorPi_mem _ (shift_mem_finite hg _)

theorem shift_mem_schwartzBruhatPi (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (φ : (κ ⊕ κ → AF F) → ℂ) (hφ : φ ∈ schA F (κ ⊕ κ)) (u : κ → AF F) :
    (fun t : κ → AF F => φ (Sum.elim (t + u) t)) ∈ schwartzBruhatPi F κ := by
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, g, hg, rfl⟩ := hx
    exact shift_pureA_mem f hg u
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul c x _ hx => exact Submodule.smul_mem _ c hx

end GlobalTheory.DiagShift
