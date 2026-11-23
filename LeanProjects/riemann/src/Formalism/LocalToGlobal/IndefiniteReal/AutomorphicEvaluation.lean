import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowDict

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory Matrix IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.IndefR.Mult
open scoped TensorProduct ContDiff InnerProductSpace

namespace Formalism.IndefR.AutomorphicEvaluation

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

def ev (M : DSModel V S) (v₀ : M.Vec) : MMap M →ₗ[ℂ] (GA D V → ℂ) where
  toFun T := T v₀
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem ev_apply (M : DSModel V S) (v₀ : M.Vec) (T : MMap M) : ev M v₀ T = T v₀ := rfl

def IsLowVec (M : DSModel V S) (v₀ : M.Vec) : Prop :=
  ∀ τ, IsLowUnit (M.ε τ) (M.lam τ) (M.σ τ) (v₀ τ : M.H τ)

theorem ev_pair (M : DSModel V S) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (T T' : MMap M) {c : ℂ}
    (h : IsMultIP M μ 𝓕 T T' c) (v₀ v₀' : M.Vec) :
    ∫ g in 𝓕, star (ev M v₀ T g) * ev M v₀' T' g ∂μ = c * ∏ τ, ⟪(v₀ τ : M.H τ), (v₀' τ : M.H τ)⟫_ℂ :=
  (h v₀ v₀').2

theorem ev_norm (M : DSModel V S) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (T : MMap M) {c : ℂ}
    (h : IsMultIP M μ 𝓕 T T c) (v₀ : M.Vec) (hv : ∀ τ, ‖(v₀ τ : M.H τ)‖ = 1) :
    ∫ g in 𝓕, ((‖ev M v₀ T g‖ ^ 2 : ℝ) : ℂ) ∂μ = c := by
  have h1 := ev_pair M μ 𝓕 T T h v₀ v₀
  have h2 : ∏ τ, ⟪(v₀ τ : M.H τ), (v₀ τ : M.H τ)⟫_ℂ = 1 := by
    refine Finset.prod_eq_one fun τ _ => ?_
    rw [inner_self_eq_norm_sq_to_K, hv τ]
    norm_num
  rw [h2, mul_one] at h1
  rw [← h1]
  congr 1
  funext g
  rw [Complex.star_def, Complex.conj_mul']
  norm_cast

def ResInj (M : DSModel V S) (C : Submodule ℂ (MMap M)) {TK : Type} [AddCommGroup TK] [Module ℂ TK]
    (emb : TK →ₗ[ℂ] ⨂[ℂ] τ, M.sm τ) : Prop :=
  ∀ T ∈ C, (PiTensorProduct.lift T) ∘ₗ emb = 0 → T = 0

def ResInjVec (M : DSModel V S) (C : Submodule ℂ (MMap M)) : Prop :=
  ∀ T ∈ C, ∀ v : M.Vec, (∀ τ, (v τ : M.H τ) ≠ 0) → T v = 0 → T = 0

theorem resInj_of_vec (M : DSModel V S) (C : Submodule ℂ (MMap M)) {TK : Type} [AddCommGroup TK] [Module ℂ TK]
    (emb : TK →ₗ[ℂ] ⨂[ℂ] τ, M.sm τ) (h : ResInjVec M C)
    (hv : ∃ v : M.Vec, (∀ τ, (v τ : M.H τ) ≠ 0) ∧ ∃ x, emb x = PiTensorProduct.tprod ℂ v) : ResInj M C emb := by
  intro T hT h0
  obtain ⟨v, hv0, x, hx⟩ := hv
  refine h T hT v hv0 ?_
  have h1 := LinearMap.congr_fun h0 x
  rw [LinearMap.comp_apply, hx, PiTensorProduct.lift.tprod, LinearMap.zero_apply] at h1
  exact h1

open Formalism.L2.SG.RowDict in

def EvalTie (M : DSModel (D.sp.Y 0) S) (μ : Measure (GA D (D.sp.Y 0))) (𝓕 : Set (GA D (D.sp.Y 0)))
    (E : Submodule ℂ (MMap M)) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (G : GoodOp X)
    (ι : GA D (D.sp.Y 0) ≃* X.B.I.GA) (c : ℝ) : Prop :=
  ∃ v₀ : M.Vec, (∀ τ, ‖(v₀ τ : M.H τ)‖ = 1) ∧ ∃ j : E ≃ₗ[ℂ] EEC X G, ∀ T : E,
    ((j T : EEC X G) : L2X X) =ᵐ[muX X] (fun x => ev M v₀ (T : MMap M) (ι.symm x)) ∧
      ‖((j T : EEC X G) : L2X X)‖ ^ 2 = c * (ipM M μ 𝓕 (T : MMap M) (T : MMap M)).re

end Formalism.IndefR.AutomorphicEvaluation

end
