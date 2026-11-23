import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WordAppend

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical
open GlobalTheory.ArchDecay LineDeriv

namespace GlobalTheory.ArchDecay.SchAStab

variable (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem pureA_line (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ)
    (x : κ → AF F) (v : κ → mixedEmbedding.mixedSpace F) (t : ℝ) :
    pureA F f g (x + fun i => infAd F (t • v i)) = f (arch F x + t • v) * g (fun i => (x i).2) := by
  unfold pureA
  congr 2
  · funext i
    change InfiniteAdeleRing.ringEquiv_mixedSpace F
        ((x i).1 + (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (t • v i)) = evI F (x i) + t • v i
    rw [map_add, RingEquiv.apply_symm_apply]
    rfl
  · funext i
    exact add_zero (x i).2

theorem hasDerivAt_line (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ)
    (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (x : κ → AF F) (v : κ → mixedEmbedding.mixedSpace F) :
    HasDerivAt (fun t : ℝ => pureA F f g (x + fun i => infAd F (t • v i)))
      (fderiv ℝ f (arch F x) v * g (fun i => (x i).2)) 0 := by
  simp only [pureA_line]
  have h1 : HasDerivAt (fun t : ℝ => arch F x + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add (arch F x)
  have h2 : HasDerivAt (fun t : ℝ => f (arch F x + t • v)) (fderiv ℝ f (arch F x) v) 0 :=
    (f.differentiableAt (x := arch F x)).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) h1 (by simp)
  exact h2.mul_const _

theorem dD_pureA (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ)
    (v : κ → mixedEmbedding.mixedSpace F) : dD F v (pureA F f g) = pureA F (∂_{v} f : SchwartzMap _ ℂ) g := by
  funext x
  rw [dD, (hasDerivAt_line F f g x v).deriv]
  show _ = (∂_{v} f : SchwartzMap _ ℂ) (arch F x) * _
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]

def mulL (l : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ) (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) :
    SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ :=
  SchwartzMap.smulLeftCLM ℂ (⇑l) f

theorem mulL_apply (l : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ)
    (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) (y : κ → mixedEmbedding.mixedSpace F) :
    mulL F l f y = (l y : ℂ) * f y := by
  rw [mulL, SchwartzMap.smulLeftCLM_apply_apply l.hasTemperateGrowth, Complex.real_smul]

theorem mM_pureA (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ)
    (l : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ) : mM F l (pureA F f g) = pureA F (mulL F l f) g := by
  funext x
  simp only [mM, pureA, mulL_apply, mul_assoc]
  rfl

theorem mem_schA_mM (l : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ) {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) :
    mM F l Φ ∈ schA F κ := by
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    rw [mM_pureA]
    exact Submodule.subset_span ⟨mulL F l f, g, hg, rfl⟩
  | zero =>
    have : mM F l (0 : (κ → AF F) → ℂ) = 0 := by funext x; simp [mM]
    rw [this]; exact Submodule.zero_mem _
  | add Φ Ψ _ _ h1 h2 =>
    have : mM F l (Φ + Ψ) = mM F l Φ + mM F l Ψ := by funext x; simp [mM, mul_add]
    rw [this]; exact Submodule.add_mem _ h1 h2
  | smul a Φ _ h =>
    have : mM F l (a • Φ) = a • mM F l Φ := by funext x; simp [mM]; ring
    rw [this]; exact Submodule.smul_mem _ a h

theorem archimedeanDirectionalDerivative_mem_adelicSchwartz (v : κ → mixedEmbedding.mixedSpace F) {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) :
    (∀ x : κ → AF F, DifferentiableAt ℝ (fun t : ℝ => Φ (x + fun i => infAd F (t • v i))) 0) ∧
      dD F v Φ ∈ schA F κ := by
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    refine ⟨fun x => (hasDerivAt_line F f g x v).differentiableAt, ?_⟩
    rw [dD_pureA]
    exact Submodule.subset_span ⟨_, g, hg, rfl⟩
  | zero =>
    refine ⟨fun x => differentiableAt_const _, ?_⟩
    have : dD F v (0 : (κ → AF F) → ℂ) = 0 := by funext x; simp [dD]
    rw [this]; exact Submodule.zero_mem _
  | add Φ Ψ _ _ h1 h2 =>
    refine ⟨fun x => (h1.1 x).add (h2.1 x), ?_⟩
    have : dD F v (Φ + Ψ) = dD F v Φ + dD F v Ψ := by
      funext x
      simp only [dD, Pi.add_apply]
      exact deriv_add (h1.1 x) (h2.1 x)
    rw [this]; exact Submodule.add_mem _ h1.2 h2.2
  | smul a Φ _ h =>
    refine ⟨fun x => (h.1 x).const_mul a, ?_⟩
    have : dD F v (a • Φ) = a • dD F v Φ := by
      funext x
      simp only [dD, Pi.smul_apply, smul_eq_mul]
      exact deriv_const_mul a (h.1 x)
    rw [this]; exact Submodule.smul_mem _ a h.2

theorem app_mem_schA : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (o : Op F κ),
    ∀ f ∈ schA F κ, app F o f ∈ schA F κ := by
  intro F _ _ κ _ o f hf
  rcases o with v | l
  · exact (archimedeanDirectionalDerivative_mem_adelicSchwartz F v hf).2
  · exact mem_schA_mM F l hf

end GlobalTheory.ArchDecay.SchAStab

end
