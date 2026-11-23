import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzSeminormSmulLeftLinearPhaseLe
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

noncomputable section

namespace GlobalTheory.ArchHeisPure

open scoped Classical Matrix

theorem exists_phase_translate {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (L : V →L[ℝ] ℝ) (c : ℝ) (a : V)
    (f : SchwartzMap V ℂ) : ∃ g : SchwartzMap V ℂ, ∀ x,
      g x = Complex.exp (-(2 * Real.pi * Complex.I) * ((L x + c : ℝ) : ℂ)) * f (x + a) := by
  refine ⟨SchwartzMap.smulLeftCLM ℂ (GlobalTheory.LinPhaseSeminorm.phaseLine c 1 ∘ ⇑L) (SchwartzMap.compSubConstCLM ℂ (-a) f),
    fun x => ?_⟩
  rw [SchwartzMap.smulLeftCLM_apply_apply (GlobalTheory.LinPhaseSeminorm.hasTemperateGrowth_phase L c 1),
    ← GlobalTheory.LinPhaseSeminorm.phase_eq]
  simp

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

variable (F) in

def evHom : AF F →+* mixedEmbedding.mixedSpace F :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp (RingHom.fst _ _)

def trForm (c : κ → mixedEmbedding.mixedSpace F) : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y => Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (y ⬝ᵥ c)
      map_add' := fun y y' => by rw [add_dotProduct, map_add]
      map_smul' := fun r y => by rw [smul_dotProduct, map_smul]; rfl }

theorem evHom_apply (a : AF F) : evHom F a = evI F a := rfl

theorem trForm_apply (c y : κ → mixedEmbedding.mixedSpace F) :
    trForm c y = Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (y ⬝ᵥ c) := rfl

theorem schr_pureA [Invertible (2 : AF F)] {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) {w : (κ → AF F) × (κ → AF F)}
    (hw : At (evI F) w) (f : SInf F κ) :
    ∃ f₁ : SInf F κ, ∀ h : (κ → Af F) → ℂ, schr ψ w (pureA F f h) = pureA F f₁ h := by
  obtain ⟨p, q⟩ := w
  obtain ⟨g, hg⟩ := exists_phase_translate (trForm fun i => evI F (q i))
    (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (⅟(2 : AF F) * (p ⬝ᵥ q)))) (fun i => evI F (p i)) f
  refine ⟨g, fun h => funext fun x => ?_⟩
  have hfin : (fun i => ((x + p) i).2) = fun i => (x i).2 := by
    funext i
    have h0 : evI F ((0, 1) : AF F) = 0 := map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
    have h1 : (1 : Af F) * (p i).2 = 0 := congrArg (fun z : (κ → AF F) × (κ → AF F) => (z.1 i).2) (hw _ h0)
    change (x i).2 + (p i).2 = _
    rw [one_mul] at h1
    rw [h1, add_zero]
  have harch : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F ((x + p) i).1) =
      (fun i => evI F (x i)) + fun i => evI F (p i) := by
    funext i
    exact map_add (evHom F) (x i) (p i)
  have hAt : At (evI F) (x ⬝ᵥ q + ⅟(2 : AF F) * (p ⬝ᵥ q)) := by
    intro v hv
    have hq : v • q = 0 := congrArg Prod.snd (hw v hv)
    rw [smul_add, ← dotProduct_smul, smul_eq_mul, mul_left_comm, ← smul_eq_mul v, ← dotProduct_smul, hq]
    simp
  have htr : Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (x ⬝ᵥ q + ⅟(2 : AF F) * (p ⬝ᵥ q))) =
      trForm (fun i => evI F (q i)) (fun i => evI F (x i)) +
        Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (⅟(2 : AF F) * (p ⬝ᵥ q))) := by
    rw [← evHom_apply, map_add, map_add, RingHom.map_dotProduct, trForm_apply]
    rfl
  simp only [schr, pureA]
  rw [hψ.2.2 _ hAt, htr, hfin, harch, ← mul_assoc, ← hg]
  rfl

theorem rho_pureA : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (α β κ : Type) [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (ψ : AddChar (AF F) ℂ)
    (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E)) (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ),
    IsStd ψ → ∀ u : Matrix α β (AE F E), At (evI F) u → ∀ f : SInf F κ,
      ∃ f₁ : SInf F κ, ∀ h : (κ → Af F) → ℂ, d.rho ψ u (pureA F f h) = pureA F f₁ h := by
  intro F E _ _ _ _ _ σ α β κ _ _ _ _ _ ψ JA JB d hψ u hu f
  refine schr_pureA hψ (fun r hr => ?_) f
  rw [← map_smul, hu r hr, map_zero]

end GlobalTheory.ArchHeisPure

end
