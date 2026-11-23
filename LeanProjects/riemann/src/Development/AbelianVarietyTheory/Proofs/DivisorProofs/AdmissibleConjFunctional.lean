import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StarMemAdelicSchwartzSpaceNumberField

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.AdmConj

def conjCLM (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] :
    SchwartzMap V ℂ →SL[starRingEnd ℂ] SchwartzMap V ℂ :=
  SchwartzMap.mkCLM (σ := starRingEnd ℂ) (fun f x => star (f x))
    (fun f g x => by simp [star_add])
    (fun c f x => by simp [star_mul', smul_eq_mul])
    (fun f => (GlobalTheory.SchAConj.conjSchwartz f).smooth')
    (by
      rintro ⟨k, n⟩
      refine ⟨{(k, n)}, 1, zero_le_one, fun f x => ?_⟩
      have h := Complex.conjLIE.norm_iteratedFDeriv_comp_left (𝕜 := ℝ) (f : V → ℂ) x n
      have e : (fun x => star (f x)) = (Complex.conjLIE : ℂ → ℂ) ∘ (f : V → ℂ) := rfl
      rw [e, h]
      simpa using SchwartzMap.le_seminorm ℂ k n f x)

theorem conjCLM_apply {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (f : SchwartzMap V ℂ) (x : V) :
    conjCLM V f x = star (f x) := rfl

def conjForm {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (T : SchwartzMap V ℂ →L[ℂ] ℂ) :
    SchwartzMap V ℂ →L[ℂ] ℂ where
  toFun f := starRingEnd ℂ (T (conjCLM V f))
  map_add' f g := by simp
  map_smul' c f := by simp [smul_eq_mul]
  cont := Complex.continuous_conj.comp (T.continuous.comp (conjCLM V).continuous)

theorem conjForm_apply {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (T : SchwartzMap V ℂ →L[ℂ] ℂ)
    (f : SchwartzMap V ℂ) : conjForm T f = starRingEnd ℂ (T (conjCLM V f)) := rfl

end GlobalTheory.AdmConj

theorem GlobalTheory.AdmConj.conj_mem_adm : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ], ∀ l ∈ (adeleClass F).adm κ,
    ∀ l' : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ, (∀ Φ, l' Φ = starRingEnd ℂ (l (fun x => starRingEnd ℂ (Φ x)))) →
    l' ∈ (adeleClass F).adm κ := by
  intro F _ _ κ _ l hl l' hl' g hg
  classical
  have hg' : (fun y => star (g y)) ∈ SB (κ → FiniteAdeleRing (𝓞 F) F) :=
    ⟨hg.1.comp star, hg.2.comp_left (g := star) (star_zero ℂ)⟩
  obtain ⟨T₀, hT₀⟩ := hl _ hg'
  refine ⟨GlobalTheory.AdmConj.conjForm T₀, fun f => ?_⟩
  rw [hl', GlobalTheory.AdmConj.conjForm_apply, ← hT₀]
  congr 2
  funext x
  simp [pureA, GlobalTheory.AdmConj.conjCLM_apply, star_mul']
