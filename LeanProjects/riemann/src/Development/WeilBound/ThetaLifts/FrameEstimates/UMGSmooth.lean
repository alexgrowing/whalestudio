import Development.WeilBound.ThetaLifts.FrameEstimates.TowerRallisLemma
import Development.WeilBound.ThetaLifts.FrameEstimates.UMGSmoothA

noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def umgComp (τ : ∀ w : InfinitePlace F, EmbOver E w) {d : ℕ} (J : Matrix (Fin d) (Fin d) E) (w : InfinitePlace F) :
    UA σ J →* Matrix (Fin d) (Fin d) ℂ :=
  (piInf (τ w)).mapMatrix.toMonoidHom.comp ((Units.coeHom _).comp (Subgroup.subtype _))

theorem umg_continuousMul {d : ℕ} (J : Matrix (Fin d) (Fin d) E) : ContinuousMul (UA σ J) := by
  have : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have : IsTopologicalGroup (GL (Fin d) (AE F E)) := inferInstance
  exact (Subgroup.instIsTopologicalGroupSubtypeMem _).toContinuousMul

theorem umg_cj_mem {d : ℕ} {W : Spc F E d} {γ : Multiplicative ℝ →* UA σ W.J} (hγ : γ ∈ Lines σ W) (x : UA σ W.J) :
    UMGS.cj x γ ∈ Lines σ W := by
  have := umg_continuousMul (σ := σ) W.J
  refine ⟨((continuous_const.mul hγ.1).mul continuous_const).congr fun s => (UMGS.cj_apply x γ s).symm,
    fun t u hu => ?_⟩
  have h := hγ.2 t u hu
  have hm : ∀ a b : UA σ W.J, mat (a * b) = mat a * mat b := fun _ _ => rfl
  have h1 : mat x⁻¹ * mat x = 1 := by rw [← hm, inv_mul_cancel]; rfl
  have e : mat (UMGS.cj x γ t) - 1 = mat x⁻¹ * (mat (γ t) - 1) * mat x := by
    rw [UMGS.cj_apply, hm, hm, mul_sub, sub_mul, mul_one, h1]
  rw [e, ← Matrix.smul_mul, ← Matrix.mul_smul, h, Matrix.mul_zero, Matrix.zero_mul]

open scoped Matrix.Norms.Operator in
theorem umgSmooth_of (hL : LinDer) (hG : LineGen) : UMGSmooth := by
  intro F E _ _ _ _ _ σ hcm τ d W hW f hf k γ hγ g
  obtain ⟨r, β, c, hβ, hl⟩ := hL F E σ hcm τ d W hW
  obtain ⟨k₀, S, hfS, hS⟩ := hf
  have := umg_continuousMul (σ := σ) W.J
  have hGn : ∀ (δ : Multiplicative ℝ →* UA σ W.J) Y, UMGS.Gn (umgComp τ W.J) δ Y ↔ Gen τ W δ Y := fun δ Y =>
    forall₂_congr fun w t => by rw [Complex.coe_smul]; rfl
  refine contDiff_infty.2 fun n => ?_
  exact UMGS.contDiff_comp_pr (umgComp τ W.J) (Lines σ W) (fun _ h => h.1) (fun _ h x => umg_cj_mem h x)
    (fun δ h => (hG F E σ hcm τ d W hW δ h).imp fun Y hY => (hGn δ Y).2 hY.2) β c hβ
    (fun f f' h δ hδ Y hY => hl f f' h δ hδ Y ((hGn δ Y).1 hY)) S
    (fun f hf => ⟨(hS f hf).1, (hS f hf).2.2⟩) γ hγ g n f hfS

end PositivityTheory.ThKEst

end
