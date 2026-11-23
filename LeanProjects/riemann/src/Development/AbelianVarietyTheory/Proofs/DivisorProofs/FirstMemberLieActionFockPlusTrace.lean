import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FramedDConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieFirstOfLieSecond
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HoweSplittingActsFockActionPlusTraceMultiplesStatement

open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

open NumberField MeasureTheory MvPolynomial Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.RealLift GlobalTheory.HoweD

namespace GlobalTheory.HoweD.LieFirstD

section Tensor

variable {ι : Type} [Fintype ι] [DecidableEq ι] {P Q R S : ι → ℕ}

def swapTD (P Q R S : ι → ℕ) :
    (⨂[ℂ] w : ι, Formalism.BasicNotions.TH.Pol (R w) (S w) (P w) (Q w)) ≃ₗ[ℂ] ⨂[ℂ] w : ι, Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w) :=
  PiTensorProduct.congr fun w => GlobalTheory.RealLift.LieFirstPf.swapE (P w) (Q w) (R w) (S w)

theorem swapTD_atPl (w : ι) (L' : Module.End ℂ (Formalism.BasicNotions.TH.Pol (R w) (S w) (P w) (Q w)))
    (L : Module.End ℂ (Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w)))
    (h : ∀ f, GlobalTheory.RealLift.LieFirstPf.swapE (P w) (Q w) (R w) (S w) (L' f) =
      L (GlobalTheory.RealLift.LieFirstPf.swapE (P w) (Q w) (R w) (S w) f))
    (T : ⨂[ℂ] w : ι, Formalism.BasicNotions.TH.Pol (R w) (S w) (P w) (Q w)) :
    swapTD P Q R S (atPl w L' T) = atPl w L (swapTD P Q R S T) := by
  have e : (swapTD P Q R S).toLinearMap ∘ₗ atPl w L' = atPl w L ∘ₗ (swapTD P Q R S).toLinearMap := by
    refine PiTensorProduct.ext (MultilinearMap.ext fun x => ?_)
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, atPl, swapTD,
      PiTensorProduct.map_tprod, PiTensorProduct.congr_tprod]
    congr 1
    funext i
    by_cases hi : i = w
    · subst hi; simp [h]
    · simp [Function.update_of_ne hi]
  exact LinearMap.congr_fun e T

theorem swapTD_sumPl (L' : ∀ w, Module.End ℂ (Formalism.BasicNotions.TH.Pol (R w) (S w) (P w) (Q w)))
    (L : ∀ w, Module.End ℂ (Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w)))
    (h : ∀ w f, GlobalTheory.RealLift.LieFirstPf.swapE (P w) (Q w) (R w) (S w) (L' w f) =
      L w (GlobalTheory.RealLift.LieFirstPf.swapE (P w) (Q w) (R w) (S w) f))
    (T : ⨂[ℂ] w : ι, Formalism.BasicNotions.TH.Pol (R w) (S w) (P w) (Q w)) :
    swapTD P Q R S (sumPl L' T) = sumPl L (swapTD P Q R S T) := by
  simp only [sumPl, LinearMap.sum_apply, map_sum]
  exact Finset.sum_congr rfl fun w _ => swapTD_atPl w (L' w) (L w) (h w) T

end Tensor

theorem lieFirstD : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (α β κ : Type) [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : InfinitePlace F → ℕ)
    (ψ : AddChar (AF F) ℂ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (d' : Darboux (symp (R := AF F) (cA σ) (-1) JB JA) κ) (a b : ℂ)
    (A : ∀ w : InfinitePlace F, Matrix α (Ix (P w) (Q w)) ℂ) (C : ∀ w : InfinitePlace F, Matrix β (Ix (R w) (S w)) ℂ)
    (Φ : TensD F P Q R S →ₗ[ℂ] SInf F κ) (om : UG (cA σ) JA →* Module.End ℂ ((κ → AF F) → ℂ)),
    IsCMExt F E σ → IsStd ψ → FramedD τ JA JB a b A C → IsFockMapD ψ τ d A C Φ →
    (∀ x : Matrix α β (AE F E), d'.e xᵀ = d.e x) → IsUSplitting (adeleClass F) ψ d' (actB (cA σ)) om →
    ∃ c, ActsByD τ A om Φ (fun w => fockAct1 (P w) (Q w) (R w) (S w)) c := by
  intro F E _ _ _ _ _ σ α β κ _ _ _ _ _ P Q R S ψ τ JA JB d d' a b A C Φ om hCM hψ hfr hΦ hdd hW
  have hfr' : FramedD τ JB JA b a C A := ⟨by rw [mul_comm]; exact hfr.1, hfr.2.2, hfr.2.1⟩
  have hΦ' : IsFockMapD ψ τ d' C A (Φ ∘ₗ (swapTD P Q R S).toLinearMap) := by
    refine ⟨hΦ.1.comp (swapTD P Q R S).injective, fun u hu c hc T => ?_⟩
    have hu' : At (evI F) uᵀ := fun x hx => by rw [← Matrix.transpose_smul, hu x hx, Matrix.transpose_zero]
    have hc' : ∀ w, uᵀ.map (piInf (τ w)) = A w * (c w)ᵀ * (C w)ᵀ := fun w => by
      rw [Matrix.transpose_map, hc w]; simp [Matrix.transpose_mul, Matrix.mul_assoc]
    have key := hΦ.2 uᵀ hu' (fun w => (c w)ᵀ) hc' (swapTD P Q R S T)
    have hr : ∀ t : ℝ, d'.rho ψ (realAd F t • u) = d.rho ψ (realAd F t • uᵀ) := fun t => by
      show schr ψ (d'.e _) = schr ψ (d.e _)
      rw [← hdd, Matrix.transpose_smul, Matrix.transpose_transpose]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hr]
    rwa [swapTD_sumPl (fun w => heisOp (c w)) (fun w => heisOp (c w)ᵀ)
      (fun w f => GlobalTheory.RealLift.LieFirstPf.swapE_heisOp (c w) f)]
  obtain ⟨c, hA⟩ := GlobalTheory.T.howeSplitting_acts_fockAction_plus_traceMultiples F E σ β α κ R S P Q ψ τ JB JA d' b a C A _ om hCM hψ hfr' hΦ' hW
  refine ⟨c, fun γ hγ Y hY T => ?_⟩
  have key := hA γ hγ Y hY ((swapTD P Q R S).symm T)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at key
  rwa [swapTD_sumPl (fun w => fockAct2 (R w) (S w) (P w) (Q w) (Y w) + (c w * (Y w).trace) • 1)
    (fun w => fockAct1 (P w) (Q w) (R w) (S w) (Y w) + (c w * (Y w).trace) • 1) (fun w f => by
      simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply, map_add, map_smul,
        GlobalTheory.RealLift.LieFirstPf.swapE_apply, (GlobalTheory.FockSwap.swap_symmetry (R w) (S w) (P w) (Q w)).2.1]),
    LinearEquiv.apply_symm_apply] at key

end GlobalTheory.HoweD.LieFirstD
