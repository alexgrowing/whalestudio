import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.DerivativeRightTranslateL2
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.FrameAd
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

theorem UpperTheory.V.Lit.Bor.delCochain :
    UpperTheory.V.Lit.Bor.DelCochain := by
  intro E _ _ _ a n e he M _ _ _ _ κ L h q ω hω k X
  let β : Herm E a →ₗ[ℝ] Herm E a →ₗ[ℝ] M :=
    LinearMap.mk₂ ℝ (fun Y Z => L (toL Y.1) (ω.curryLeft Z fun i => adHerm k (X i)))
      (fun Y Y' Z => LinearMap.congr_fun (map_add L (toL Y.1) (toL Y'.1)) _)
      (fun c Y Z => LinearMap.congr_fun (map_smul L c (toL Y.1)) _)
      (fun Y Z Z' => by rw [map_add, AlternatingMap.add_apply, map_add])
      (fun c Y Z => by
        rw [map_smul, AlternatingMap.smul_apply]
        exact ((L (toL Y.1)).restrictScalars ℝ).map_smul c _)
  have hβ : ∀ Y Z, β Y Z = L (toL Y.1) (ω (Matrix.vecCons Z fun i => adHerm k (X i))) := fun _ _ => rfl
  have key := UpperTheory.V.Lit.Bor.frameAd E a n e he M β k
  simp only [hβ] at key
  rw [del_apply, del_apply, map_sum, ← key]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hc : (Matrix.vecCons (adHerm k (e j)) fun i => adHerm k (X i)) =
      fun i => adHerm k (Matrix.vecCons (e j) X i) := by
    funext i
    refine Fin.cases ?_ (fun i => ?_) i <;> rfl
  rw [hc, hω k]
  exact (LinearMap.congr_fun (h k (e j)) _).symm
