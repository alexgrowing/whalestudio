import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.DerivativeRightTranslateL2
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.BasicEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.LevelOp
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

private theorem cmp_rT {W : Type} [AddCommGroup W] [Module ℂ W] {d : ℕ} (T : W →ₗ[ℂ] W) (i : Fin d)
    (m : W ⊗[ℂ] (Fin d → ℂ)) : cmp i (T.rTensor _ m) = T (cmp i m) := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul φ v => simp only [LinearMap.rTensor_tmul, cmp_tmul, map_smul]

private theorem ex_cmp {W : Type} [AddCommGroup W] [Module ℂ W] {d : ℕ} {m : W ⊗[ℂ] (Fin d → ℂ)} (h : m ≠ 0) :
    ∃ i, cmp i m ≠ 0 := by
  by_contra hc
  push Not at hc
  apply h
  rw [← sum_cmp m]
  simp [hc]

private theorem rT_map {W : Type} [AddCommGroup W] [Module ℂ W] {d : ℕ} (T A : Module.End ℂ W)
    (B : Module.End ℂ (Fin d → ℂ)) (h : Commute T A) (m : W ⊗[ℂ] (Fin d → ℂ)) :
    T.rTensor _ (TensorProduct.map A B m) = TensorProduct.map A B (T.rTensor _ m) := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul φ v =>
    simp only [LinearMap.rTensor_tmul, TensorProduct.map_tmul]
    congr 1
    exact LinearMap.congr_fun h.eq φ

theorem UpperTheory.V.Lit.Bor.levelCo :
    UpperTheory.V.Lit.Bor.LevelCo := by
  intro E _ _ _ a U hU π Ξ hC hF
  obtain ⟨q, ω, h0, hK, hB⟩ := basicEx E a _ (tensorK π Ξ) (tensorLie π Ξ) hC
  obtain ⟨X, hX⟩ : ∃ X, ω X ≠ 0 := by
    by_contra hc
    push Not at hc
    exact h0 (AlternatingMap.ext hc)
  obtain ⟨i, hi⟩ := ex_cmp hX
  obtain ⟨T, hT, hTK, hTU⟩ := levelOp E a U hU π hF _ hi
  refine ⟨q, ((T.rTensor (Fin Ξ.d → ℂ)).restrictScalars ℝ).compAlternatingMap ω, fun h => hT ?_, fun k Y => ?_,
    fun Y j hj => ?_, fun Y j u hu => ?_⟩
  · have h1 : T.rTensor (Fin Ξ.d → ℂ) (ω X) = 0 := DFunLike.congr_fun h X
    rw [← cmp_rT, h1, map_zero]
  · change T.rTensor (Fin Ξ.d → ℂ) (ω _) = tensorK π Ξ k (T.rTensor (Fin Ξ.d → ℂ) (ω Y))
    rw [hK k Y]
    exact rT_map T _ _ (hTK k) _
  · change T.rTensor (Fin Ξ.d → ℂ) (ω Y) = 0
    rw [hB Y j hj, map_zero]
  · change π.op (.fin u) (cmp j (T.rTensor (Fin Ξ.d → ℂ) (ω Y))) = cmp j (T.rTensor (Fin Ξ.d → ℂ) (ω Y))
    rw [cmp_rT]
    exact hTU _ u hu
