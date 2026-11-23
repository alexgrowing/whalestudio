import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasimirResolventProjection
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

private def levFnSub {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}
    (U : Subgroup (GL (Fin a) (Af E))) (Ξ : AlgRep E a) : Submodule ℂ (Sm E a) where
  carrier := {φ | IsLevelFn U Ξ φ}
  zero_mem' := ⟨fun _ _ => rfl, fun u _ => map_zero _, fun m _ => by simp⟩
  add_mem' := fun {φ ψ} h h' => ⟨fun γ g => congrArg₂ (· + ·) (h.1 γ g) (h'.1 γ g),
    fun u hu => by rw [map_add, h.2.1 u hu, h'.2.1 u hu],
    fun m hm => by rw [map_add, h.2.2 m hm, h'.2.2 m hm, smul_add]⟩
  smul_mem' := fun c φ h => ⟨fun γ g => congrArg (c • ·) (h.1 γ g),
    fun u hu => by rw [map_smul, h.2.1 u hu],
    fun m hm => by rw [map_smul, h.2.2 m hm, smul_comm]⟩

private theorem cmp_rTensor {W : Type} [AddCommGroup W] [Module ℂ W] {d : ℕ} (T : Module.End ℂ W) (i : Fin d)
    (m : W ⊗[ℂ] (Fin d → ℂ)) : cmp i (T.rTensor (Fin d → ℂ) m) = T (cmp i m) := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul φ v => simp only [LinearMap.rTensor_tmul, cmp_tmul, map_smul]

theorem UpperTheory.V.Cj.H.levLin :
    UpperTheory.V.Cj.H.LevLin := by
  intro E _ _ _ a U Ξ q
  have ap : ∀ (α β : Co Ξ q) (s t : ℂ) X, (s • α + t • β) X = s • α X + t • β X := fun _ _ _ _ _ => rfl
  refine ⟨fun α β s t hα hβ => ⟨fun k X => ?_, fun X i hi => ?_, fun X => ?_⟩, fun α β s t => ?_,
    fun α hα X i => ?_, fun T α X i => ?_⟩
  · rw [ap, ap, hα.equiv k X, hβ.equiv k X, map_add, map_smul, map_smul]
  · rw [ap, hα.basic X i hi, hβ.basic X i hi, smul_zero, smul_zero, add_zero]
  · rw [ap]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (hα.val X)) (Submodule.smul_mem _ _ (hβ.val X))
  · refine AlternatingMap.ext fun X => ?_
    have e : (s • dCo (smLie Ξ) α + t • dCo (smLie Ξ) β) X = s • dCo (smLie Ξ) α X + t • dCo (smLie Ξ) β X := rfl
    rw [e, dCo_apply, dCo_apply, dCo_apply]
    simp only [ap, map_add, map_smul, smul_add, Finset.sum_add_distrib, Finset.smul_sum]
    congr 1 <;> exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _
  · exact mem_tens.1 (span_le_tens (N := levFnSub U Ξ) (fun φ h => h) (hα.val X)) i
  · rw [app_apply, cmp_rTensor]
