import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasimirResolventProjection
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.TmulMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.SqOrth
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.ROpApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.LieOneComm
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

private theorem cmp_rT {W : Type} [AddCommGroup W] [Module ℂ W] {d : ℕ} (T : Module.End ℂ W) (i : Fin d)
    (x : W ⊗[ℂ] (Fin d → ℂ)) : cmp i (T.rTensor _ x) = T (cmp i x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul φ v => simp

private theorem adj_rT {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} (Ξ : AlgRep E a) (r : ℝ)
    (T : Module.End ℂ (Sm E a)) (hT : ∀ X φ, lie E a X (T φ) = T (lie E a X φ)) (X : GlobalTheory.CuspRep.Lie E a)
    (x : Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ)) : smAdj Ξ r X (T.rTensor _ x) = T.rTensor _ (smAdj Ξ r X x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul φ v =>
    simp only [smAdj, adj_apply, smA_apply, smB_apply, map_sub, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul, hT,
      LinearMap.map_smul_of_tower]

private theorem cocl_app {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} (Ξ : AlgRep E a) (r : ℝ)
    {n : ℕ} (e : Fin n → Herm E a)
    (T : Module.End ℂ (Sm E a)) (hT : ∀ X φ, lie E a X (T φ) = T (lie E a X φ)) :
    ∀ {q : ℕ} (ω : Co Ξ q), Coclosed (smAdj Ξ r) e ω → Coclosed (smAdj Ξ r) e (app T ω)
  | 0, _, _ => trivial
  | _ + 1, ω, h => by
    have h' : del (smAdj Ξ r) e ω = 0 := h
    show del (smAdj Ξ r) e (app T ω) = 0
    refine AlternatingMap.ext fun X => ?_
    have h2 := congrArg (fun η => T.rTensor (Fin Ξ.d → ℂ) (η X)) h'
    simp only [del_apply, map_sum, AlternatingMap.zero_apply, map_zero] at h2
    simp only [del_apply, app_apply, adj_rT Ξ r T hT, AlternatingMap.zero_apply, h2]

theorem UpperTheory.V.Cj.H.charOf :
    UpperTheory.V.Cj.H.CharOf := by
  intro E _ _ _ a ha n e he Ξ r m hm q ω h1 h2 h3 h4 X i t u
  have hL := (sqLie E a r).2
  obtain ⟨-, -, c3, c4⟩ := capSm E a Ξ t u
  have hx := wigSm E a Ξ (sqSub E a r) hL t (m t) (hm t) u q ω h1 h2 h4
  have hv : Val (sqSub E a r) (app (cap t u - ((m t).map (u + ·)).prod • 1) ω) := fun Y j => by
    rw [app_apply, cmp_rT, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
    exact Submodule.sub_mem _ (c4 _ hL _ (h4 Y j)) (Submodule.smul_mem _ _ (h4 Y j))
  have hc := cocl_app Ξ r e (cap t u - ((m t).map (u + ·)).prod • 1) (fun Y φ => by
    have := LinearMap.congr_fun (c3 Y).eq φ
    simp only [Module.End.mul_apply] at this
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub, map_smul, this]) ω h3
  have h0 := (sqOrth E a ha n e he Ξ r q).1 _ hv hc hx
  have h5 := congrArg (fun η : Co Ξ q => cmp i (η X)) h0
  simp only [app_apply, cmp_rT, AlternatingMap.zero_apply, map_zero, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.one_apply] at h5
  exact sub_eq_zero.1 h5
