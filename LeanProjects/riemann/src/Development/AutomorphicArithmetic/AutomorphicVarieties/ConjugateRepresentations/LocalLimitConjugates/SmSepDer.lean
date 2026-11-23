import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasimirResolventProjection
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.InfAbs
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualInfinitesimalCharacterRegular
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

private theorem sm_sepDer (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (Ξ : AlgRep E a) :
    SepDer (smK Ξ) (smLie Ξ) := by
  intro k Z h0 hk m' hm
  have h1 : ∃ j, Bor.cmp j m' ≠ 0 := by
    by_contra h
    push Not at h
    apply hm
    rw [← sum_cmp m']
    simp [h]
  obtain ⟨j, hj⟩ := h1
  have h2 : (Bor.cmp j m').1 ≠ 0 := fun h => hj (Subtype.ext h)
  obtain ⟨g, hg⟩ := Function.ne_iff.1 h2
  let l : Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun m => (Bor.cmp j m).1 g
      map_add' := fun x y => by rw [map_add]; rfl
      map_smul' := fun c x => by rw [map_smul]; rfl }
  have hl : ∀ (φ : Sm E a) (v : Fin Ξ.d → ℂ), l (φ ⊗ₜ v) = φ.1 g * v j := fun φ v => by
    change (Bor.cmp j (φ ⊗ₜ v)).1 g = _
    rw [cmp_tmul, mul_comm]
    rfl
  have hc0 : (fun t => Unitary.toUnits (k t)) 0 = 1 := by simp only [h0, map_one]
  refine ⟨l, hg, fun m => ?_⟩
  induction m using TensorProduct.induction_on with
  | zero => simpa only [map_zero] using hasDerivAt_const (0 : ℝ) (0 : ℂ)
  | add x y hx hy => simpa only [map_add] using hx.fun_add hy
  | tmul φ v =>
    have h3 := GlobalTheory.CuspRep.hasDerivAt_curve φ g (fun t => Unitary.toUnits (k t)) (toL Z) hc0 hk
    have h4 := HasDerivAt.fun_sum (u := Finset.univ) fun i _ =>
      (Ξ.hasDerivAt_curve (fun t => Unitary.toUnits (k t)) (toL Z) hc0 hk j i).mul_const (v i)
    have h5 := h3.fun_mul h4
    simp only [h0, map_one, mul_one] at h5
    have h7 : smLie Ξ (toL Z) (φ ⊗ₜ v) = lie E a (toL Z) φ ⊗ₜ v + φ ⊗ₜ (Ξ.dmat (toL Z) *ᵥ v) := rfl
    simp only [smK, h7, TensorProduct.map_tmul, map_add, hl, Matrix.toLin'_apply]
    have h6 : ∑ i, (1 : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ) j i * v i = v j := congrFun (Matrix.one_mulVec v) j
    rw [h6] at h5
    exact h5

theorem UpperTheory.V.Cj.H.smAB :
    UpperTheory.V.Cj.H.SmAB := by
  intro E _ _ _ a Ξ
  refine ⟨fun X Y => ?_, fun X Y => ?_, fun X Y => ?_, fun k X => ?_, fun k X => ?_,
    infAbs E a _ _ _ (sm_sepDer E a Ξ)⟩
  · simp only [smA_apply]
    rw [← LinearMap.rTensor_mul, ← LinearMap.rTensor_mul, ← LinearMap.rTensor_sub]
    congr 1
    exact (lie_comm (toL X) (toL Y)).trans (map_sub (lie E a) (toL (X * Y)) (toL (Y * X))).symm
  · simp only [smB_apply]
    rw [← GlobalTheory.AlgInfChar.dmat_bracket, map_sub, LinearMap.lTensor_sub, Matrix.toLin'_mul, Matrix.toLin'_mul,
      LinearMap.lTensor_comp, LinearMap.lTensor_comp]
    rfl
  · rw [smA_apply, smB_apply]
    exact TensorProduct.ext' fun _ _ => rfl
  · refine TensorProduct.ext' fun φ v => ?_
    have h1 : act (.cpt k) (lie E a (toL X) φ) = lie E a (toL (k.1 * X * star k.1)) (act (.cpt k) φ) :=
      LinearMap.congr_fun (GlobalTheory.CapAdInv.rt_lie (Unitary.toUnits k) X) φ
    simp only [Module.End.mul_apply, smK, smA_apply, LinearMap.rTensor_tmul, TensorProduct.map_tmul, h1]
  · refine TensorProduct.ext' fun φ v => ?_
    have h2 : Ξ.mat (Unitary.toUnits k) * Ξ.dmat (toL X) =
        Ξ.dmat (toL (k.1 * X * star k.1)) * Ξ.mat (Unitary.toUnits k) :=
      Ξ.mat_mul_dmat (Unitary.toUnits k) X
    simp only [Module.End.mul_apply, smK, smB_apply, LinearMap.lTensor_tmul, TensorProduct.map_tmul,
      Matrix.toLin'_apply, Matrix.mulVec_mulVec, h2]
