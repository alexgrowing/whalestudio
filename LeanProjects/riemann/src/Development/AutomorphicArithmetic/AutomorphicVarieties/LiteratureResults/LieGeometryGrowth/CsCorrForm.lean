import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsSecOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.MatSmooth
open UpperTheory.V.Lit.Geo.Cs
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open scoped TensorProduct ContDiff Topology

private theorem ev_eq_cmp {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a d : ℕ}
    (m : Sm E a ⊗[ℂ] (Fin d → ℂ)) (j : Fin d) (g : GA E a) : ev m g j = (UpperTheory.V.Lit.Bor.cmp j m).1 g := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | tmul φ v => simp [mul_comm]

private theorem alt_expand {V W M : Type} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    [AddCommGroup M] [Module ℝ M] {q n : ℕ} (α : V [⋀^Fin q]→ₗ[ℝ] M) (e : V ≃ₗ[ℝ] W) (b : Module.Basis (Fin n) ℝ W)
    (u : Fin q → W) :
    α (fun i => e.symm (u i)) = ∑ I : Fin q → Fin n, (∏ i, b.repr (u i) (I i)) • α fun i => e.symm (b (I i)) := by
  have h : (fun i => e.symm (u i)) = fun i => ∑ k, b.repr (u i) k • e.symm (b k) := by
    funext i
    conv_lhs => rw [← b.sum_repr (u i)]
    simp only [map_sum, map_smul]
  rw [h]
  refine (α.toMultilinearMap.map_sum (fun i k => b.repr (u i) k • e.symm (b k))).trans ?_
  exact Finset.sum_congr rfl fun I _ => α.map_smul_univ _ _

theorem UpperTheory.V.Lit.Geo.Cs.corrForm :
    CorrForm := by
  intro E _ _ _ a Ξ q v
  classical
  obtain ⟨τ, h1, hτ, -, -, hi, hs⟩ := secOne E a
  let b := Module.finBasis ℝ (HV E a)
  let u : HV E a → Fin q → HV E a := fun p i => (2 : ℝ)⁻¹ • sand (τ p)⁻¹ (v i)
  refine ⟨(Fin q → Fin (Module.finrank ℝ (HV E a))) × Fin Ξ.d, inferInstance,
    fun I i => hv.symm (b (I.1 i)), fun I => I.2,
    fun I p k => ((∏ i, b.repr (u p i) (I.1 i) : ℝ) : ℂ) * Ξ.mat (τ p) k I.2,
    fun p => toL (τ p).val, by simp only [h1]; rfl, hτ, fun I => ?_, fun U α w hc g x => ?_⟩
  · refine contDiffAt_pi.2 fun k => ContDiffAt.mul ?_ ?_
    · refine Complex.ofRealCLM.contDiff.contDiffAt.comp (hOne E a)
        (f := fun p => ∏ i, b.repr (u p i) (I.1 i)) ?_
      refine contDiffAt_prod fun i _ => ?_
      have hu : ContDiffAt ℝ ∞ (fun p => u p i) (hOne E a) := (hi.clm_apply contDiffAt_const).const_smul _
      exact (LinearMap.toContinuousLinearMap (b.coord (I.1 i))).contDiff.contDiffAt.comp (hOne E a) hu
    · have := (((matSmooth E a Ξ k I.2).1).contDiffAt
          (isOpen_invSet.mem_nhds (val_mem_invSet (τ (hOne E a))))).comp (hOne E a) hτ
      simpa only [Function.comp_def, extGL_val] using this
  · refine hs.mono fun p hp => ?_
    have e1 : sand (g * τ p) (hOne E a) = sand g p := by
      rw [map_mul, ContinuousLinearMap.mul_apply, hp]
    have e2 : ∀ i, (2 : ℝ) • sand (g * τ p) (u p i) = sand g (v i) := fun i => by
      simp only [u, map_smul, smul_smul]
      rw [← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel_right]
      simp
    have h := hc (g * τ p) x fun i => hv.symm (u p i)
    simp only [LinearEquiv.apply_symm_apply, e1, e2] at h
    have e3 : infGL E a (g * τ p) * finGL E a x = pt g x * infGL E a (τ p) := pt_mul g (τ p) x
    simp only [Tw, tp_apply, mulVecL_apply, h, e3, Matrix.mulVec_mulVec, ← map_mul, inv_mul_cancel_left, chart_val]
    rw [alt_expand α hv b (u p)]
    funext k
    have e4 : ∀ (I : Fin q → Fin (Module.finrank ℝ (HV E a))) (r : ℝ) (y : GA E a),
        ev (r • α fun i => hv.symm (b (I i))) y = (r : ℂ) • ev (α fun i => hv.symm (b (I i))) y := fun I r y => by
      rw [← algebraMap_smul ℂ r, map_smul]; rfl
    rw [map_sum]
    simp only [Finset.sum_apply, e4, Matrix.mulVec, dotProduct, Pi.smul_apply, ← ev_eq_cmp,
      Fintype.sum_prod_type, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun I _ => Finset.sum_congr rfl fun j _ => ?_
    ring
