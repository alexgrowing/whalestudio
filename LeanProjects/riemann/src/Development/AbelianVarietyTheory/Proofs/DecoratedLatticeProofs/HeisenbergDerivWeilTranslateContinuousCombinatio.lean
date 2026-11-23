import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLast
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfAeFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsBiThetaIffJoin
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BiThetaOfVac
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HeisLineComb

open GlobalTheory.WeilVacMove GlobalTheory.FockCompare

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem actO_actO_inv (g : GA D S) (h : GA D T) (x : WO S T) : actO S T g h (actO S T g⁻¹ h⁻¹ x) = x := by
  unfold actO
  rw [inv_inv]
  calc HMul.hMul (HMul.hMul (mt T h) (HMul.hMul (HMul.hMul (mt T h⁻¹) x) (mt S g))) (mt S g⁻¹)
      = HMul.hMul (HMul.hMul (HMul.hMul (mt T h) (mt T h⁻¹)) x) (HMul.hMul (mt S g) (mt S g⁻¹)) := by
        simp only [Matrix.mul_assoc]
    _ = x := by rw [← GlobalTheory.WeilVacMove.mt_mul, ← GlobalTheory.WeilVacMove.mt_mul, mul_inv_cancel, mul_inv_cancel, GlobalTheory.WeilVacMove.mt_one, GlobalTheory.WeilVacMove.mt_one, Matrix.one_mul, Matrix.mul_one]

theorem dLine_apply {θ : GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition.InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (h : Chart θ σ)
    {lam : AF D.host.F →+ ℂ} (hl : Continuous lam) (hlam : ∀ a, sndA D.host.F a = 0 → ψ a = Complex.exp (lam a))
    {L : ℝ →+ WO S T} (hL : Continuous L) (hL0 : ∀ t, (L t).map (finPart D) = 0) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (w : WO S T) :
    dLine ψ S T L f w = phase lam S T (L 1) w * f w +
      fderiv ℝ (fun x => f (w + iotaW σ T S x)) 0 (piW θ T S (L 1)) := by
  have hline := (smooth_iff_sm_and_real_lines D θ σ h T S).2.1 L ⟨hL, hL0⟩
  have hfs := ((smooth_iff_sm_and_real_lines D θ σ h T S).1 f).1 hf.smooth
  have e : (fun t : ℝ => heisO ψ S T (L t) f w) = fun t : ℝ => Complex.exp (t * phase lam S T (L 1) w) *
      f (w + iotaW σ T S (t • piW θ T S (L 1))) := by
    funext t
    rw [heisO, psi_sympl_line hl hlam hL hL0, ← hline t]
  unfold dLine
  rw [e]
  exact (hasDerivAt_exp_mul _ _ f hfs _ w).deriv

theorem dLine_eq_sum (hψ : IsStdChar D ψ (-1)) {θ : GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition.InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D}
    (h : Chart θ σ) {ι : Type} [Fintype ι] (b : Module.Basis ι ℝ (RW T S)) {L : ℝ →+ WO S T} (hL : Continuous L)
    (hL0 : ∀ t, (L t).map (finPart D) = 0) (N : ι → ℝ →+ WO S T) (hN : ∀ i, Continuous (N i))
    (hN0 : ∀ i t, (N i t).map (finPart D) = 0) (hN1 : ∀ i, piW θ T S (N i 1) = b i) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) :
    dLine ψ S T L f = ∑ i, ((b.coord i (piW θ T S (L 1)) : ℝ) : ℂ) • dLine ψ S T (N i) f := by
  obtain ⟨lam, hl, hlam⟩ := exists_log hψ
  funext w
  let A : RW T S →+ ℂ := AddMonoidHom.mk' (fun v => lam (symplOH S T w (iotaW σ T S v))) fun u v => by
    rw [map_add, symplOH_add_right, map_add]
  have hA : Continuous A := hl.comp (continuous_symplOH S T continuous_const (h.continuous_iota T S))
  let A' : RW T S →L[ℝ] ℂ := A.toRealLinearMap hA
  let B : RW T S →L[ℝ] ℂ := fderiv ℝ (fun x => f (w + iotaW σ T S x)) 0
  let Φ : RW T S →ₗ[ℝ] ℂ := (LinearMap.mulRight ℝ (f w)).comp A'.toLinearMap + B.toLinearMap
  have key : ∀ (K : ℝ →+ WO S T), Continuous K → (∀ t, (K t).map (finPart D) = 0) →
      dLine ψ S T K f w = Φ (piW θ T S (K 1)) := by
    intro K hK hK0
    rw [dLine_apply h hl hlam hK hK0 hf]
    have e1 : K 1 = iotaW σ T S (piW θ T S (K 1)) := by
      have := (smooth_iff_sm_and_real_lines D θ σ h T S).2.1 K ⟨hK, hK0⟩ 1
      rwa [one_smul] at this
    have e2 : lam (symplOH S T w (K 1)) = A (piW θ T S (K 1)) := by
      show _ = lam (symplOH S T w (iotaW σ T S (piW θ T S (K 1))))
      rw [← e1]
    show lam (symplOH S T w (K 1)) * f w + _ = _
    rw [e2]
    rfl
  rw [Finset.sum_apply, key L hL hL0]
  simp only [Pi.smul_apply, smul_eq_mul]
  simp only [fun i => key (N i) (hN i) (hN0 i), hN1]
  conv_lhs => rw [← b.sum_repr (piW θ T S (L 1))]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, Complex.real_smul, Module.Basis.coord_apply]

theorem dLine_om_comb : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ M : ℝ →+ WO S T, Continuous M → (∀ s, (M s).map (finPart D) = 0) → ∃ (m : ℕ) (N : Fin m → ℝ →+ WO S T) (c : Fin m → GA D S × GA D T → ℂ), (∀ i, Continuous (N i)) ∧ (∀ i s, (N i s).map (finPart D) = 0) ∧ (∀ i, Continuous (c i)) ∧ ∀ p f, IsThetaFunO ψ S T f → GlobalTheory.WeilVacMove.dLine ψ S T M (om p f) = ∑ i, c i p • om p (GlobalTheory.WeilVacMove.dLine ψ S T (N i) f) := by
  intro D ψ S T χS χT om hW M hM hM0
  have hψ := hW.std
  obtain ⟨θ, hθ⟩ := hψ.2.1
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  let b := Module.finBasis ℝ (RW T S)
  let N : Fin (Module.finrank ℝ (RW T S)) → ℝ →+ WO S T := fun i =>
    (iotaW σ T S).comp (ContinuousLinearMap.toSpanSingleton ℝ (b i)).toLinearMap.toAddMonoidHom
  have hN : ∀ i, Continuous (N i) := fun i =>
    (h.continuous_iota T S).comp (ContinuousLinearMap.toSpanSingleton ℝ (b i)).continuous
  have hN0 : ∀ i t, (N i t).map (finPart D) = 0 := fun i t => h.real_iota T S _
  have hN1 : ∀ i, piW θ T S (N i 1) = b i := fun i => by
    show piW θ T S (iotaW σ T S ((1 : ℝ) • b i)) = b i
    rw [h.pi_iota, one_smul]
  let Mp : GA D S × GA D T → ℝ →+ WO S T := fun p =>
    AddMonoidHom.mk' (fun s => actO S T p.1⁻¹ p.2⁻¹ (M s)) fun s t => by rw [map_add, actO_add]
  have hMp : ∀ p, Continuous (Mp p) := fun p =>
    (continuous_const.matrix_mul hM).matrix_mul continuous_const
  have hMp0 : ∀ p t, (Mp p t).map (finPart D) = 0 := fun p t => by
    show (actO S T p.1⁻¹ p.2⁻¹ (M t)).map (finPart D) = 0
    unfold actO
    rw [Matrix.map_mul, Matrix.map_mul, hM0 t, Matrix.mul_zero, Matrix.zero_mul]
  refine ⟨_, N, fun i p => ((b.coord i (piW θ T S (Mp p 1)) : ℝ) : ℂ), hN, hN0, fun i => ?_, fun p f hf => ?_⟩
  · have hc : Continuous fun p : GA D S × GA D T => actO S T p.1⁻¹ p.2⁻¹ (M 1) := by
      unfold actO
      exact (((GlobalTheory.MixModel.continuous_mt T).comp (continuous_snd.inv)).matrix_mul continuous_const).matrix_mul
        ((GlobalTheory.MixModel.continuous_mt S).comp continuous_fst.inv.inv)
    exact Complex.continuous_ofReal.comp ((LinearMap.continuous_of_finiteDimensional (b.coord i)).comp
      ((continuous_pi' hθ T S).comp hc))
  · obtain ⟨g, k⟩ := p
    have e := om_dLine hW g k (hMp (g, k)) (hMp0 (g, k)) hM hM0 (fun t => (actO_actO_inv g k (M t)).symm) hf
    rw [← e, dLine_eq_sum hψ h b (hMp (g, k)) (hMp0 (g, k)) N hN hN0 hN1 hf, map_sum]
    simp only [map_smul]

end GlobalTheory.HeisLineComb

end
