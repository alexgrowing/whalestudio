import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Entire
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.AdelicCharacterRationalDual
import GroundTheory.AutomorphicForms.GL2.GJMatrixAdelic
import GroundTheory.GlobalFields.TateThesis.GaussianSchwartz

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical

namespace UpperTheory.ConvolutionTheory.RankTwoDescent

private abbrev Fa : Type := FiniteAdeleRing (𝓞 ℚ) ℚ

private theorem dv_iff {N : ℕ} (hN : 0 < N) (z : Fa) :
    (∀ v : H.P ℚ, Valued.v (z v) ≤ Valued.v ((N : H.Kv v))) ↔
      ∃ u : Fa, (∀ v, u v ∈ v.adicCompletionIntegers ℚ) ∧ z = N • u := by
  have hNq : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  set w : Fa := algebraMap ℚ Fa (N : ℚ)⁻¹ with hw
  have hwN : w * (N : Fa) = 1 := by
    rw [hw, ← map_natCast (algebraMap ℚ Fa), ← map_mul, inv_mul_cancel₀ hNq, map_one]
  constructor
  · intro h
    refine ⟨w * z, fun v => ?_, ?_⟩
    · rw [HeightOneSpectrum.mem_adicCompletionIntegers]
      have e1 : (w * z) v = w v * z v := rfl
      have e2 : w v * (N : H.Kv v) = 1 := by
        have := congrArg (pLoc ℚ v) hwN
        rwa [map_mul, map_natCast, map_one] at this
      rw [e1, map_mul]
      calc Valued.v (w v) * Valued.v (z v) ≤ Valued.v (w v) * Valued.v (N : H.Kv v) := mul_le_mul' le_rfl (h v)
        _ = 1 := by rw [← map_mul, e2, map_one]
    · rw [nsmul_eq_mul, ← mul_assoc, mul_comm (N : Fa), hwN, one_mul]
  · rintro ⟨u, hu, rfl⟩ v
    have e1 : (N • u) v = (N : H.Kv v) * u v := by
      exact (map_nsmul (pLoc ℚ v) N u).trans (nsmul_eq_mul _ _)
    rw [e1, map_mul]
    have := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hu v)
    exact mul_le_of_le_one_right' this

private abbrev Mx : Type := mixedEmbedding.mixedSpace ℚ

private instance : IsEmpty {w : InfinitePlace ℚ // w.IsComplex} :=
  ⟨fun w => InfinitePlace.not_isReal_iff_isComplex.2 w.2 (Subsingleton.elim w.1 Rat.infinitePlace ▸ Rat.isReal_infinitePlace)⟩

private def mE : Mx ≃L[ℝ] ℝ :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun y => y.1 ⟨Rat.infinitePlace, Rat.isReal_infinitePlace⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      invFun := fun t => (fun _ => t, 0)
      left_inv := fun y => by
        refine Prod.ext (funext fun w => ?_) (Subsingleton.elim _ _)
        exact congrArg y.1 (Subsingleton.elim (α := {w : InfinitePlace ℚ // w.IsReal}) _ _)
      right_inv := fun _ => rfl }

private def eE : (Fin 2 → Mx) ≃L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  (ContinuousLinearEquiv.piCongrRight fun _ => mE).trans (EuclideanSpace.equiv (Fin 2) ℝ).symm

private theorem eE_apply (x : Fin 2 → A ℚ) (i : Fin 2) : eE (infPartPi x) i = re (x i) := rfl

private theorem temp (p : MvPolynomial (Fin 2) ℂ) :
    (fun y : Fin 2 → Mx => MvPolynomial.eval (fun i => ((eE y i : ℝ) : ℂ)) p).HasTemperateGrowth := by
  induction p using MvPolynomial.induction_on with
  | C a => simpa using Function.HasTemperateGrowth.const a
  | add p q hp hq =>
    simp only [map_add]
    exact hp.add hq
  | mul_X p k hp =>
    simp only [map_mul, MvPolynomial.eval_X]
    refine hp.mul ?_
    exact (Complex.ofRealCLM.comp ((EuclideanSpace.proj k : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).comp
      eE.toContinuousLinearMap)).hasTemperateGrowth

private def phiS (p : MvPolynomial (Fin 2) ℂ) : SchwartzMap (Fin 2 → Mx) ℂ :=
  SchwartzMap.smulLeftCLM ℂ (fun y : Fin 2 → Mx => MvPolynomial.eval (fun i => ((eE y i : ℝ) : ℂ)) p)
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ eE (gaussianSchwartz (EuclideanSpace ℝ (Fin 2))))

private theorem cond_iff {N : ℕ} (hN : 0 < N) (x : Fin 2 → A ℚ) :
    (∀ v, Dv N v (x 0) ∧ Dv N v (x 1 - 1)) ↔
      ∀ i, ∃ u : Fa, (∀ v, u v ∈ v.adicCompletionIntegers ℚ) ∧
        finPartPi x i = algebraMap ℚ Fa ((![0, 1] : Fin 2 → ℚ) i) + N • u := by
  have h0 := dv_iff hN (x 0).2
  have h1 := dv_iff hN ((x 1 - 1).2)
  have e1 : ∀ u : Fa, (x 1 - 1).2 = N • u ↔ (x 1).2 = 1 + N • u := fun u => by
    change (x 1).2 - 1 = N • u ↔ _
    rw [sub_eq_iff_eq_add']
  constructor
  · intro h i
    fin_cases i
    · obtain ⟨u, hu, e⟩ := h0.1 fun v => (h v).1
      exact ⟨u, hu, by simpa [finPartPi] using e⟩
    · obtain ⟨u, hu, e⟩ := h1.1 fun v => (h v).2
      exact ⟨u, hu, by simpa [finPartPi] using (e1 u).1 e⟩
  · intro h v
    refine ⟨h0.2 ?_ v, h1.2 ?_ v⟩
    · obtain ⟨u, hu, e⟩ := h 0
      exact ⟨u, hu, by simpa [finPartPi] using e⟩
    · obtain ⟨u, hu, e⟩ := h 1
      exact ⟨u, hu, (e1 u).2 (by simpa [finPartPi] using e)⟩

private theorem phiS_apply (p : MvPolynomial (Fin 2) ℂ) (x : Fin 2 → A ℚ) :
    phiS p (infPartPi x) = MvPolynomial.eval (fun i => (re (x i) : ℂ)) p *
      Complex.exp (-(Real.pi : ℂ) * ((re (x 0) ^ 2 + re (x 1) ^ 2 : ℝ) : ℂ)) := by
  rw [phiS, SchwartzMap.smulLeftCLM_apply_apply (temp p), SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
    Function.comp_apply, gaussianSchwartz_apply, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, smul_eq_mul]
  simp only [eE_apply]
  push_cast
  rfl

theorem phiMem_of :
    PhiMem := by
  intro N p hN
  have e : PhiN N p = schwartzBruhatTensorPi (phiS p) (GlobalTheory.CompanionTheory.ThetaUniq.cosetInd ℚ N ![0, 1]) := by
    funext x
    rw [PhiN, schwartzBruhatTensorPi, phiS_apply, GlobalTheory.CompanionTheory.ThetaUniq.cosetInd, Set.indicator_apply]
    split_ifs with h h' h''
    · rw [Pi.one_apply, mul_one]
    · exact absurd ((cond_iff hN x).1 h) h'
    · exact absurd ((cond_iff hN x).2 h'') h
    · rw [mul_zero]
  rw [e]
  exact schwartzBruhatTensorPi_mem _
    ((mem_finiteSchwartzBruhatPi ℚ).2 (GlobalTheory.CompanionTheory.ThetaUniq.cosetInd_mem_SB ℚ (Fin 2) N hN _))

end UpperTheory.ConvolutionTheory.RankTwoDescent

end
