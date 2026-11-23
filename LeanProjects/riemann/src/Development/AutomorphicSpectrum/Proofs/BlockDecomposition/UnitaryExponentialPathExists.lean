import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsTestZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneParameterSubgroupExists
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CompanionTheory.SmoothRep
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.SmoothRep.KCurve

section
open scoped Matrix.Norms.L2Operator

theorem exists_exp_eq_of_unitary {n : ℕ} (k : Matrix (Fin n) (Fin n) ℂ)
    (hu : k ∈ unitary (Matrix (Fin n) (Fin n) ℂ)) :
    ∃ Y : Matrix (Fin n) (Fin n) ℂ, NormedSpace.exp Y = k := by
  haveI : IsStarNormal k :=
    ⟨(Unitary.star_mul_self_of_mem hu).trans (Unitary.mul_star_self_of_mem hu).symm⟩
  have hfin := Matrix.finite_spectrum k
  have hunit : IsUnit k := (Unitary.toUnits ⟨k, hu⟩).isUnit
  have hne : ∀ x ∈ spectrum ℂ k, x ≠ 0 := fun x hx h0 =>
    (spectrum.zero_notMem_iff ℂ).mpr hunit (h0 ▸ hx)
  refine ⟨cfc Complex.log k, ?_⟩
  rw [← CFC.exp_eq_normedSpace_exp (𝕜 := ℂ) (p := IsStarNormal) (a := cfc Complex.log k),
    ← cfc_comp (R := ℂ) (p := IsStarNormal) NormedSpace.exp Complex.log k
      (hg := (hfin.image _).continuousOn _) (hf := hfin.continuousOn _)]
  have hc : cfc (NormedSpace.exp ∘ Complex.log) k = cfc (id : ℂ → ℂ) k := by
    refine cfc_congr fun x hx => ?_
    simp only [Function.comp, id]
    rw [← Complex.exp_eq_exp_ℂ, Complex.exp_log (hne x hx)]
  rw [hc, cfc_id ℂ k]

end

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

def atPlace (w : InfinitePlace E) :
    Matrix (Fin a) (Fin a) (Cinf E) →+* Matrix (Fin a) (Fin a) ℂ :=
  (Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) w).mapMatrix

theorem atPlace_apply (w : InfinitePlace E) (x : Matrix (Fin a) (Fin a) (Cinf E)) (i j : Fin a) :
    atPlace w x i j = x i j w := rfl

theorem continuous_atPlace (w : InfinitePlace E) :
    Continuous (atPlace (a := a) w) :=
  continuous_id.matrix_map (continuous_apply w)

theorem atPlace_star (w : InfinitePlace E) (x : Matrix (Fin a) (Fin a) (Cinf E)) :
    atPlace w (star x) = star (atPlace w x) := by
  ext i j
  rfl

theorem exists_exp_eq (k : Kinf E a) :
    ∃ M : Matrix (Fin a) (Fin a) (Cinf E), NormedSpace.exp M = k.1 := by
  have hk : ∀ w, atPlace w k.1 ∈ unitary (Matrix (Fin a) (Fin a) ℂ) := fun w =>
    Unitary.mem_iff.mpr
      ⟨by rw [← atPlace_star, ← map_mul, Unitary.star_mul_self_of_mem k.2, map_one],
       by rw [← atPlace_star, ← map_mul, Unitary.mul_star_self_of_mem k.2, map_one]⟩
  choose Y hY using fun w => exists_exp_eq_of_unitary (atPlace w k.1) (hk w)
  refine ⟨Matrix.of fun i j w => Y w i j, Matrix.ext fun i j => ?_⟩
  funext w
  have h1 := congrArg (fun m => m i j)
    (NormedSpace.map_exp (atPlace w) (continuous_atPlace w) (Matrix.of fun i j w => Y w i j))
  have hM : atPlace w (Matrix.of fun i j w => Y w i j) = Y w := by
    ext i' j'
    rfl
  simp only [atPlace_apply, hM] at h1
  exact h1.trans ((congrArg (fun m => m i j) (hY w)).trans (atPlace_apply w k.1 i j))

theorem exists_curve : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (k : Kinf E a), ∃ (c : ℝ → GL (Fin a) (Cinf E)) (Y : Lie E a), c 0 = 1 ∧ c 1 = Unitary.toUnits k ∧ (∀ s, HasDerivAt (fun t => toL (c t).val) (toL ((c s).val * Matrix.of Y)) s) ∧ (∀ s, HasDerivAt (fun t => toL ((c t)⁻¹).val) (toL (-(Matrix.of Y * ((c s)⁻¹).val))) s) := by
  intro E _ _ _ a k
  obtain ⟨M, hM⟩ := exists_exp_eq k
  have htoL : ∀ N : Matrix (Fin a) (Fin a) (Cinf E), toL N = GlobalTheory.CompanionTheory.LieCurve.toLieL E a N := fun N => by
    rw [GlobalTheory.CompanionTheory.LieCurve.toLieL_apply]
  have hof : Matrix.of (GlobalTheory.CompanionTheory.LieCurve.toLieL E a M) = M := by
    rw [GlobalTheory.CompanionTheory.LieCurve.toLieL_apply]
    rfl
  refine ⟨GlobalTheory.CompanionTheory.LieCurve.expUnit E a M, GlobalTheory.CompanionTheory.LieCurve.toLieL E a M,
    GlobalTheory.CompanionTheory.LieCurve.expUnit_zero E a M, ?_, fun s => ?_, fun s => ?_⟩
  · apply Units.ext
    rw [GlobalTheory.CompanionTheory.LieCurve.expUnit_val, one_smul, hM]
    rfl
  · simp only [GlobalTheory.CompanionTheory.LieCurve.expUnit_val, hof, htoL]
    exact (GlobalTheory.CompanionTheory.LieCurve.toLieL E a).hasFDerivAt.comp_hasDerivAt s
      (GlobalTheory.CompanionTheory.LieCurve.hasDerivAt_exp E a M s)
  · simp only [GlobalTheory.CompanionTheory.LieCurve.expUnit_inv_val, hof, htoL]
    have h1 := GlobalTheory.CompanionTheory.LieCurve.hasDerivAt_exp E a (-M) s
    have e1 : (fun t : ℝ => NormedSpace.exp (t • -M)) = fun t : ℝ => NormedSpace.exp (-t • M) := by
      funext t
      rw [neg_smul, smul_neg]
    have e2 : NormedSpace.exp (s • -M) * -M = -(M * NormedSpace.exp (-s • M)) := by
      rw [smul_neg, ← neg_smul, mul_neg, ((Commute.refl M).smul_right (-s)).exp_right.eq]
    rw [e1, e2] at h1
    exact (GlobalTheory.CompanionTheory.LieCurve.toLieL E a).hasFDerivAt.comp_hasDerivAt s h1

end GlobalTheory.CompanionTheory.SmoothRep.KCurve
