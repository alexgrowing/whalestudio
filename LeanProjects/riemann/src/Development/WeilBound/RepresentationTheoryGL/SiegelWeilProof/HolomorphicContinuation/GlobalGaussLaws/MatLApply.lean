import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.NormIterFstComp
import GroundTheory.GlobalFields.IdeleGroups.GaloisOnAdeles.Action

noncomputable section

open Filter Topology MvPolynomial Set
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.Glob.SchDH

variable {m n : ℕ}

def matLin (M : Matrix (Fin m) (Fin m) ℂ) : (Fin m → Fin n → ℂ) →ₗ[ℝ] (Fin m → Fin n → ℂ) where
  toFun y := fun a i => ∑ c, M a c * y c i
  map_add' y z := by funext a i; simp [mul_add, Finset.sum_add_distrib]
  map_smul' r y := by
    funext a i
    simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Complex.real_smul, Complex.real_smul]; ring

def matL (M : Matrix (Fin m) (Fin m) ℂ) : (Fin m → Fin n → ℂ) →L[ℝ] (Fin m → Fin n → ℂ) :=
  LinearMap.toContinuousLinearMap (matLin M)

theorem matL_apply (M : Matrix (Fin m) (Fin m) ℂ) (y : Fin m → Fin n → ℂ) (a : Fin m) (i : Fin n) :
    matL M y a i = ∑ c, M a c * y c i := rfl

theorem matL_mul (M N : Matrix (Fin m) (Fin m) ℂ) (y : Fin m → Fin n → ℂ) : matL (M * N) y = matL M (matL N y) := by
  funext a i
  simp only [matL_apply, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

theorem matL_one (y : Fin m → Fin n → ℂ) : matL (1 : Matrix (Fin m) (Fin m) ℂ) y = y := by
  funext a i
  simp [matL_apply, Matrix.one_apply]

theorem contDiff_A (X : Matrix (Fin m) (Fin m) ℂ) :
    ContDiff ℝ ∞ (fun t : ℝ => matL (n := n) (NormedSpace.exp ((t : ℂ) • X))) := by
  letI : NormedAddCommGroup (Matrix (Fin m) (Fin m) ℂ) := Matrix.linftyOpNormedAddCommGroup
  letI : NormedSpace ℝ (Matrix (Fin m) (Fin m) ℂ) := Matrix.linftyOpNormedSpace
  letI : NormedRing (Matrix (Fin m) (Fin m) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (Fin m) (Fin m) ℂ) := Matrix.linftyOpNormedAlgebra
  let Lm : Matrix (Fin m) (Fin m) ℂ →ₗ[ℝ] ((Fin m → Fin n → ℂ) →L[ℝ] (Fin m → Fin n → ℂ)) :=
    { toFun := matL
      map_add' := fun M N => by ext y a i; simp [matL_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := fun r M => by
        ext y a i
        simp only [matL_apply, Matrix.smul_apply, RingHom.id_apply, ContinuousLinearMap.smul_apply, Pi.smul_apply,
          Finset.smul_sum]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Complex.real_smul, Complex.real_smul]; ring }
  have hexp : ContDiff ℝ ∞ (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X)) := by
    have e : (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X)) = NormedSpace.exp ∘ (fun t : ℝ => t • X) := by
      funext t; simp only [Function.comp_apply, Complex.coe_smul]
    rw [e]
    exact (contDiff_iff_contDiffAt.2 fun x => (NormedSpace.exp_analytic (𝕂 := ℝ) x).contDiffAt).comp
      (contDiff_id.smul contDiff_const)
  exact (LinearMap.toContinuousLinearMap Lm).contDiff.comp hexp

theorem hasDerivAt_entry (X : Matrix (Fin m) (Fin m) ℂ) (a c : Fin m) :
    HasDerivAt (fun t : ℝ => (NormedSpace.exp ((t : ℂ) • X)) a c) (X a c) 0 := by
  letI : NormedAddCommGroup (Matrix (Fin m) (Fin m) ℂ) := Matrix.linftyOpNormedAddCommGroup
  letI : NormedSpace ℝ (Matrix (Fin m) (Fin m) ℂ) := Matrix.linftyOpNormedSpace
  letI : NormedRing (Matrix (Fin m) (Fin m) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (Fin m) (Fin m) ℂ) := Matrix.linftyOpNormedAlgebra
  let ent : Matrix (Fin m) (Fin m) ℂ →ₗ[ℝ] ℂ :=
    { toFun := fun M => M a c, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have h := (hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ))
  have h2 := (LinearMap.toContinuousLinearMap ent).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h
  have e : (fun t : ℝ => (NormedSpace.exp ((t : ℂ) • X)) a c) =
      (LinearMap.toContinuousLinearMap ent) ∘ (fun u : ℝ => NormedSpace.exp (u • X)) := by
    funext t; simp only [Function.comp_apply, Complex.coe_smul]; rfl
  have h3 : HasDerivAt (fun t : ℝ => (NormedSpace.exp ((t : ℂ) • X)) a c)
      ((LinearMap.toContinuousLinearMap ent) (NormedSpace.exp ((0 : ℝ) • X) * X)) 0 := by
    rw [e]; exact h2
  have h4 : (LinearMap.toContinuousLinearMap ent) (NormedSpace.exp ((0 : ℝ) • X) * X) = X a c := by
    rw [zero_smul, NormedSpace.exp_zero, one_mul]; rfl
  rw [h4] at h3
  exact h3

theorem exists_gs (c : ℝ) (hc : 0 < c) : ∃ g : SchwartzMap (Fin m → Fin n → ℂ) ℂ, ∀ u, g u = gs c u := by
  obtain ⟨g0, hg0⟩ := GlobalTheory.CompanionTheory.PolyGaussSchwartz.exists_gauss (m := m) (n := n)
  set s : ℝ := Real.sqrt (c / (2 * Real.pi)) with hs
  have hs0 : s ≠ 0 := (Real.sqrt_pos.2 (by positivity)).ne'
  let L : (Fin m → Fin n → ℂ) ≃L[ℝ] (Fin m → Fin n → ℂ) :=
    (LinearEquiv.smulOfNeZero ℝ (Fin m → Fin n → ℂ) s hs0).toContinuousLinearEquiv
  refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L g0, fun u => ?_⟩
  rw [SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply, hg0]
  have key : 2 * Real.pi * ∑ a, ∑ i, ‖(L u) a i‖ ^ 2 = c * ∑ a, ∑ i, ‖u a i‖ ^ 2 := by
    have h1 : ∀ a i, ‖(L u) a i‖ ^ 2 = s ^ 2 * ‖u a i‖ ^ 2 := fun a i => by
      change ‖(s • u) a i‖ ^ 2 = _
      rw [Pi.smul_apply, Pi.smul_apply, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    simp only [h1, ← Finset.mul_sum]
    rw [hs, Real.sq_sqrt (by positivity)]
    field_simp
  unfold gs
  rw [key]

theorem exists_fP (c : ℝ) (hc : 0 < c) (P : PX m n) :
    ∃ φ : SchwartzMap (Fin m → Fin n → ℂ) ℂ, ∀ u, φ u = fP c P u := by
  obtain ⟨g, hg⟩ := exists_gs (m := m) (n := n) c hc
  refine ⟨SchwartzMap.smulLeftCLM ℂ (fun u => MvPolynomial.eval (fun k => GlobalTheory.CompanionTheory.PolyGaussSchwartz.coord k u) P) g,
    fun u => ?_⟩
  rw [SchwartzMap.smulLeftCLM_apply_apply (GlobalTheory.CompanionTheory.PolyGaussSchwartz.eval_temperate P), hg, smul_eq_mul]
  rfl

end PositivityTheory.Rg.Sw.Glob.SchDH
