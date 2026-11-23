import Mathlib
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.SummandsAreCuspForms
import GroundTheory.AutomorphicForms.DixmierMalliavinBasic

noncomputable section

namespace GroundTheory.Automorphic

namespace UnitaryAdmissible

open NumberField NumberField.InfinitePlace AutomorphicForm CuspidalSpectrum Reduction
open scoped NumberField.AdeleRing

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

theorem ringEquiv_posIdele (r : ℝ) (hr : 0 < r) :
    InfiniteAdeleRing.ringEquiv_mixedSpace K ((posIdele (K := K) r hr : 𝔸[K]).1) =
      algebraMap ℝ (mixedEmbedding.mixedSpace K) r := by
  rw [InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  ext w
  · show Completion.extensionEmbeddingOfIsReal w.2 ((posIdele (K := K) r hr : 𝔸[K]).1 w) = r
    rw [← GroundTheory.Global.IdeleGroup.coe_infiniteProj, infiniteProj_posIdele]
    show Completion.extensionEmbeddingOfIsReal w.2 (GroundTheory.Global.posRealElem w.1 (r ^ w.1.mult)) = r
    rw [GroundTheory.Global.posRealElem, dif_pos w.2, w.2.mult_eq_one, pow_one,
      ← Completion.ringEquivRealOfIsReal_apply, RingEquiv.apply_symm_apply]
  · show Completion.extensionEmbedding w.1 ((posIdele (K := K) r hr : 𝔸[K]).1 w) = (r : ℂ)
    rw [← GroundTheory.Global.IdeleGroup.coe_infiniteProj, infiniteProj_posIdele]
    show Completion.extensionEmbedding w.1 (GroundTheory.Global.posRealElem w.1 (r ^ w.1.mult)) = r
    have hc : ¬ w.1.IsReal := not_isReal_iff_isComplex.2 w.2
    rw [GroundTheory.Global.posRealElem, dif_neg hc, mult, if_neg hc,
      ← Completion.ringEquivComplexOfIsComplex_apply (not_isReal_iff_isComplex.1 hc),
      RingEquiv.apply_symm_apply, Real.sqrt_sq hr.le]

variable (K n) in

def centralExp : ℝ := ((n * Module.finrank ℚ K : ℝ))⁻¹

theorem coe_zInf (s : {r : ℝ // 0 < r}) :
    (((zInf K n s : archGroup K n) : (ArchMatrix K n)ˣ) : ArchMatrix K n) =
      algebraMap ℝ (ArchMatrix K n) ((s : ℝ) ^ centralExp K n) := by
  refine Matrix.ext fun a b => ?_
  change InfiniteAdeleRing.ringEquiv_mixedSpace K
      ((((centralSection K n s : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) a b).1) = _
  rw [centralSection, MonoidHom.comp_apply, MonoidHom.comp_apply, scalarUnits_apply, coe_diagUnits]
  change _ = (Matrix.diagonal fun _ => algebraMap ℝ (mixedEmbedding.mixedSpace K)
    ((s : ℝ) ^ centralExp K n) : Matrix (Fin n) (Fin n) (mixedEmbedding.mixedSpace K)) a b
  by_cases hab : a = b
  · subst hab
    rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, posIdeleHom_apply]
    exact ringEquiv_posIdele _ _
  · rw [Matrix.diagonal_apply_ne _ hab, Matrix.diagonal_apply_ne _ hab]
    exact map_zero _

variable (K n) in

def centralZ : (isExpLieAlgebra K n).lieSubalgebra :=
  ⟨algebraMap ℝ (ArchMatrix K n) (centralExp K n), Submodule.mem_top⟩

theorem coe_centralZ :
    ((centralZ K n : (isExpLieAlgebra K n).lieSubalgebra) : ArchMatrix K n) =
      algebraMap ℝ (ArchMatrix K n) (centralExp K n) := rfl

theorem expG_centralZ (t : ℝ) :
    (isExpLieAlgebra K n).expG (t • (isExpLieAlgebra K n).ofLie (centralZ K n)) =
      zInf K n ⟨Real.exp t, Real.exp_pos t⟩ := by
  apply Subtype.ext
  apply Units.ext
  rw [IsExpLieAlgebra.coe_expG, coe_zInf]
  change NormedSpace.exp (t • algebraMap ℝ (ArchMatrix K n) (centralExp K n)) = _
  rw [Algebra.smul_def, ← map_mul, ← NormedSpace.algebraMap_exp_comm, ← Real.exp_eq_exp_ℝ]
  congr 1
  show Real.exp (t * centralExp K n) = Real.exp t ^ centralExp K n
  rw [Real.rpow_def_of_pos (Real.exp_pos t), Real.log_exp]

theorem lie_centralZ (X : (isExpLieAlgebra K n).lieSubalgebra) : ⁅centralZ K n, X⁆ = 0 := by
  apply Subtype.ext
  rw [LieSubalgebra.coe_bracket, Ring.lie_def, coe_centralZ, Algebra.commutes, sub_self]
  rfl

theorem Ad_centralZ (g : archGroup K n) :
    (isExpLieAlgebra K n).Ad g ((isExpLieAlgebra K n).ofLie (centralZ K n)) =
      (isExpLieAlgebra K n).ofLie (centralZ K n) := by
  apply Subtype.ext
  rw [IsExpLieAlgebra.coe_Ad, IsExpLieAlgebra.coe_ofLie, coe_centralZ, ← Algebra.commutes,
    mul_assoc, ← Units.val_mul]
  simp

theorem apply_mul_centralSection {φ : cuspForms K n} {c : ℂ}
    (hφ : lieActionCusp K n (centralZ K n) φ = c • φ) (g : AdelicGLn.AdelicGL K n)
    (s : {r : ℝ // 0 < r}) :
    (φ : AdelicGLn.AdelicGL K n → ℂ) (g * centralSection K n s) =
      Complex.exp (c * Real.log s) * (φ : AdelicGLn.AdelicGL K n → ℂ) g := by
  set X := (isExpLieAlgebra K n).ofLie (centralZ K n) with hX
  set f : ℝ → ℂ := fun t =>
    (φ : AdelicGLn.AdelicGL K n → ℂ) (g * infEmb K n ((isExpLieAlgebra K n).expG (t • X))) with hf
  have hsm : IsArchSmooth (φ : AdelicGLn.AdelicGL K n → ℂ) := φ.2.1.isSmooth.1
  have hder : ∀ t, HasDerivAt f (c * f t) t := by
    intro t
    set g' := g * infEmb K n ((isExpLieAlgebra K n).expG (t • X)) with hg'
    have h1 := (isExpLieAlgebra K n).hasDerivAt_rightDeriv (hsm g') X 1
    have hval : (isExpLieAlgebra K n).rightDeriv X (archSlice (φ : AdelicGLn.AdelicGL K n → ℂ) g') 1 =
        c * f t := by
      have e1 := uAction_ι_apply (centralZ K n) ⟨φ, hsm⟩ g'
      have e2 := congrArg (fun ψ : cuspForms K n => (ψ : AdelicGLn.AdelicGL K n → ℂ) g') hφ
      exact e1.symm.trans e2
    rw [hval] at h1
    have h2 : (fun u : ℝ => archSlice (φ : AdelicGLn.AdelicGL K n → ℂ) g'
        (1 * (isExpLieAlgebra K n).expG (u • X))) = fun u => f (t + u) := by
      funext u
      simp only [archSlice_apply, one_mul, hf, hg', mul_assoc, ← map_mul,
        ← (isExpLieAlgebra K n).expG_add_smul]
    rw [h2] at h1
    have h1' : HasDerivAt (fun u => f (t + u)) (c * f t) (t - t) := by rw [sub_self]; exact h1
    have h3 := h1'.comp_sub_const t t
    have e : (fun x => f (t + (x - t))) = f := by
      funext x
      simp only [add_sub_cancel]
    rw [e] at h3
    exact h3

  set F : ℝ → ℂ := fun t => Complex.exp (-(c * t)) * f t with hF
  have hFd : ∀ t, HasDerivAt F 0 t := by
    intro t
    have he : HasDerivAt (fun x : ℝ => Complex.exp (-(c * x))) (Complex.exp (-(c * t)) * (-c)) t := by
      have hl : HasDerivAt (fun x : ℝ => -(c * (x : ℂ))) (-c) t := by
        have := ((hasDerivAt_id t).ofReal_comp).const_mul (-c)
        have e1 : (fun y : ℝ => -c * ((id y : ℝ) : ℂ)) = fun x : ℝ => -(c * (x : ℂ)) := by
          funext y
          simp
        have e2 : -c * ((1 : ℝ) : ℂ) = -c := by simp
        rw [e1, e2] at this
        exact this
      exact hl.cexp
    have := he.mul (hder t)
    have e : Complex.exp (-(c * t)) * (-c) * f t + Complex.exp (-(c * t)) * (c * f t) = 0 := by ring
    rw [e] at this
    exact this
  have hconst : F (Real.log s) = F 0 :=
    is_const_of_deriv_eq_zero (fun t => (hFd t).differentiableAt)
      (fun t => (hFd t).deriv) _ _
  have hf0 : f 0 = (φ : AdelicGLn.AdelicGL K n → ℂ) g := by
    simp [hf]
  have hfs : f (Real.log s) = (φ : AdelicGLn.AdelicGL K n → ℂ) (g * centralSection K n s) := by
    simp only [hf]
    rw [expG_centralZ, infEmb_zInf]
    have : (⟨Real.exp (Real.log s), Real.exp_pos _⟩ : {r : ℝ // 0 < r}) = s :=
      Subtype.ext (Real.exp_log s.2)
    rw [this]
  simp only [hF, hf0, Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero, one_mul] at hconst
  rw [← hfs, ← hconst, ← mul_assoc, ← Complex.exp_add]
  simp

theorem eq_zero_of_cuspFormLp_eq_zero (μ : MeasureTheory.Measure (normOneGL K n)) [μ.IsHaarMeasure]
    {φ : cuspForms K n} {c : ℂ} (hφ : lieActionCusp K n (centralZ K n) φ = c • φ)
    (h0 : cuspToL2 μ φ = 0) : φ = 0 := by
  rw [cuspToL2_eq_zero_iff] at h0
  refine Subtype.ext (funext fun x => ?_)
  obtain ⟨s, y, hy, rfl⟩ := exists_centralSection_mul_mem_normOneGL x
  rw [centralSection_mul_comm, apply_mul_centralSection hφ, h0 y hy, mul_zero]
  rfl

end UnitaryAdmissible

end GroundTheory.Automorphic
