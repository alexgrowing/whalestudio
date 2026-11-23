import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinIso
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecProdRecSatakeLL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Formalism.SharpRestriction.LevelLetterCocycles.SphericalInertData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueWeightDefiniteUnitaryAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightEqOfFinitePartNeBot
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolyRep
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolynomialRepGLComplexAlgebraicWeightEvalPointStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArchimedeanUnitaryPointsEquivUnitaryGroupStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped Matrix

noncomputable section

namespace GlobalTheory.AlgWtHW

theorem eval_adjugate_mvPolynomialX {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) (x y : Fin n) :
    MvPolynomial.eval (fun p : Fin n × Fin n => g p.1 p.2)
      ((Matrix.mvPolynomialX (Fin n) (Fin n) ℂ).adjugate x y) = g.adjugate x y := by
  have h := RingHom.map_adjugate (MvPolynomial.eval (fun p : Fin n × Fin n => g p.1 p.2))
    (Matrix.mvPolynomialX (Fin n) (Fin n) ℂ)
  have h2 : (MvPolynomial.eval (fun p : Fin n × Fin n => g p.1 p.2)).mapMatrix
      (Matrix.mvPolynomialX (Fin n) (Fin n) ℂ) = g := by
    ext i j; simp [Matrix.mvPolynomialX]
  rw [h2] at h
  simpa using congrFun (congrFun h x) y

theorem eval_det_mvPolynomialX {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) :
    MvPolynomial.eval (fun p : Fin n × Fin n => g p.1 p.2) (Matrix.mvPolynomialX (Fin n) (Fin n) ℂ).det = g.det := by
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp [Matrix.mvPolynomialX]

theorem det_mul_inv_apply {n : ℕ} (B : GL (Fin n) ℂ) (x y : Fin n) :
    B.val.det * (B⁻¹).val x y = B.val.adjugate x y := by
  have h : B.val.adjugate = B.val.det • (B⁻¹).val := by
    calc B.val.adjugate = B.val.adjugate * (B.val * (B⁻¹).val) := by rw [Units.mul_inv, Matrix.mul_one]
      _ = (B.val.adjugate * B.val) * (B⁻¹).val := by rw [Matrix.mul_assoc]
      _ = _ := by rw [Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul]
  rw [h, Matrix.smul_apply, smul_eq_mul]

theorem exists_det_pow_mul_eq_poly {n : ℕ} (Q : MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) ℂ) :
    ∃ (d : ℕ) (P : MvPolynomial (Fin n × Fin n) ℂ), ∀ B : GL (Fin n) ℂ,
      B.val.det ^ d * MvPolynomial.eval (Sum.elim (fun p => B.val p.1 p.2) (fun p => (B⁻¹).val p.1 p.2)) Q =
        MvPolynomial.eval (fun p => B.val p.1 p.2) P := by
  induction Q using MvPolynomial.induction_on with
  | C a => exact ⟨0, MvPolynomial.C a, fun B => by simp⟩
  | add p q hp hq =>
    obtain ⟨d₁, P₁, h₁⟩ := hp
    obtain ⟨d₂, P₂, h₂⟩ := hq
    refine ⟨d₁ + d₂, P₁ * (Matrix.mvPolynomialX (Fin n) (Fin n) ℂ).det ^ d₂ +
      P₂ * (Matrix.mvPolynomialX (Fin n) (Fin n) ℂ).det ^ d₁, fun B => ?_⟩
    simp only [map_add, map_mul, map_pow, eval_det_mvPolynomialX, ← h₁ B, ← h₂ B]
    ring
  | mul_X p v hp =>
    obtain ⟨d, P, h⟩ := hp
    cases v with
    | inl x =>
      refine ⟨d, P * MvPolynomial.X x, fun B => ?_⟩
      simp only [map_mul, MvPolynomial.eval_X, Sum.elim_inl, ← h B]
      ring
    | inr x =>
      refine ⟨d + 1, P * (Matrix.mvPolynomialX (Fin n) (Fin n) ℂ).adjugate x.1 x.2, fun B => ?_⟩
      simp only [map_mul, MvPolynomial.eval_X, Sum.elim_inr, eval_adjugate_mvPolynomialX, ← h B,
        ← det_mul_inv_apply]
      ring

theorem sqRep_intertwines_of_unitary : ∀ (n : ℕ) (lam : DomWeight n) (ι : Type) [Fintype ι] [DecidableEq ι] (Φ : GL (Fin n) ℂ → Matrix ι ι ℂ), GlobalTheory.AlgWtHW.IsPolyRep Φ → ∀ M : nablaSq ℂ n lam →ₗ[ℂ] (ι → ℂ), (∀ (u : Matrix.unitaryGroup (Fin n) ℂ) (v : nablaSq ℂ n lam), M (GlobalTheory.Branching.sqRep ℂ n lam (GlobalTheory.Branching.unitaryIncl n u) v) = Matrix.mulVec (Φ (GlobalTheory.Branching.unitaryIncl n u)) (M v)) → ∀ (B : GL (Fin n) ℂ) (v : nablaSq ℂ n lam), M (GlobalTheory.Branching.sqRep ℂ n lam B v) = Matrix.mulVec (Φ B) (M v) := by
  classical
  intro n lam ι _ _ Φ hΦ M hU B v
  funext k
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (nablaSq ℂ n lam)
  let π := (nablaSq ℂ n lam).linearProjOfIsCompl C hC
  let l : Module.Dual ℂ (MvPolynomial (Fin n × Fin n) ℂ) := LinearMap.proj k ∘ₗ M ∘ₗ π
  have hl : ∀ B' : GL (Fin n) ℂ, M (GlobalTheory.Branching.sqRep ℂ n lam B' v) k =
      detPow ℂ n B' lam.detShift * l (Formalism.GradedWeylDivisibility.rowAct ℂ (B'.val)ᵀ v.1) := by
    intro B'
    calc M (GlobalTheory.Branching.sqRep ℂ n lam B' v) k = l (sqAct ℂ n lam B' v.1) := by
          simp only [l, π, LinearMap.comp_apply, LinearMap.proj_apply]
          have := Submodule.linearProjOfIsCompl_apply_left hC (GlobalTheory.Branching.sqRep ℂ n lam B' v)
          rw [← GlobalTheory.Branching.sqRep_coe]
          exact (congrArg (fun w => M w k) this).symm
      _ = _ := by rw [sqAct, map_smul, smul_eq_mul]
  obtain ⟨P₁, hP₁⟩ := GlobalTheory.Branching.exists_poly_rowAct_coef n n v.1 l
  let R₁ := MvPolynomial.rename Prod.swap P₁
  have hR₁ : ∀ g : Matrix (Fin n) (Fin n) ℂ,
      MvPolynomial.eval (fun x => g x.1 x.2) R₁ = l (Formalism.GradedWeylDivisibility.rowAct ℂ gᵀ v.1) := by
    intro g
    rw [hP₁, MvPolynomial.eval_rename]
    rfl
  choose Q hQ using hΦ.poly
  let Qs := ∑ j, Q k j * MvPolynomial.C ((M v) j)
  have hQs : ∀ B' : GL (Fin n) ℂ,
      MvPolynomial.eval (Sum.elim (fun p => B'.val p.1 p.2) (fun p => (B'⁻¹).val p.1 p.2)) Qs = (Φ B' *ᵥ M v) k := by
    intro B'
    simp only [Qs, map_sum, map_mul, MvPolynomial.eval_C, ← hQ, Matrix.mulVec, dotProduct]
  obtain ⟨d, P₂, hP₂⟩ := exists_det_pow_mul_eq_poly Qs
  set a := lam.detShift
  set m : ℕ := a.natAbs
  have ha : 0 ≤ a + (m : ℤ) := by omega
  have hdet : ∀ B' : GL (Fin n) ℂ, B'.val.det ≠ 0 := fun B' => (Matrix.isUnits_det_units B').ne_zero
  have hdp : ∀ B' : GL (Fin n) ℂ, detPow ℂ n B' a = B'.val.det ^ a := by
    intro B'
    simp [detPow, Units.val_zpow_eq_zpow_val]
  have key : ∀ B' : GL (Fin n) ℂ,
      B'.val.det ^ d * B'.val.det ^ (a + (m : ℤ)).toNat * l (Formalism.GradedWeylDivisibility.rowAct ℂ (B'.val)ᵀ v.1) -
        B'.val.det ^ m * MvPolynomial.eval (fun p => B'.val p.1 p.2) P₂ =
      B'.val.det ^ d * B'.val.det ^ m * (M (GlobalTheory.Branching.sqRep ℂ n lam B' v) k - (Φ B' *ᵥ M v) k) := by
    intro B'
    have hx := hdet B'
    rw [hl, ← hQs, ← hP₂, hdp]
    have e1 : B'.val.det ^ (a + (m : ℤ)).toNat = B'.val.det ^ m * B'.val.det ^ a := by
      rw [← zpow_natCast (B'.val.det) (a + (m : ℤ)).toNat, Int.toNat_of_nonneg ha, zpow_add₀ hx, zpow_natCast]
      ring
    rw [e1]
    ring
  let Dp := (Matrix.mvPolynomialX (Fin n) (Fin n) ℂ).det
  let Qd := Dp ^ d * Dp ^ (a + (m : ℤ)).toNat * R₁ - Dp ^ m * P₂
  have hQd : ∀ g : Matrix (Fin n) (Fin n) ℂ, MvPolynomial.eval (fun x => g x.1 x.2) Qd =
      g.det ^ d * g.det ^ (a + (m : ℤ)).toNat * l (Formalism.GradedWeylDivisibility.rowAct ℂ gᵀ v.1) -
        g.det ^ m * MvPolynomial.eval (fun p => g p.1 p.2) P₂ := by
    intro g
    simp only [Qd, Dp, map_sub, map_mul, map_pow, eval_det_mvPolynomialX, hR₁]
  have Q0 : Qd = 0 := by
    refine GlobalTheory.Branching.eq_zero_of_vanish_unitaryGroup n Qd fun u hu => ?_
    have h1 := key (GlobalTheory.Branching.unitaryIncl n ⟨u, hu⟩)
    have h2 := congrFun (hU ⟨u, hu⟩ v) k
    rw [h2, sub_self, mul_zero] at h1
    rw [hQd]
    exact h1
  have h3 := key B
  rw [← hQd, Q0, map_zero] at h3
  have hx := hdet B
  have h4 : B.val.det ^ d * B.val.det ^ m ≠ 0 := mul_ne_zero (pow_ne_zero _ hx) (pow_ne_zero _ hx)
  exact sub_eq_zero.1 ((mul_eq_zero.1 h3.symm).resolve_left h4)

end GlobalTheory.AlgWtHW
