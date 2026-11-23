import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsProjChowNonzero
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PIncidenceZeroLocus
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace ProjChowNonzero

theorem aeval_smul_of_isHomogeneous {Ω : Type*} [Field Ω] [Algebra ℂ Ω] {n m : ℕ}
    {φ : MvPolynomial (Fin n) ℂ} (hφ : φ.IsHomogeneous m) (c : Ω) (x : Fin n → Ω) :
    aeval (c • x) φ = c ^ m * aeval x φ := by
  simp only [aeval_def, eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg := hφ.degree_eq_sum_deg_support hd
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [← hdeg]
  ring

theorem aeval_smul_eq_zero {Ω : Type*} [Field Ω] [Algebra ℂ Ω] {n : ℕ}
    {W : Ideal (MvPolynomial (Fin n) ℂ)} (hW : IsHomogIdeal W) {x : Fin n → Ω}
    (hx : ∀ q ∈ W, aeval x q = 0) (c : Ω) : ∀ q ∈ W, aeval (c • x) q = 0 := by
  intro q hq
  rw [← sum_homogeneousComponent q, map_sum]
  refine Finset.sum_eq_zero fun d _ => ?_
  rw [aeval_smul_of_isHomogeneous (homogeneousComponent_isHomogeneous d q), hx _ (hW q hq d), mul_zero]

theorem eq_zero_of_isFiniteProjection {Ω : Type*} [Field Ω] [IsAlgClosed Ω] [Algebra ℂ Ω] {n d : ℕ}
    {W : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ} (hW : IsHomogIdeal W)
    (hA : ComplexSets.IsFiniteProjection W A) {x : Fin n → Ω} (hx : ∀ q ∈ W, aeval x q = 0)
    (hAx : ∀ i, aeval x (ComplexSets.linPoly A i) = 0) : x = 0 := by
  funext j
  by_contra hj
  obtain ⟨p, hpm, hp⟩ := hA.finite.to_isIntegral (Ideal.Quotient.mk W (X j))
  set q := Polynomial.eval₂ (ComplexSets.pullback A).toRingHom (X j) p with hq_def
  have hq : q ∈ W := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, hq_def, Polynomial.hom_eval₂]
    exact hp

  set ψ : MvPolynomial (Fin d) ℂ →+* Ω := (algebraMap ℂ Ω).comp (eval 0) with hψ
  have hcomp : ∀ c : Ω, ((aeval (c • x) : MvPolynomial (Fin n) ℂ →ₐ[ℂ] Ω) : MvPolynomial (Fin n) ℂ →+* Ω).comp
      (ComplexSets.pullback A).toRingHom = ψ := by
    intro c
    refine MvPolynomial.ringHom_ext (fun a => by simp [hψ, ComplexSets.pullback]) fun i => ?_
    have h1 := aeval_smul_of_isHomogeneous (Ω := Ω) (m := 1) ?_ c x (φ := ComplexSets.linPoly A i)
    · simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
        ComplexSets.pullback, aeval_X, hψ, eval_X, Pi.zero_apply, map_zero]
      rw [h1, hAx i, mul_zero]
    · exact IsHomogeneous.sum _ _ _ fun j _ => (isHomogeneous_C_mul_X _ _)
  have hroot : ∀ c : Ω, (p.map ψ).eval (c * x j) = 0 := by
    intro c
    have h := aeval_smul_eq_zero hW hx c q hq
    rw [hq_def, ← AlgHom.coe_toRingHom, Polynomial.hom_eval₂, hcomp c] at h
    simpa [Polynomial.eval_map] using h
  have hzero : p.map ψ = 0 := Polynomial.funext fun r => by
    have := hroot (r / x j)
    rw [div_mul_cancel₀ r hj] at this
    simpa using this
  exact (hpm.map ψ).ne_zero hzero

theorem aeval_ne_zero_of_not_incidence {n k : ℕ} {W : Ideal (MvPolynomial (Fin n) ℂ)}
    {f : MvPolynomial (Fin k × Fin n) ℂ} (hW : IsHomogIdeal W) (hf : IsChowForm W k f)
    (v : Fin k × Fin n → AlgebraicClosure ℂ)
    (hv : ∀ y : Fin n → AlgebraicClosure ℂ, (∀ q ∈ W, aeval y q = 0) →
      (∀ i, ∑ j, v (i, j) * y j = 0) → y = 0) :
    aeval v f ≠ 0 := by
  intro h0
  have hinc : ∀ g ∈ incIdeal W k, aeval v g = 0 := by
    intro g hg
    have hmem : ∀ u ∈ incidence W k, aeval u g = 0 := by
      simpa only [incIdeal, Submodule.mem_iInf, RingHom.mem_ker] using hg
    obtain ⟨h, rfl⟩ := (hf.2 g).mp hmem
    rw [map_mul, h0, zero_mul]
  obtain ⟨y, hy0, hyW, hyv⟩ := IncidenceZeroLocus.proof ℂ n k W hW (AlgebraicClosure ℂ) v hinc
  exact hy0 (hv y hyW hyv)

abbrev Loc (e : ℕ) : Type := Localization.Away (X 0 : MvPolynomial (Fin (e + 1)) ℂ)

theorem projVar_zero_ne (e : ℕ) : projVar e 0 ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective (MvPolynomial (Fin (e + 1)) ℂ) _)).mpr (X_ne_zero 0)

def toK (e : ℕ) : Loc e →+* FractionRing (MvPolynomial (Fin (e + 1)) ℂ) :=
  IsLocalization.Away.lift (X 0) (g := algebraMap _ _) (IsUnit.mk0 _ (projVar_zero_ne e))

def pt (e : ℕ) : Fin (e + 1) → ℂ := fun i => if i = 0 then 1 else 0

def atPt (e : ℕ) : Loc e →+* AlgebraicClosure ℂ :=
  IsLocalization.Away.lift (X 0) (g := (algebraMap ℂ (AlgebraicClosure ℂ)).comp (eval (pt e)))
    (by simp [pt])

def locPar {n e : ℕ} (A : Matrix (Fin (e + 1)) (Fin n) ℂ) (ij : Fin (e + 1) × Fin n) : Loc e :=
  Fin.cases (motive := fun _ => Loc e)
    (algebraMap ℂ (Loc e) (A 0 ij.2) * IsLocalization.Away.invSelf (X 0 : MvPolynomial (Fin (e + 1)) ℂ))
    (fun i => algebraMap (MvPolynomial (Fin (e + 1)) ℂ) (Loc e)
      (X i.succ * C (A 0 ij.2) - X 0 * C (A i.succ ij.2))) ij.1

theorem toK_injective (e : ℕ) : Function.Injective (toK e) := by
  have h1 : Function.Injective (algebraMap (MvPolynomial (Fin (e + 1)) ℂ) (Loc e)) :=
    IsLocalization.injective (Loc e) (powers_le_nonZeroDivisors_of_noZeroDivisors (X_ne_zero 0))
  have h2 := IsFractionRing.injective (MvPolynomial (Fin (e + 1)) ℂ)
    (FractionRing (MvPolynomial (Fin (e + 1)) ℂ))
  exact (IsLocalization.lift_injective_iff _).mpr fun a b => h1.eq_iff.trans h2.eq_iff.symm

theorem toK_invSelf (e : ℕ) :
    toK e (IsLocalization.Away.invSelf (X 0 : MvPolynomial (Fin (e + 1)) ℂ)) = (projVar e 0)⁻¹ := by
  have h := congrArg (toK e) (IsLocalization.Away.mul_invSelf (S := Loc e) (X 0 : MvPolynomial (Fin (e + 1)) ℂ))
  rw [map_mul, map_one, toK, IsLocalization.Away.lift_eq] at h
  exact (eq_inv_of_mul_eq_one_right h)

theorem atPt_invSelf (e : ℕ) :
    atPt e (IsLocalization.Away.invSelf (X 0 : MvPolynomial (Fin (e + 1)) ℂ)) = 1 := by
  have h := congrArg (atPt e) (IsLocalization.Away.mul_invSelf (S := Loc e) (X 0 : MvPolynomial (Fin (e + 1)) ℂ))
  rw [map_mul, map_one] at h
  unfold atPt at h ⊢
  rw [IsLocalization.Away.lift_eq] at h
  simpa [pt] using h

theorem toK_algebraMap (e : ℕ) (a : ℂ) :
    toK e (algebraMap ℂ (Loc e) a) = algebraMap ℂ (FractionRing (MvPolynomial (Fin (e + 1)) ℂ)) a := by
  rw [IsScalarTower.algebraMap_apply ℂ (MvPolynomial (Fin (e + 1)) ℂ) (Loc e), toK,
    IsLocalization.Away.lift_eq, ← IsScalarTower.algebraMap_apply]

theorem atPt_algebraMap (e : ℕ) (a : ℂ) :
    atPt e (algebraMap ℂ (Loc e) a) = algebraMap ℂ (AlgebraicClosure ℂ) a := by
  rw [IsScalarTower.algebraMap_apply ℂ (MvPolynomial (Fin (e + 1)) ℂ) (Loc e), atPt,
    IsLocalization.Away.lift_eq]
  simp

theorem value_eq {n e : ℕ} (A : Matrix (Fin (e + 1)) (Fin n) ℂ) (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ) :
    eval (fun j => projPar A (.inr j))
        (Vertical.specRest (algebraMap ℂ (FractionRing (MvPolynomial (Fin (e + 1)) ℂ))) f (projPar A)) =
      toK e (aeval (locPar A) f) := by
  rw [Vertical.specRest, eval₂_comp_left, aeval_def, eval₂_comp_left]
  congr 1
  · ext a
    simp [toK_algebraMap]
  · funext ⟨i, j⟩
    cases i using Fin.cases with
    | zero => simp [locPar, projPar, map_mul, toK_algebraMap, toK_invSelf, div_eq_mul_inv]
    | succ i =>
      simp [locPar, projPar, toK, IsLocalization.Away.lift_eq, projVar,
        IsScalarTower.algebraMap_apply ℂ (MvPolynomial (Fin (e + 1)) ℂ)
          (FractionRing (MvPolynomial (Fin (e + 1)) ℂ)), mul_comm]

theorem atPt_aeval {n e : ℕ} (A : Matrix (Fin (e + 1)) (Fin n) ℂ) (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ) :
    atPt e (aeval (locPar A) f) =
      aeval (fun ij : Fin (e + 1) × Fin n => Fin.cases (motive := fun _ => AlgebraicClosure ℂ)
        (algebraMap ℂ _ (A 0 ij.2)) (fun i => -algebraMap ℂ _ (A i.succ ij.2)) ij.1) f := by
  rw [aeval_def, eval₂_comp_left, aeval_def]
  congr 1
  · ext a
    simp [atPt_algebraMap]
  · funext ⟨i, j⟩
    cases i using Fin.cases with
    | zero => simp [locPar, atPt_algebraMap, atPt_invSelf]
    | succ i => simp [locPar, atPt, IsLocalization.Away.lift_eq, pt, Fin.succ_ne_zero]

end ProjChowNonzero

theorem ProjChowNonzero.proof : ProjChowNonzero.Statement := by
  intro n e W f A hW hf hA
  rw [ProjChowNonzero.value_eq]
  intro h0
  have h1 : aeval (ProjChowNonzero.locPar A) f = 0 :=
    (map_eq_zero_iff _ (ProjChowNonzero.toK_injective e)).mp h0
  have h2 := congrArg (ProjChowNonzero.atPt e) h1
  rw [map_zero, ProjChowNonzero.atPt_aeval] at h2
  refine ProjChowNonzero.aeval_ne_zero_of_not_incidence hW.isHomog hf _ (fun y hyW hyv => ?_) h2
  refine ProjChowNonzero.eq_zero_of_isFiniteProjection hW.isHomog hA hyW fun i => ?_
  have hi := hyv i
  cases i using Fin.cases with
  | zero => simpa [ComplexSets.linPoly] using hi
  | succ i =>
    simp only [Fin.cases_succ, neg_mul, Finset.sum_neg_distrib, neg_eq_zero] at hi
    simpa [ComplexSets.linPoly] using hi

end

end GroundTheory.Heights₂.Heights
