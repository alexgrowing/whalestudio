import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.SectionNormSquares.ExistsFormOfMemChartRingZ
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open scoped Topology

noncomputable section

set_option linter.unusedSectionVars false

namespace SectionNormSqExtension

section Poly

variable {J : Type} [Fintype J]

theorem hasFDerivAt_eval (P : MvPolynomial J ℂ) (x : J → ℂ) :
    HasFDerivAt (fun y => eval y P)
      (∑ q, eval x (pderiv q P) • ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : J => ℂ) q) x := by
  classical
  induction P using MvPolynomial.induction_on with
  | C a =>
    have e : (fun y : J → ℂ => eval y (C a)) = fun _ => a := by funext y; simp
    rw [e]
    refine (hasFDerivAt_const (𝕜 := ℂ) a x).congr_fderiv (ContinuousLinearMap.ext fun w => ?_)
    simp
  | add p q hp hq =>
    have e : (fun y : J → ℂ => eval y (p + q)) = fun y => eval y p + eval y q := by funext y; simp
    rw [e]
    refine (hp.add hq).congr_fderiv (ContinuousLinearMap.ext fun w => ?_)
    simp [add_mul, Finset.sum_add_distrib]
  | mul_X p q0 hp =>
    have hX : HasFDerivAt (fun y : J → ℂ => y q0) (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : J => ℂ) q0) x :=
      hasFDerivAt_apply q0 x
    have key : ∀ q, eval x (pderiv q (p * X q0)) =
        eval x (pderiv q p) * x q0 + if q = q0 then eval x p else 0 := by
      intro q
      rw [Derivation.leibniz, pderiv_X]
      by_cases hq : q = q0
      · subst hq
        simp only [Pi.single_eq_same, smul_eq_mul, map_add, map_mul, eval_X, map_one, if_true]
        ring
      · rw [Pi.single_eq_of_ne' hq]
        simp only [smul_eq_mul, map_add, map_mul, eval_X, map_zero, if_neg hq]
        ring
    have e : (fun y : J → ℂ => eval y (p * X q0)) = fun y => eval y p * y q0 := by funext y; simp
    rw [e]
    refine (hp.mul hX).congr_fderiv (ContinuousLinearMap.ext fun w => ?_)
    have lhs : (∑ q, eval x (pderiv q (p * X q0)) • ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : J => ℂ) q) w =
        ∑ q, eval x (pderiv q (p * X q0)) * w q := by simp
    rw [lhs]
    simp only [key, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
      if_true]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
      ContinuousLinearMap.proj_apply]
    have hs : (∑ q, eval x (pderiv q p) • ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : J => ℂ) q) w =
        ∑ q, eval x (pderiv q p) * w q := by simp
    rw [hs, Finset.mul_sum]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun q _ => ?_
    ring

theorem fderiv_eval_apply (P : MvPolynomial J ℂ) (x w : J → ℂ) :
    fderiv ℂ (fun y => eval y P) x w = ∑ q, eval x (pderiv q P) * w q := by
  rw [(hasFDerivAt_eval P x).fderiv]
  simp

theorem analyticAt_eval (P : MvPolynomial J ℂ) (z : J → ℂ) : AnalyticAt ℂ (fun y => eval y P) z := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    simp only [eval_C]
    exact analyticAt_const
  | add p q hp hq =>
    simp only [map_add]
    exact hp.add hq
  | mul_X p v hp =>
    simp only [map_mul, eval_X]
    exact hp.mul ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : J => ℂ) v).analyticAt z)

theorem fderiv_eq_zero_of_tangent {I : Ideal (MvPolynomial J ℤ)} {z w : J → ℂ}
    (h : IsConeTangent (Int.castRingHom ℂ) I z w) {f : MvPolynomial J ℤ} (hf : f ∈ I) :
    fderiv ℂ (fun y => eval y (map (Int.castRingHom ℂ) f)) z w = 0 := by
  rw [fderiv_eval_apply]
  exact h f hf

theorem contDiff_normSq_eval (P : MvPolynomial J ℂ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun y : J → ℂ => ‖eval y P‖ ^ 2) := by
  refine contDiff_iff_contDiffAt.mpr fun z => ?_
  exact (contDiff_norm_sq ℝ).contDiffAt.comp z ((analyticAt_eval P z).contDiffAt.restrict_scalars ℝ)

end Poly

section Levi

variable {J : Type} [Fintype J]

theorem leviForm_congr {φ ψ : (J → ℂ) → ℝ} {z : J → ℂ} (h : φ =ᶠ[𝓝 z] ψ) (w : J → ℂ) :
    leviForm φ z w = leviForm ψ z w := by
  have h1 : fderiv ℝ φ =ᶠ[𝓝 z] fderiv ℝ ψ := by
    filter_upwards [h.eventuallyEq_nhds] with y hy
    exact hy.fderiv_eq
  unfold leviForm
  rw [h1.fderiv_eq]

theorem eventually_differentiableAt {f : (J → ℂ) → ℝ} {z : J → ℂ} (hf : ContDiffAt ℝ 2 f z) :
    ∀ᶠ y in 𝓝 z, DifferentiableAt ℝ f y :=
  (hf.eventually (by simp)).mono fun _ hy => hy.differentiableAt (by norm_num)

theorem differentiableAt_fderiv {f : (J → ℂ) → ℝ} {z : J → ℂ} (hf : ContDiffAt ℝ 2 f z) :
    DifferentiableAt ℝ (fderiv ℝ f) z :=
  (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)

theorem leviForm_add {f g : (J → ℂ) → ℝ} {z : J → ℂ} (hf : ContDiffAt ℝ 2 f z) (hg : ContDiffAt ℝ 2 g z)
    (w : J → ℂ) : leviForm (fun x => f x + g x) z w = leviForm f z w + leviForm g z w := by
  have hfd : fderiv ℝ (fun x => f x + g x) =ᶠ[𝓝 z] fun y => fderiv ℝ f y + fderiv ℝ g y := by
    filter_upwards [eventually_differentiableAt hf, eventually_differentiableAt hg] with y h1 h2
    exact fderiv_fun_add h1 h2
  unfold leviForm
  rw [hfd.fderiv_eq, fderiv_fun_add (differentiableAt_fderiv hf) (differentiableAt_fderiv hg)]
  simp only [ContinuousLinearMap.add_apply]
  ring

theorem leviForm_sub {f g : (J → ℂ) → ℝ} {z : J → ℂ} (hf : ContDiffAt ℝ 2 f z) (hg : ContDiffAt ℝ 2 g z)
    (w : J → ℂ) : leviForm (fun x => f x - g x) z w = leviForm f z w - leviForm g z w := by
  have hfd : fderiv ℝ (fun x => f x - g x) =ᶠ[𝓝 z] fun y => fderiv ℝ f y - fderiv ℝ g y := by
    filter_upwards [eventually_differentiableAt hf, eventually_differentiableAt hg] with y h1 h2
    exact fderiv_fun_sub h1 h2
  unfold leviForm
  rw [hfd.fderiv_eq, fderiv_fun_sub (differentiableAt_fderiv hf) (differentiableAt_fderiv hg)]
  simp only [ContinuousLinearMap.sub_apply]
  ring

theorem leviForm_const_mul {f : (J → ℂ) → ℝ} {z : J → ℂ} (hf : ContDiffAt ℝ 2 f z) (c : ℝ) (w : J → ℂ) :
    leviForm (fun x => c * f x) z w = c * leviForm f z w := by
  have hfd : fderiv ℝ (fun x => c * f x) =ᶠ[𝓝 z] fun y => c • fderiv ℝ f y := by
    filter_upwards [eventually_differentiableAt hf] with y h1
    exact fderiv_const_mul h1 c
  unfold leviForm
  rw [hfd.fderiv_eq, fderiv_fun_const_smul (differentiableAt_fderiv hf) c]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

def IsFlat (u : (J → ℂ) → ℝ) (z w : J → ℂ) : Prop :=
  ContDiffAt ℝ 2 u z ∧ u z = 0 ∧ fderiv ℝ u z w = 0 ∧ fderiv ℝ u z (Complex.I • w) = 0 ∧ leviForm u z w = 0

theorem IsFlat.add {u v : (J → ℂ) → ℝ} {z w : J → ℂ} (hu : IsFlat u z w) (hv : IsFlat v z w) :
    IsFlat (fun x => u x + v x) z w := by
  obtain ⟨hu1, hu2, hu3, hu4, hu5⟩ := hu
  obtain ⟨hv1, hv2, hv3, hv4, hv5⟩ := hv
  have d1 := hu1.differentiableAt (by norm_num)
  have d2 := hv1.differentiableAt (by norm_num)
  refine ⟨hu1.add hv1, by simp [hu2, hv2], ?_, ?_, ?_⟩
  · rw [fderiv_fun_add d1 d2, ContinuousLinearMap.add_apply, hu3, hv3, add_zero]
  · rw [fderiv_fun_add d1 d2, ContinuousLinearMap.add_apply, hu4, hv4, add_zero]
  · rw [leviForm_add hu1 hv1, hu5, hv5, add_zero]

theorem isFlat_zero (z w : J → ℂ) : IsFlat (fun _ => (0 : ℝ)) z w :=
  ⟨contDiffAt_const, rfl, by simp, by simp, by simp [leviForm]⟩

theorem isFlat_sum {ι' : Type} (s : Finset ι') {u : ι' → (J → ℂ) → ℝ} {z w : J → ℂ}
    (h : ∀ i ∈ s, IsFlat (u i) z w) : IsFlat (fun x => ∑ i ∈ s, u i x) z w := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isFlat_zero z w
  | insert a s ha ih =>
    have := (h a (Finset.mem_insert_self a s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
    simpa [Finset.sum_insert ha] using this

end Levi

section Graph

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

variable (ι) in

def oldEmb (N : ℕ) (p : Σ k, ι k) : Σ k, addIdx ι N k := ⟨some p.1, p.2⟩

variable (ι) in

def oldL (N : ℕ) : ((Σ k, addIdx ι N k) → ℂ) →L[ℂ] ((Σ k, ι k) → ℂ) :=
  ContinuousLinearMap.pi fun p => ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : (Σ k, addIdx ι N k) => ℂ)
    (oldEmb ι N p)

variable (ι) in

def newL (N : ℕ) : ((Σ k, addIdx ι N k) → ℂ) →L[ℂ] (Fin N → ℂ) :=
  ContinuousLinearMap.pi fun j => ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : (Σ k, addIdx ι N k) => ℂ)
    (⟨none, j⟩ : Σ k, addIdx ι N k)

theorem oldL_apply {N : ℕ} (z : (Σ k, addIdx ι N k) → ℂ) : oldL ι N z = basePart₂ z := rfl

theorem newL_apply {N : ℕ} (z : (Σ k, addIdx ι N k) → ℂ) (j : Fin N) : newL ι N z j = z ⟨none, j⟩ := rfl

theorem eval_rename_old {N : ℕ} (F : MRing ι) (z : (Σ k, addIdx ι N k) → ℂ) :
    eval z (map (Int.castRingHom ℂ) (rename (oldEmb ι N) F)) = eval (basePart₂ z) (map (Int.castRingHom ℂ) F) := by
  rw [map_rename, eval_rename]
  rfl

theorem mConeMap_rename_old (y : (Σ k, ι k) → Ω) {N : ℕ} (v : Fin N → Ω) (F : MRing ι) :
    mConeMap (addBlock y v) (rename (oldEmb ι N) F) = rename Option.some (mConeMap y F) := by
  induction F using MvPolynomial.induction_on with
  | C a => simp [mConeMap]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p q hp =>
    simp only [map_mul, hp]
    congr 1
    simp [mConeMap, oldEmb, addBlock]

theorem rename_mem {y : (Σ k, ι k) → Ω} {N : ℕ} (v : Fin N → Ω) {F : MRing ι} (hF : F ∈ mCoordIdeal y) :
    rename (oldEmb ι N) F ∈ mCoordIdeal (addBlock y v) := by
  show _ ∈ RingHom.ker (mConeMap (addBlock y v))
  have h : mConeMap y F = 0 := hF
  rw [RingHom.mem_ker, mConeMap_rename_old, h, map_zero]

theorem oldPart_mem {y : (Σ k, ι k) → Ω} {N : ℕ} {v : Fin N → Ω} {z : (Σ k, addIdx ι N k) → ℂ}
    (hz : z ∈ mcPts (mCoordIdeal (addBlock y v))) : basePart₂ z ∈ mcPts (mCoordIdeal y) := by
  refine ⟨fun k => hz.1 (some k), fun F hF => ?_⟩
  rw [← eval_rename_old]
  exact hz.2 _ (rename_mem v hF)

theorem fderiv_old_eq_zero {y : (Σ k, ι k) → Ω} {N : ℕ} {v : Fin N → Ω} {z w : (Σ k, addIdx ι N k) → ℂ}
    (hw : IsConeTangent (Int.castRingHom ℂ) (mCoordIdeal (addBlock y v)) z w) {F : MRing ι}
    (hF : F ∈ mCoordIdeal y) :
    fderiv ℂ (fun x => eval x (map (Int.castRingHom ℂ) F)) (basePart₂ z) (basePart₂ w) = 0 := by
  have h := fderiv_eq_zero_of_tangent hw (rename_mem v hF)
  have hc : (fun y' : (Σ k, addIdx ι N k) → ℂ => eval y' (map (Int.castRingHom ℂ) (rename (oldEmb ι N) F))) =
      (fun x => eval x (map (Int.castRingHom ℂ) F)) ∘ oldL ι N := by
    funext y'
    rw [eval_rename_old]
    rfl
  rw [hc, fderiv_comp z ((analyticAt_eval _ _).differentiableAt) (oldL ι N).differentiableAt,
    (oldL ι N).fderiv] at h
  exact h

theorem cross_mem {y : (Σ k, ι k) → Ω} {N : ℕ} {v : Fin N → Ω} {e : K → ℕ} {G G' : MRing ι}
    (hG : IsMultiHomog G e) (hG' : IsMultiHomog G' e) (j j' : Fin N)
    (hy : v j * aeval y G' = v j' * aeval y G) :
    X ⟨none, j⟩ * rename (oldEmb ι N) G' - X ⟨none, j'⟩ * rename (oldEmb ι N) G ∈ mCoordIdeal (addBlock y v) := by
  show _ ∈ RingHom.ker (mConeMap (addBlock y v))
  rw [RingHom.mem_ker, map_sub, map_mul, map_mul, mConeMap_rename_old, mConeMap_rename_old]
  erw [mConeMap_homog y hG, mConeMap_homog y hG']
  simp only [mConeMap, aeval_X, map_mul, rename_C]
  have h1 : addBlock y v ⟨none, j⟩ = v j := rfl
  have h2 : addBlock y v ⟨none, j'⟩ = v j' := rfl
  rw [h1, h2]
  have h3 : (MvPolynomial.C (v j) : MvPolynomial (Option K) Ω) * MvPolynomial.C (aeval y G') =
      MvPolynomial.C (v j') * MvPolynomial.C (aeval y G) := by
    rw [← map_mul, ← map_mul, hy]
  linear_combination (MvPolynomial.X none * rename Option.some (∏ k, (MvPolynomial.X k : MvPolynomial K Ω) ^ e k)) * h3

end Graph

end SectionNormSqExtension

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
