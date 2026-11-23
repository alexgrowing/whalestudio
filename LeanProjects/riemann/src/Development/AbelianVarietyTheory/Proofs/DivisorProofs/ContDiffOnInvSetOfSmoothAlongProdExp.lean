import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
open NumberField
open scoped ContDiff

namespace GlobalTheory.SecondKind

open GlobalTheory.CuspRep

variable {E : Type} [Field E] [NumberField E] {d : ℕ}

theorem prod_ofFn_eq_of_ne {M : Type*} [Monoid M] {k : ℕ} (f : Fin k → M) (i : Fin k)
    (h : ∀ j, j ≠ i → f j = 1) : (List.ofFn f).prod = f i := by
  induction k with
  | zero => exact i.elim0
  | succ k ih =>
    rw [List.ofFn_succ, List.prod_cons]
    cases i using Fin.cases with
    | zero =>
      rw [List.prod_eq_one, mul_one]
      intro x hx
      obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hx
      exact h _ (Fin.succ_ne_zero j)
    | succ i =>
      rw [h 0 (Fin.succ_ne_zero i).symm, one_mul]
      exact ih _ i fun j hj => h _ fun e => hj (Fin.succ_injective _ e)

theorem contDiff_prodExp (y : Lie E d) {k : ℕ} (X : Fin k → Matrix (Fin d) (Fin d) (Cinf E)) :
    ContDiff ℝ ∞ (fun t : Fin k → ℝ =>
      toL (Matrix.of y * (List.ofFn fun i => NormedSpace.exp (t i • X i)).prod)) := by
  letI : NormedRing (Matrix (Fin d) (Fin d) (Cinf E)) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (Fin d) (Fin d) (Cinf E)) := Matrix.linftyOpNormedAlgebra
  haveI : CompleteSpace (Matrix (Fin d) (Fin d) (Cinf E)) := FiniteDimensional.complete ℝ _
  let T : Matrix (Fin d) (Fin d) (Cinf E) →L[ℝ] Lie E d :=
    LinearMap.toContinuousLinearMap (LinearMap.id : Lie E d →ₗ[ℝ] Lie E d)
  have hexp : ContDiff ℝ ∞ (NormedSpace.exp : Matrix (Fin d) (Fin d) (Cinf E) → _) :=
    contDiff_iff_contDiffAt.2 fun x => (NormedSpace.exp_analytic (𝕂 := ℝ) x).contDiffAt
  have hprod : ∀ (n : ℕ) (g : Fin n → (Fin k → ℝ) → Matrix (Fin d) (Fin d) (Cinf E)),
      (∀ i, ContDiff ℝ ∞ (g i)) → ContDiff ℝ ∞ (fun t => (List.ofFn fun i => g i t).prod) := by
    intro n
    induction n with
    | zero => intro g _; simpa using contDiff_const
    | succ n ih =>
      intro g hg
      simp only [List.ofFn_succ, List.prod_cons]
      exact (hg 0).mul (ih _ fun i => hg _)
  have h := hprod k (fun i t => NormedSpace.exp (t i • X i))
    fun i => hexp.comp ((contDiff_apply ℝ ℝ i).smul contDiff_const)
  exact T.contDiff.comp (contDiff_const.mul h)

end GlobalTheory.SecondKind

namespace GlobalTheory.SecondKind

open GlobalTheory.CuspRep

variable {E : Type} [Field E] [NumberField E] {d : ℕ}

theorem hasDerivAt_mulExp (y : Lie E d) (Z : Matrix (Fin d) (Fin d) (Cinf E)) :
    HasDerivAt (fun s : ℝ => toL (Matrix.of y * NormedSpace.exp (s • Z))) (toL (Matrix.of y * Z)) 0 := by
  letI : NormedRing (Matrix (Fin d) (Fin d) (Cinf E)) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (Fin d) (Fin d) (Cinf E)) := Matrix.linftyOpNormedAlgebra
  haveI : CompleteSpace (Matrix (Fin d) (Fin d) (Cinf E)) := FiniteDimensional.complete ℝ _
  let T : Matrix (Fin d) (Fin d) (Cinf E) →L[ℝ] Lie E d :=
    LinearMap.toContinuousLinearMap (LinearMap.id : Lie E d →ₗ[ℝ] Lie E d)
  have h := ((hasDerivAt_exp_smul_const' (𝕂 := ℝ) Z (0 : ℝ)).const_mul (Matrix.of y))
  rw [zero_smul, NormedSpace.exp_zero, mul_one] at h
  exact T.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h

theorem fderiv_prodExp (y : Lie E d) {k : ℕ} (X : Fin k → Matrix (Fin d) (Fin d) (Cinf E)) (i : Fin k) (c : ℝ) :
    fderiv ℝ (fun t : Fin k → ℝ =>
      toL (Matrix.of y * (List.ofFn fun i => NormedSpace.exp (t i • X i)).prod)) 0 (Pi.single i c) =
      c • toL (Matrix.of y * X i) := by
  set Θ := fun t : Fin k → ℝ =>
      toL (Matrix.of y * (List.ofFn fun i => NormedSpace.exp (t i • X i)).prod)
  have hΘ : HasFDerivAt Θ (fderiv ℝ Θ 0) (0 : Fin k → ℝ) :=
    ((contDiff_prodExp y X).differentiable (by simp)).differentiableAt.hasFDerivAt
  let J : ℝ →L[ℝ] (Fin k → ℝ) := ContinuousLinearMap.single ℝ (fun _ : Fin k => ℝ) i
  have hJ0 : J 0 = 0 := map_zero J
  have h1 : HasFDerivAt (Θ ∘ J) ((fderiv ℝ Θ 0).comp J) 0 := by
    have hΘ' : HasFDerivAt Θ (fderiv ℝ Θ 0) (J 0) := by rw [hJ0]; exact hΘ
    exact hΘ'.comp (0 : ℝ) J.hasFDerivAt
  have e : Θ ∘ J = fun s : ℝ => toL (Matrix.of y * NormedSpace.exp (s • X i)) := by
    funext s
    simp only [Function.comp_apply, Θ]
    congr 2
    rw [prod_ofFn_eq_of_ne _ i]
    · simp [J]
    · intro j hj
      simp [J, Pi.single_eq_of_ne hj]
  rw [e] at h1
  have h2 := h1.hasDerivAt.unique (hasDerivAt_mulExp y (X i))
  have h3 : Pi.single i c = c • J 1 := by
    simp [J, ← Pi.single_smul]
  rw [h3, map_smul]
  simpa using congrArg (c • ·) h2

end GlobalTheory.SecondKind

namespace GlobalTheory.SecondKind

open GlobalTheory.CuspRep

theorem contDiffOn_of_prodExp : ∀ (E : Type) [Field E] [NumberField E] (d : ℕ) (f : GlobalTheory.CuspRep.Lie E d → ℂ)
    (S : Set (Matrix (Fin d) (Fin d) (GlobalTheory.CuspRep.Cinf E))), Submodule.span ℝ S = ⊤ →
    (∀ (k : ℕ) (X : Fin k → Matrix (Fin d) (Fin d) (GlobalTheory.CuspRep.Cinf E)), (∀ i, X i ∈ S) →
      ∀ y ∈ GlobalTheory.CuspRep.invSet E d, ContDiff ℝ ∞ fun t : Fin k → ℝ =>
        f (GlobalTheory.CuspRep.toL (Matrix.of y * (List.ofFn fun i => NormedSpace.exp (t i • X i)).prod))) →
    ContDiffOn ℝ ∞ f (GlobalTheory.CuspRep.invSet E d) := by
  intro E _ _ d f S hS hf x₀ hx₀
  refine ContDiffAt.contDiffWithinAt ?_

  obtain ⟨b, hbS, hbspan, hbli⟩ := exists_linearIndependent ℝ S
  haveI : Module.Finite ℝ (Matrix (Fin d) (Fin d) (Cinf E)) := inferInstance
  haveI : Finite b := hbli.finite
  letI : Fintype b := Fintype.ofFinite b
  set m := Fintype.card b
  let e := Fintype.equivFin b
  let X : Fin m → Matrix (Fin d) (Fin d) (Cinf E) := fun i => (e.symm i).1
  have hXS : ∀ i, X i ∈ S := fun i => hbS (e.symm i).2
  have hXli : LinearIndependent ℝ X := hbli.comp e.symm e.symm.injective
  have hXspan : Submodule.span ℝ (Set.range X) = ⊤ := by
    have : Set.range X = b := by
      ext x; constructor
      · rintro ⟨i, rfl⟩; exact (e.symm i).2
      · intro hx; exact ⟨e ⟨x, hx⟩, by simp [X]⟩
    rw [this, hbspan, hS]
  let B : Module.Basis (Fin m) ℝ (Matrix (Fin d) (Fin d) (Cinf E)) := Module.Basis.mk hXli hXspan.ge
  have hdim : Module.finrank ℝ (Fin m → ℝ) = Module.finrank ℝ (Lie E d) := by
    rw [Module.finrank_fin_fun]
    exact (Module.finrank_eq_card_basis B).trans (Fintype.card_fin m) |>.symm

  let Lin : (Fin m → ℝ) →ₗ[ℝ] Lie E d :=
    { toFun := fun t => toL (Matrix.of x₀ * ∑ i, t i • X i)
      map_add' := fun s t => by
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib, mul_add]; rfl
      map_smul' := fun c t => by
        simp only [Pi.smul_apply, smul_eq_mul, mul_smul, ← Finset.smul_sum, Matrix.mul_smul]; rfl }
  have hLinj : Function.Injective Lin := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro t ht
    have h1 : Matrix.of x₀ * ∑ i, t i • X i = Matrix.of x₀ * 0 := by
      rw [mul_zero]; exact ht
    have h2 := (show IsUnit (Matrix.of x₀) from hx₀).mul_left_cancel h1
    funext i
    exact Fintype.linearIndependent_iff.1 hXli t h2 i
  let L : (Fin m → ℝ) ≃L[ℝ] Lie E d :=
    (LinearMap.linearEquivOfInjective Lin hLinj hdim).toContinuousLinearEquiv
  set Θ := fun t : Fin m → ℝ =>
      toL (Matrix.of x₀ * (List.ofFn fun i => NormedSpace.exp (t i • X i)).prod) with hΘdef
  have hΘ : ContDiff ℝ ∞ Θ := contDiff_prodExp x₀ X
  have hΘ0 : Θ 0 = x₀ := by
    simp [Θ]
  have hD : HasFDerivAt Θ (L : (Fin m → ℝ) →L[ℝ] Lie E d) 0 := by
    have h := ((hΘ.differentiable (by simp)) 0).hasFDerivAt
    have hE : ((L : (Fin m → ℝ) →L[ℝ] Lie E d) : (Fin m → ℝ) →ₗ[ℝ] Lie E d) =
        ((fderiv ℝ Θ 0 : (Fin m → ℝ) →L[ℝ] Lie E d) : (Fin m → ℝ) →ₗ[ℝ] Lie E d) := by
      refine LinearMap.pi_ext fun i c => ?_
      change Lin (Pi.single i c) = fderiv ℝ Θ 0 (Pi.single i c)
      rw [hΘdef, fderiv_prodExp]
      simp only [Lin, LinearMap.coe_mk, AddHom.coe_mk]
      rw [Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_eq_of_ne hj]) (by simp)]
      simp only [Pi.single_eq_same, Matrix.mul_smul]
      rfl
    rw [ContinuousLinearMap.coe_injective hE]
    exact h
  have hn : (∞ : ℕ∞ω) ≠ 0 := by simp
  have hΨ := hΘ.contDiffAt.to_localInverse hD hn
  have hinv := (hΘ.contDiffAt.hasStrictFDerivAt' hD hn).eventually_right_inverse
  have hc : ContDiffAt ℝ ∞ (f ∘ Θ ∘ hΘ.contDiffAt.localInverse hD hn) (Θ 0) :=
    (hf m X hXS x₀ hx₀).contDiffAt.comp _ hΨ
  rw [hΘ0] at hc hinv
  refine hc.congr_of_eventuallyEq (hinv.mono fun x hx => ?_)
  simp only [Function.comp_apply]
  exact congrArg f hx.symm

end GlobalTheory.SecondKind
