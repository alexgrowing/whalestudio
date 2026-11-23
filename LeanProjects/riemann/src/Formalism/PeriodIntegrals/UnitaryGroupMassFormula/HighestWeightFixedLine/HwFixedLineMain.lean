import Mathlib
import Formalism.PeriodIntegrals.HwFixedLine
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.HwIrred

noncomputable section

namespace PI.HwFix.Line

open Formalism.BasicNotions Formalism.L2.DIV MvPolynomial
open scoped Matrix

section Spec

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ}

def spec (τ : ι) (y : ι × Fin n × Fin n → ℂ) : Pol ℂ ι n →ₐ[ℂ] MvPolynomial (Fin n × Fin n) ℂ :=
  aeval fun v => if v.1 = τ then X v.2 else C (y v)

theorem eval_spec (τ : ι) (y : ι × Fin n × Fin n → ℂ) (z : Fin n × Fin n → ℂ) (P : Pol ℂ ι n) :
    eval z (spec τ y P) = eval (fun v => if v.1 = τ then z v.2 else y v) P := by
  have h : (aeval z).comp (spec τ y) =
      aeval (fun v : ι × Fin n × Fin n => if v.1 = τ then z v.2 else y v) := by
    apply MvPolynomial.algHom_ext
    intro v
    by_cases hv : v.1 = τ <;> simp [spec, hv]
  have := congrArg (fun φ => φ P) h
  simpa [MvPolynomial.coe_aeval_eq_eval] using this

theorem spec_blockEmb (τ σ : ι) (y : ι × Fin n × Fin n → ℂ) (F : MvPolynomial (Fin n × Fin n) ℂ) :
    spec τ y (Formalism.GradedWeylDivisibility.blockEmb ℂ σ F) = if σ = τ then F else C (eval (fun w => y (σ, w)) F) := by
  unfold spec Formalism.GradedWeylDivisibility.blockEmb
  rw [aeval_rename]
  split_ifs with h
  · subst h
    have : ((fun v : ι × Fin n × Fin n => if v.1 = σ then X v.2 else C (y v)) ∘ fun v => (σ, v)) = X := by
      funext w; simp
    rw [this, aeval_X_left_apply]
  · have : ((fun v : ι × Fin n × Fin n => if v.1 = τ then X v.2 else C (y v)) ∘ fun v => (σ, v)) =
        fun w => C (y (σ, w)) := by
      funext w; simp [h]
    rw [this]
    have hh : (aeval fun w : Fin n × Fin n => (C (y (σ, w)) : MvPolynomial (Fin n × Fin n) ℂ)) =
        (Algebra.ofId ℂ (MvPolynomial (Fin n × Fin n) ℂ)).comp (aeval fun w => y (σ, w)) := by
      apply MvPolynomial.algHom_ext
      intro w
      simp [MvPolynomial.algebraMap_eq]
    rw [hh, AlgHom.comp_apply]
    simp [MvPolynomial.algebraMap_eq]

theorem spec_ten (τ : ι) (y : ι × Fin n × Fin n → ℂ) (f : ι → MvPolynomial (Fin n × Fin n) ℂ) :
    ∃ c : ℂ, spec τ y (ten f) = c • f τ := by
  refine ⟨∏ σ ∈ Finset.univ.erase τ, eval (fun w => y (σ, w)) (f σ), ?_⟩
  unfold ten
  rw [map_prod, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ τ), spec_blockEmb, if_pos rfl]
  have : ∏ σ ∈ Finset.univ.erase τ, spec τ y (Formalism.GradedWeylDivisibility.blockEmb ℂ σ (f σ)) =
      C (∏ σ ∈ Finset.univ.erase τ, eval (fun w => y (σ, w)) (f σ)) := by
    rw [map_prod]
    refine Finset.prod_congr rfl fun σ hσ => ?_
    rw [spec_blockEmb, if_neg (Finset.ne_of_mem_erase hσ)]
  rw [this, MvPolynomial.smul_eq_C_mul, mul_comm]

theorem spec_mem (lam : ι → DomWeight n) (τ : ι) (y : ι × Fin n × Fin n → ℂ) (v : VV ℂ lam) :
    spec τ y v.1 ∈ nablaSq ℂ n (lam τ) := by
  have : VV ℂ lam ≤ (nablaSq ℂ n (lam τ)).comap (spec τ y).toLinearMap := by
    unfold VV Formalism.GradedWeylDivisibility.tensorLat
    rw [Submodule.span_le]
    rintro P ⟨F, hF, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap, AlgHom.toLinearMap_apply]
    change spec τ y (ten F) ∈ _
    obtain ⟨c, hc⟩ := spec_ten τ y F
    rw [hc]
    exact Submodule.smul_mem _ _ (hF τ)
  exact this v.2

theorem spec_blockAct (τ : ι) (y : ι × Fin n × Fin n → ℂ) (G : ι → Matrix (Fin n) (Fin n) ℂ)
    (hG : ∀ σ, σ ≠ τ → G σ = 1) (P : Pol ℂ ι n) :
    spec τ y (Formalism.GradedWeylDivisibility.blockAct ℂ G P) = Formalism.GradedWeylDivisibility.rowAct ℂ (G τ) (spec τ y P) := by
  have h : (spec τ y).comp (Formalism.GradedWeylDivisibility.blockAct ℂ G) = (Formalism.GradedWeylDivisibility.rowAct ℂ (G τ)).comp (spec τ y) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨σ, a, s⟩
    by_cases hσ : σ = τ
    · subst hσ
      simp [spec, Formalism.GradedWeylDivisibility.blockAct, Formalism.GradedWeylDivisibility.rowAct, MvPolynomial.algebraMap_eq]
    · simp [spec, Formalism.GradedWeylDivisibility.blockAct, Formalism.GradedWeylDivisibility.rowAct, hσ, hG σ hσ, Matrix.one_apply, MvPolynomial.algebraMap_eq]
  exact congrArg (fun φ => φ P) h

end Spec

section Assembly

variable {ι : Type} [Fintype ι] {n : ℕ}

theorem detTwK_uni (lam : ι → DomWeight n) (g : ι → GL (Fin n) ℂ) (hg : MtwUni g) : detTwK lam g = 1 := by
  unfold detTwK
  refine Finset.prod_eq_one fun σ _ => ?_
  unfold detPow
  rw [PI.WGB.det_unitri_A n (g σ) (hg σ).1 (hg σ).2]
  simp

theorem rhoK_val (lam : ι → DomWeight n) (g : ι → GL (Fin n) ℂ) (v : VV ℂ lam) :
    ((rhoK lam g v : VV ℂ lam) : Pol ℂ ι n) = detTwK lam g • trAct g v.1 := rfl

theorem spec_fixed [DecidableEq ι] (lam : ι → DomWeight n) (v : VV ℂ lam)
    (hv : ∀ g : ι → GL (Fin n) ℂ, MtwUni g → rhoK lam g v = v) (τ : ι) (y : ι × Fin n × Fin n → ℂ) :
    ∃ c : ℂ, spec τ y v.1 = c • extremal ℂ n (lam τ) := by
  apply (highest_weight_irreducible n (lam τ)).2.2 _ (spec_mem lam τ y v)
  intro h hl hd
  let g : ι → GL (Fin n) ℂ := Function.update 1 τ h
  have hg : MtwUni g := by
    intro σ
    by_cases hσ : σ = τ
    · subst hσ
      simp only [g, Function.update_self]
      exact ⟨hl, hd⟩
    · simp only [g, Function.update_of_ne hσ, Pi.one_apply, Units.val_one]
      exact ⟨fun i j hij => Matrix.one_apply_ne (ne_of_lt hij).symm, fun i => Matrix.one_apply_eq i⟩
  have h1 := congrArg Subtype.val (hv g hg)
  rw [rhoK_val, detTwK_uni lam g hg, one_smul] at h1
  unfold sqAct
  rw [detPow, PI.WGB.det_unitri_A n h hl hd, one_zpow, Units.val_one, one_smul]
  conv_rhs => rw [← h1]
  unfold trAct
  rw [spec_blockAct τ y _ (fun σ hσ => by simp [g, Function.update_of_ne hσ])]
  simp [g]

theorem vanish_of [DecidableEq ι] (e : ι → MvPolynomial (Fin n × Fin n) ℂ) (p : ι → Fin n × Fin n → ℂ)
    (hp : ∀ τ, eval (p τ) (e τ) ≠ 0) (Q : Pol ℂ ι n)
    (hQ : ∀ τ y, ∃ c : ℂ, spec τ y Q = c • e τ) (h0 : eval (fun v => p v.1 v.2) Q = 0) : Q = 0 := by
  have hS : ∀ S : Finset ι, ∀ x : ι × Fin n × Fin n → ℂ, (∀ v : ι × Fin n × Fin n, v.1 ∉ S → x v = p v.1 v.2) →
      eval x Q = 0 := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro x hx
      have : x = fun v => p v.1 v.2 := funext fun v => hx v (by simp)
      rw [this, h0]
    | insert τ S hτ ih =>
      intro x hx
      obtain ⟨c, hc⟩ := hQ τ x
      have h1 : eval (fun w => x (τ, w)) (spec τ x Q) = eval x Q := by
        rw [eval_spec]
        apply congrArg (fun z => eval z Q)
        funext v
        split_ifs with h
        · obtain ⟨σ, w⟩ := v
          simp only at h
          subst h
          rfl
        · rfl
      have h2 : eval (p τ) (spec τ x Q) = 0 := by
        rw [eval_spec]
        apply ih
        intro v hv
        split_ifs with h
        · rw [h]
        · exact hx v (by simp [Finset.mem_insert, h, hv])
      rw [hc, MvPolynomial.smul_eval] at h1 h2
      have hc0 : c = 0 := by
        rcases mul_eq_zero.mp h2 with h | h
        · exact h
        · exact absurd h (hp τ)
      rw [← h1, hc0, zero_mul]
  apply MvPolynomial.funext
  intro x
  rw [map_zero]
  exact hS Finset.univ x (by simp)

theorem hwFixedLine_main : HwFixedLine := by
  intro ι _ n lam v hv
  classical
  let e : ι → MvPolynomial (Fin n × Fin n) ℂ := fun τ => extremal ℂ n (lam τ)
  have hne : ∀ τ, ∃ z, eval z (e τ) ≠ 0 := by
    intro τ
    by_contra hc0
    have hc : ∀ z, eval z (e τ) = 0 := fun z => by
      by_contra h
      exact hc0 ⟨z, h⟩
    exact Formalism.GradedWeylDivisibility.hwNe ℂ n n le_rfl (lam τ).natW (MvPolynomial.funext fun z => by simpa [e, extremal] using hc z)
  choose p hp using hne
  have hten : eval (fun v => p v.1 v.2) (ten e) = ∏ τ, eval (p τ) (e τ) := by
    unfold ten
    rw [map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    unfold Formalism.GradedWeylDivisibility.blockEmb
    rw [eval_rename]
    rfl
  have hten0 : eval (fun v => p v.1 v.2) (ten e) ≠ 0 := by
    rw [hten]
    exact Finset.prod_ne_zero_iff.mpr fun τ _ => hp τ
  let c : ℂ := eval (fun v => p v.1 v.2) v.1 / eval (fun v => p v.1 v.2) (ten e)
  refine ⟨c, ?_⟩
  have hQ : v.1 - c • ten e = 0 := by
    apply vanish_of e p hp
    · intro τ y
      obtain ⟨c1, h1⟩ := spec_fixed lam v hv τ y
      obtain ⟨c2, h2⟩ := spec_ten τ y e
      refine ⟨c1 - c * c2, ?_⟩
      rw [map_sub, map_smul, h1, h2, smul_smul, sub_smul]
    · rw [map_sub, MvPolynomial.smul_eval]
      simp only [c]
      rw [div_mul_cancel₀ _ hten0, sub_self]
  apply Subtype.ext
  rw [Submodule.coe_smul]
  exact sub_eq_zero.mp hQ

end Assembly

end PI.HwFix.Line
