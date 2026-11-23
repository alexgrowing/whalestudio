import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.LiftCommEAt

noncomputable section

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz.TGK

variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] {P : Type} [Fintype P] [DecidableEq P]

def cLam (lam : TV n M P →ₗ[ℂ] ℂ) (I : P → Fin n) : M →ₗ[ℂ] ℂ :=
  lam ∘ₗ LinearMap.single ℂ (fun _ : P → Fin n => M) I

theorem cLam_sum (lam : TV n M P →ₗ[ℂ] ℂ) (v : TV n M P) : lam v = ∑ I, cLam lam I (v I) := by
  conv_lhs => rw [← Finset.univ_sum_single v]
  rw [map_sum]
  rfl

omit [DecidableEq P] in
theorem cprod_one (I J : P → Fin n) :
    ∏ p, (1 : Matrix (Fin n) (Fin n) ℂ) (I p) (J p) = if I = J then 1 else 0 := by
  split_ifs with h
  · subst h; simp
  · obtain ⟨p, hp⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ p) (Matrix.one_apply_ne hp)

theorem cprod_erase (I J : P → Fin n) (p : P) (x : ℂ) :
    (∏ q ∈ Finset.univ.erase p, (1 : Matrix (Fin n) (Fin n) ℂ) (I q) (J q)) * x =
      ∑ b, if J = Function.update I p b then x else 0 := by
  by_cases h : ∀ q, q ≠ p → I q = J q
  · rw [Finset.prod_eq_one, one_mul, Finset.sum_eq_single (J p)]
    · rw [if_pos]; funext q; by_cases hq : q = p
      · subst hq; simp
      · simp [Function.update_of_ne hq, h q hq]
    · intro b _ hb; rw [if_neg]; intro hJ; apply hb; rw [hJ]; simp
    · simp
    · intro q hq; rw [h q (Finset.ne_of_mem_erase hq)]; simp
  · push Not at h
    obtain ⟨q, hqp, hq⟩ := h
    have h0 : ∏ q ∈ Finset.univ.erase p, (1 : Matrix (Fin n) (Fin n) ℂ) (I q) (J q) = 0 :=
      Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hqp, Finset.mem_univ q⟩) (Matrix.one_apply_ne hq)
    rw [h0, zero_mul]
    refine (Finset.sum_eq_zero fun b _ => if_neg ?_).symm
    intro hJ; apply hq; rw [hJ, Function.update_of_ne hqp]

theorem csum_erase (I : P → Fin n) (p : P) (φ : (P → Fin n) → ℂ) :
    ∑ J, (∏ q ∈ Finset.univ.erase p, (1 : Matrix (Fin n) (Fin n) ℂ) (I q) (J q)) * φ J =
      ∑ b, φ (Function.update I p b) := by
  simp_rw [cprod_erase]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp

omit [Fintype P] [DecidableEq P] in
theorem ckey (I : P → Fin n) (S : Finset P) (F : Fin n → Fin n → ℂ) (h : Fin n → P → ℂ) :
    ∑ a, ∑ b, F a b * ∑ p ∈ S, (if I p = a then h b p else 0) = ∑ p ∈ S, ∑ b, F (I p) b * h b p := by
  simp_rw [Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp

def cD {ι : Type} [DecidableEq ι] (bar : ι → ι) (τ : ι) (X : Matrix (Fin n) (Fin n) ℂ) (σ : ι) (i j : Fin n) : ℂ :=
  (if σ = τ then X i j else 0) + (if σ = bar τ then star (X i j) else 0)

theorem cderiv_entry {ι Γ : Type} [DecidableEq ι] (κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ) (bar : ι → ι) (τ : ι)
    (hne : bar τ ≠ τ) (hconj : ∀ σ γ i j, κ (bar σ) γ i j = star (κ σ γ i j))
    (X : Matrix (Fin n) (Fin n) ℂ) (c : ℝ → Γ)
    (hd : ∀ i j, HasDerivAt (fun t => κ τ (c t) i j) (X i j) 0)
    (hoth : ∀ τ', τ' ≠ τ → τ' ≠ bar τ → ∀ t, κ τ' (c t) = 1) (σ : ι) (i j : Fin n) :
    HasDerivAt (fun t => κ σ (c t) i j) (cD bar τ X σ i j) 0 := by
  unfold cD
  by_cases h1 : σ = τ
  · subst h1
    rw [if_pos rfl, if_neg (fun h => hne h.symm), add_zero]
    exact hd i j
  · by_cases h2 : σ = bar τ
    · subst h2
      rw [if_neg h1, if_pos rfl, zero_add]
      simp_rw [hconj τ]
      exact (hd i j).star
    · rw [if_neg h1, if_neg h2, add_zero]
      rw [show (fun t => κ σ (c t) i j) = fun _ => (1 : Matrix (Fin n) (Fin n) ℂ) i j from
        funext fun t => by rw [hoth σ h1 h2 t]]
      exact hasDerivAt_const _ _

omit [DecidableEq P] in
theorem cpart {ι : Type} [DecidableEq ι] (lab : P → ι) (bar : ι → ι) (τ : ι) (X : Matrix (Fin n) (Fin n) ℂ)
    (I : P → Fin n) (h : Fin n → P → ℂ) :
    ∑ p, ∑ b, cD bar τ X (lab p) (I p) b * h b p =
      ∑ p ∈ fib lab τ, ∑ b, X (I p) b * h b p + ∑ p ∈ fib lab (bar τ), ∑ b, star (X (I p) b) * h b p := by
  unfold fib
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  unfold cD
  split_ifs <;> simp [add_mul, Finset.sum_add_distrib]

theorem actT_der {ι Γ : Type} [DecidableEq ι] [Group Γ] (lab : P → ι) (κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ)
    (E : ι → Fin n → Fin n → Module.End ℂ M) (ρ : Γ → Module.End ℂ M) (bar : ι → ι) (τ : ι) (hne : bar τ ≠ τ)
    (hρ1 : ρ 1 = 1) (hκ1 : ∀ σ, κ σ 1 = 1) (hconj : ∀ σ γ i j, κ (bar σ) γ i j = star (κ σ γ i j))
    (X : Matrix (Fin n) (Fin n) ℂ) (c : ℝ → Γ) (hc0 : c 0 = 1)
    (hd : ∀ i j, HasDerivAt (fun t => κ τ (c t) i j) (X i j) 0)
    (hoth : ∀ τ', τ' ≠ τ → τ' ≠ bar τ → ∀ t, κ τ' (c t) = 1)
    (hρ : ∀ y (lam : M →ₗ[ℂ] ℂ), HasDerivAt (fun t => lam (ρ (c t) y))
      (lam ((∑ a, ∑ b, (X a b • E τ a b + star (X a b) • E (bar τ) a b)) y)) 0)
    (y : TV n M P) (lam : TV n M P →ₗ[ℂ] ℂ) :
    HasDerivAt (fun t => lam (actT lab κ ρ (c t) y))
      (lam ((∑ a, ∑ b, (X a b • tE (fib lab τ) (E τ) a b + star (X a b) • tE (fib lab (bar τ)) (E (bar τ)) a b)) y))
      0 := by
  have hf : (fun t => lam (actT lab κ ρ (c t) y)) = fun t => ∑ I, ∑ J,
      (∏ p, κ (lab p) (c t) (I p) (J p)) * cLam lam I (ρ (c t) (y J)) := by
    funext t
    rw [cLam_sum]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [actT_apply, map_sum]
    simp only [map_smul, smul_eq_mul]
  rw [hf]
  have hg : ∀ I J : P → Fin n, HasDerivAt (fun t => ∏ p, κ (lab p) (c t) (I p) (J p))
      (∑ p, (∏ q ∈ Finset.univ.erase p, (1 : Matrix (Fin n) (Fin n) ℂ) (I q) (J q)) •
        cD bar τ X (lab p) (I p) (J p)) 0 := by
    intro I J
    have := HasDerivAt.fun_finsetProd (u := Finset.univ) (f := fun p t => κ (lab p) (c t) (I p) (J p)) (x := 0)
      (fun p _ => cderiv_entry κ bar τ hne hconj X c hd hoth (lab p) (I p) (J p))
    simp only [hc0, hκ1] at this
    exact this
  have hall : HasDerivAt (fun t => ∑ I, ∑ J,
      (∏ p, κ (lab p) (c t) (I p) (J p)) * cLam lam I (ρ (c t) (y J))) _ 0 :=
    HasDerivAt.fun_sum fun I _ => HasDerivAt.fun_sum fun J _ => (hg I J).fun_mul (hρ (y J) (cLam lam I))
  refine hall.congr_deriv ?_
  simp only [hc0, hκ1, hρ1, Module.End.one_apply]
  rw [cLam_sum]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [Finset.sum_add_distrib]
  simp_rw [cprod_one, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  simp_rw [Finset.sum_mul, smul_eq_mul, mul_assoc]
  rw [Finset.sum_comm]
  simp_rw [csum_erase, Function.update_self]
  rw [cpart lab bar τ X I (fun b p => cLam lam I (y (Function.update I p b)))]
  simp only [LinearMap.sum_apply, LinearMap.add_apply, LinearMap.smul_apply, Finset.sum_apply, Pi.add_apply,
    Pi.smul_apply, tE_apply, map_sum, map_add, map_smul, smul_eq_mul, apply_ite (cLam lam I), map_zero,
    mul_add, Finset.sum_add_distrib]
  rw [ckey I (fib lab τ) (fun a b => X a b) (fun b p => cLam lam I (y (Function.update I p b))),
    ckey I (fib lab (bar τ)) (fun a b => star (X a b)) (fun b p => cLam lam I (y (Function.update I p b)))]
  ring

end PositivityTheory.Rg.Cz.TGK

end
