import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ThDistC

open Formalism.L2.Ker MvPolynomial

noncomputable section

namespace GlobalTheory.JetScale

section General

variable {σ : Type} [Fintype σ]

def scaleVar (w : σ → ℂ) : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial σ ℂ :=
  aeval fun v => C (w v) * X v

lemma monomial_eq_prod (s : σ →₀ ℕ) (r : ℂ) :
    (monomial s r : MvPolynomial σ ℂ) = C r * ∏ v, X v ^ s v := by
  rw [monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]

lemma scaleVar_monomial (w : σ → ℂ) (s : σ →₀ ℕ) (r : ℂ) :
    scaleVar w (monomial s r) = monomial s (r * ∏ v, w v ^ s v) := by
  rw [monomial_eq_prod, monomial_eq_prod, scaleVar, map_mul, aeval_C, map_prod, map_mul C, map_prod C]
  simp only [map_pow, aeval_X, mul_pow, Finset.prod_mul_distrib, algebraMap_eq]
  ring

end General

section Jet

variable {ι : Type} [Fintype ι] {a b : ℕ}

lemma jetLin_monomial (J : (DVar ι a b →₀ ℕ) → ℂ) (m : ((ι × Fin b × Fin b) ⊕ DVar ι a b) →₀ ℕ) (r : ℂ) :
    jetLin J (monomial m r) =
      monomial (m.comapDomain Sum.inl Sum.inl_injective.injOn) (r * J (m.comapDomain Sum.inr Sum.inr_injective.injOn)) := by
  have h : (monomial m r : MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) ℂ) =
      r • basisMonomials ((ι × Fin b × Fin b) ⊕ DVar ι a b) ℂ m := by
    rw [coe_basisMonomials, smul_monomial, smul_eq_mul, mul_one]
  rw [h, map_smul, jetLin, Module.Basis.constr_basis, smul_monomial, smul_eq_mul]

def wDer (c : ι → ℂ) : (ι × Fin b × Fin b) ⊕ DVar ι a b → ℂ := Sum.elim (fun _ => 1) (fun k => c k.1)

def wCoord (c : ι → ℂ) : (ι × Fin b × Fin b) ⊕ DVar ι a b → ℂ := Sum.elim (fun k => c k.1) (fun _ => 1)

lemma jetLin_scaleDer (c : ι → ℂ) (J : (DVar ι a b →₀ ℕ) → ℂ) (Q : MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) ℂ) :
    jetLin J (scaleVar (wDer c) Q) = jetLin (fun m => (∏ k, c k.1 ^ m k) * J m) Q := by
  induction Q using MvPolynomial.induction_on' with
  | monomial m r =>
    rw [scaleVar_monomial, jetLin_monomial, jetLin_monomial, Fintype.prod_sum_type]
    simp [wDer, Finsupp.comapDomain_apply]
    congr 1
    ring
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]

lemma blockAct_diag (c : ι → ℂ) :
    Formalism.GradedWeylDivisibility.blockAct ℂ (n := b) (fun τ => Matrix.diagonal fun _ : Fin b => c τ) = scaleVar (fun v : ι × Fin b × Fin b => c v.1) := by
  apply MvPolynomial.algHom_ext
  intro v
  simp [Formalism.GradedWeylDivisibility.blockAct, scaleVar, Matrix.diagonal_apply, apply_ite C, ite_mul, Finset.sum_ite_eq]

lemma jetLin_scaleCoord (c : ι → ℂ) (J : (DVar ι a b →₀ ℕ) → ℂ) (Q : MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) ℂ) :
    jetLin J (scaleVar (wCoord c) Q) = scaleVar (fun v : ι × Fin b × Fin b => c v.1) (jetLin J Q) := by
  induction Q using MvPolynomial.induction_on' with
  | monomial m r =>
    rw [scaleVar_monomial, jetLin_monomial, jetLin_monomial, scaleVar_monomial, Fintype.prod_sum_type]
    simp [wCoord, Finsupp.comapDomain_apply]
    congr 1
    ring
  | add p q hp hq => simp only [map_add, hp, hq]

lemma scale_subD (c : ι → ℂ) :
    (scaleVar (wDer (a := a) (b := b) c)).comp (subD ℂ ι a b) = (scaleVar (wCoord c)).comp (subD ℂ ι a b) := by
  apply MvPolynomial.algHom_ext
  intro v
  simp only [AlgHom.comp_apply, subD, aeval_X]
  split_ifs
  · simp only [map_sum, map_mul, scaleVar, aeval_X, wDer, wCoord, Sum.elim_inl, Sum.elim_inr, map_one, one_mul]
    refine Finset.sum_congr rfl fun β _ => ?_
    ring
  · simp

lemma jetLin_smul_table (u : ℂ) (J : (DVar ι a b →₀ ℕ) → ℂ) (Q : MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) ℂ) :
    jetLin (fun m => u * J m) Q = u • jetLin J Q := by
  induction Q using MvPolynomial.induction_on' with
  | monomial m r =>
    rw [jetLin_monomial, jetLin_monomial, smul_monomial, smul_eq_mul]
    congr 1
    ring
  | add p q hp hq => simp only [map_add, hp, hq, smul_add]

end Jet

theorem jetMap_weight_scale {ι : Type} [Fintype ι] {a b : ℕ} (u : ℂ) (c : ι → ℂ) (J : (DVar ι a b →₀ ℕ) → ℂ) (nn : ι → ℕ)
    (P : Formalism.L2.DIV.Pol ℂ ι a) :
    jetMap (fun m => u * ((m.prod fun k e => c k.1 ^ e) * J m)) nn P =
      u • Formalism.GradedWeylDivisibility.blockAct ℂ (fun τ => Matrix.diagonal fun _ : Fin b => c τ) (jetMap J nn P) := by
  have hJ : (fun m : DVar ι a b →₀ ℕ => u * ((m.prod fun k e => c k.1 ^ e) * J m)) =
      fun m => u * ((∏ k, c k.1 ^ m k) * J m) := by
    funext m
    rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  rw [hJ, blockAct_diag]
  rw [jetMap, jetMap, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply,
    AlgHom.toLinearMap_apply]
  have key := DFunLike.congr_fun (scale_subD (a := a) (b := b) c) (LinearMap.mulRight ℂ (∏ τ, frDet ℂ a τ ^ nn τ) P)
  rw [AlgHom.comp_apply, AlgHom.comp_apply] at key
  rw [jetLin_smul_table, ← jetLin_scaleDer, key, jetLin_scaleCoord]

end GlobalTheory.JetScale
