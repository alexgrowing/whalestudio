import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ConjugateConjugate
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SpanColsMul

namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex Module Matrix
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace Data

variable {r : ℕ} (X : Data E r)

theorem cc_kappa0 : cc X.κ0 = -X.κ0 := by
  have hx : IsCMField.complexConj E X.ξ0 = -X.ξ0 := X.ξ0_im
  rcases X.κ0_xi with h | h <;> rw [h] <;> simp only [cc, map_mul, map_neg, map_ofNat, hx] <;> ring

theorem tau_kappa0 (τ : X.Ψ) : τ.1 X.κ0 = -(I * X.c τ) := by
  have hcc := congrArg τ.1 X.cc_kappa0
  have hconj : conj (τ.1 X.κ0) = -(τ.1 X.κ0) := by
    rw [← map_neg, ← hcc]
    exact (NumberField.IsCMField.complexEmbedding_complexConj E τ.1 X.κ0).symm
  have hre : (τ.1 X.κ0).re = 0 := by
    have h := congrArg Complex.re hconj
    simp only [Complex.conj_re, Complex.neg_re] at h
    linarith
  have him := X.κ0_sign τ
  have hnorm : ‖τ.1 X.κ0‖ = X.c τ := by
    simp only [Data.c]
    rcases X.κ0_xi with h | h <;> rw [h] <;> simp [map_mul, map_neg, norm_mul, map_ofNat]
  have hz : τ.1 X.κ0 = ((τ.1 X.κ0).im : ℂ) * I := by
    apply Complex.ext <;> simp [hre]
  have habs : ‖τ.1 X.κ0‖ = -(τ.1 X.κ0).im := by
    conv_lhs => rw [hz]
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_neg him]
  apply Complex.ext
  · simp [hre]
  · simp
    linarith

noncomputable def Mmat (u : Fin 2 → Fin r → E) (β : Matrix (Fin 2) (Fin 2) E) : Matrix (Fin r) (Fin r) E :=
  Matrix.of fun a j => (if a = j then 1 else 0) +
    X.κ0 * ∑ i, ∑ k, β i k * u i a * ∑ l, X.Gm j l * cc (u k l)

theorem Mmat_map (u : Fin 2 → Fin r → E) (β : Matrix (Fin 2) (Fin 2) E) (τ : X.Ψ) :
    (X.Mmat u β).map τ.1 = X.zmat u (X.embH β) τ := by
  ext a j
  by_cases h : a = j <;>
    simp [h, Matrix.map_apply, Data.Mmat, Data.zmat, Data.embH, Data.emb, map_add, map_mul, map_sum,
      X.tau_kappa0 τ, cc, NumberField.IsCMField.complexEmbedding_complexConj] <;> ring

theorem embH_add (β β' : Matrix (Fin 2) (Fin 2) E) : X.embH (β + β') = X.embH β + X.embH β' := by
  funext τ i k
  simp [Data.embH]

theorem Mmat_zero (u : Fin 2 → Fin r → E) : X.Mmat u 0 = 1 := by
  ext a j
  simp [Data.Mmat, Matrix.one_apply]

private lemma Mmat_mulVec_eq_add_sum (u : Fin 2 → Fin r → E) (β : Matrix (Fin 2) (Fin 2) E) (v : Fin r → E) :
    X.Mmat u β *ᵥ v = v + ∑ i, (X.κ0 * ∑ k, β i k * herm X.Gm v (u k)) • u i := by
  funext a
  simp only [Matrix.mulVec, dotProduct, Data.Mmat, Matrix.of_apply, add_mul, Finset.sum_add_distrib,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, Pi.add_apply,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, herm, Finset.mul_sum, Finset.sum_mul]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  ring

private lemma herm_add_left_fundamental_domains (G : Matrix (Fin r) (Fin r) E) (x y z : Fin r → E) :
    herm G (x + y) z = herm G x z + herm G y z := by
  simp only [herm, Pi.add_apply, add_mul, Finset.sum_add_distrib]

private lemma herm_smul_left_fundamental_domains (G : Matrix (Fin r) (Fin r) E) (c : E) (x z : Fin r → E) :
    herm G (c • x) z = c * herm G x z := by
  simp only [herm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

private lemma herm_add_right_fundamental_domains' (G : Matrix (Fin r) (Fin r) E) (x y z : Fin r → E) :
    herm G x (y + z) = herm G x y + herm G x z := by
  simp only [herm, Pi.add_apply, cc, map_add, mul_add, Finset.sum_add_distrib]

private lemma herm_smul_right_eq_cc_mul' (G : Matrix (Fin r) (Fin r) E) (c : E) (x z : Fin r → E) :
    herm G x (c • z) = cc c * herm G x z := by
  simp only [herm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, cc, map_mul]
  ring

theorem Mmat_mul (u : Fin 2 → Fin r → E) (hu : ∀ i k, herm X.Gm (u i) (u k) = 0)
    (β β' : Matrix (Fin 2) (Fin 2) E) : X.Mmat u β * X.Mmat u β' = X.Mmat u (β + β') := by
  refine Matrix.toLin'.injective (LinearMap.ext fun v => ?_)
  simp only [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, Mmat_mulVec_eq_add_sum, herm_add_left_fundamental_domains,
    herm_smul_left_fundamental_domains, Fin.sum_univ_two, hu, mul_zero, add_zero, Matrix.add_apply]
  first
    | module
    | (simp only [add_mul, mul_add, add_smul]; abel)

noncomputable def gam (u : Fin 2 → Fin r → E) (hu : ∀ i k, herm X.Gm (u i) (u k) = 0)
    (β : Matrix (Fin 2) (Fin 2) E) : GL (Fin r) E :=
  ⟨X.Mmat u β, X.Mmat u (-β), by rw [X.Mmat_mul u hu, add_neg_cancel, Mmat_zero],
    by rw [X.Mmat_mul u hu, neg_add_cancel, Mmat_zero]⟩

theorem emb_mulVec (τ : E →+* ℂ) (M : Matrix (Fin r) (Fin r) E) (v : Fin r → E) :
    emb τ (M *ᵥ v) = (M.map τ) *ᵥ emb τ v := by
  funext a
  simp [Data.emb, Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]

private lemma cc_herm_Gm_eq_herm_swap (x y : Fin r → E) : cc (herm X.Gm x y) = herm X.Gm y x := by
  simp only [herm, cc, map_sum, map_mul, NumberField.IsCMField.complexConj_apply_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  first
    | (have hg := X.Gm_herm b a
       simp only [cc] at hg
       rw [hg]
       ring)
    | (have hg := X.Gm_herm a b
       simp only [cc] at hg
       rw [hg]
       ring)

theorem herm_Mmat (u : Fin 2 → Fin r → E) (hu : ∀ i k, herm X.Gm (u i) (u k) = 0)
    (β : Matrix (Fin 2) (Fin 2) E) (hβ : ∀ i k, cc (β i k) = β k i) (v w : Fin r → E) :
    herm X.Gm (X.Mmat u β *ᵥ v) (X.Mmat u β *ᵥ w) = herm X.Gm v w := by
  have hk : IsCMField.complexConj E X.κ0 = -X.κ0 := X.cc_kappa0
  have hb' : ∀ i k, IsCMField.complexConj E (β i k) = β k i := hβ
  have hh : ∀ x y, IsCMField.complexConj E (herm X.Gm x y) = herm X.Gm y x := cc_herm_Gm_eq_herm_swap X
  simp only [Mmat_mulVec_eq_add_sum, herm_add_left_fundamental_domains, herm_add_right_fundamental_domains', herm_smul_left_fundamental_domains,
    herm_smul_right_eq_cc_mul', Fin.sum_univ_two, hu, mul_zero, add_zero, zero_add, cc, map_mul, map_add,
    hk, hb', hh]
  ring

theorem Mmat_mulVec (u : Fin 2 → Fin r → E) (β : Matrix (Fin 2) (Fin 2) E) (v : Fin r → E) :
    X.Mmat u β *ᵥ v = v + ∑ i, (X.κ0 * ∑ k, β i k * herm X.Gm v (u k)) • u i := by
  funext a
  simp only [Matrix.mulVec, dotProduct, Data.Mmat, Matrix.of_apply, add_mul, Finset.sum_add_distrib,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, Pi.add_apply,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, herm, Finset.mul_sum, Finset.sum_mul]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  ring

end Data

end ReciprocityTheory.ChartRestriction.G.FD
