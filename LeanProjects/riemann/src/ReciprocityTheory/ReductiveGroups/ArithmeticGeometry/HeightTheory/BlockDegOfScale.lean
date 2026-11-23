import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.ScaleMultiHomogeneous

namespace ReciprocityTheory.ChartRestriction.G.T0

open MvPolynomial

section Gen

variable {K : Type} [Field K] {D N : ℕ}

theorem coeff_scaleEquiv {σ : Type*} [Fintype σ] (P : σ → Prop) [DecidablePred P] (u : Kˣ)
    (F : MvPolynomial σ K) (s : σ →₀ ℕ) :
    coeff s (scaleEquiv P u F) = (u : K) ^ (∑ v ∈ Finset.univ.filter P, s v) * coeff s F := by

  have hmon : ∀ (t : σ →₀ ℕ) (a : K), scaleEquiv P u (monomial t a) =
      monomial t ((u : K) ^ (∑ v ∈ Finset.univ.filter P, t v) * a) := by
    intro t a
    have hg : ∀ v, (if P v then C (u : K) * X v else X v) ^ t v =
        C (if P v then (u : K) ^ t v else 1) * (X v : MvPolynomial σ K) ^ t v := by
      intro v
      split_ifs <;> simp [mul_pow]
    rw [scaleEquiv, AlgEquiv.ofAlgHom_apply, aeval_monomial]
    rw [monomial_eq]
    simp only [Finsupp.prod_pow, algebraMap_eq, hg, Finset.prod_mul_distrib, ← map_prod, ← Finset.prod_filter,
      Finset.prod_pow_eq_pow_sum, map_mul]
    ring
  classical
  refine MvPolynomial.induction_on' F (fun t a => ?_) (fun p q hp hq => ?_)
  · rw [hmon, coeff_monomial, coeff_monomial]
    split_ifs with h
    · subst h
      rfl
    · simp
  · rw [map_add, coeff_add, coeff_add, hp, hq, mul_add]

theorem sum_filter_block (b : Fin (D + 1)) (s : TVar D N →₀ ℕ) :
    (∑ v ∈ Finset.univ.filter (fun v : TVar D N => v.1 = b), s v) = ∑ j, s (b, j) := by
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  refine (Finset.sum_eq_single b (fun c _ hc => Finset.sum_eq_zero fun j _ => if_neg hc)
    (by simp)).trans (Finset.sum_congr rfl fun j _ => if_pos rfl)

theorem block_deg_of_scale [CharZero K] (b : Fin (D + 1)) (a : ℕ) (F : MvPolynomial (TVar D N) K)
    (hF : ∀ u : Kˣ, scaleEquiv (fun v : TVar D N => v.1 = b) u F = C ((u : K) ^ a) * F) :
    ∀ s ∈ F.support, ∑ j, s (b, j) = a := by
  intro s hs
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  have h := congrArg (coeff s) (hF (Units.mk0 2 h2))
  rw [coeff_scaleEquiv, coeff_C_mul, sum_filter_block] at h
  have hc : coeff s F ≠ 0 := mem_support_iff.1 hs
  have h' := mul_right_cancel₀ hc h
  simp only [Units.val_mk0] at h'
  have h'' : ((2 ^ (∑ j, s (b, j)) : ℕ) : K) = ((2 ^ a : ℕ) : K) := by
    push_cast
    exact h'
  exact Nat.pow_right_injective (le_refl 2) (Nat.cast_injective h'')

end Gen

section Blocks

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {D N : ℕ}

def IsBaseBlockVar (b : Fin (D + 1)) (v : SVar D N) : Prop :=
  Sum.elim (fun _ => b = 0) (fun w : Fin (D + 1) × Fin N => w.1 = b) v

instance (b : Fin (D + 1)) : DecidablePred (IsBaseBlockVar (D := D) (N := N) b) := by
  intro v
  cases v <;> simp only [IsBaseBlockVar, Sum.elim_inl, Sum.elim_inr] <;> infer_instance

noncomputable def tauPG (b : Fin (D + 1)) (u : Kˣ) :
    MvPolynomial (SVar D N) Ω ≃ₐ[Ω] MvPolynomial (SVar D N) Ω :=
  scaleEquiv (IsBaseBlockVar b) (Units.map (algebraMap K Ω).toMonoidHom u)

noncomputable def tauFG (b : Fin (D + 1)) (u : Kˣ) : OmS Ω D N ≃+* OmS Ω D N :=
  IsFractionRing.ringEquivOfRingEquiv (tauPG (Ω := Ω) (D := D) (N := N) b u).toRingEquiv

end Blocks

end ReciprocityTheory.ChartRestriction.G.T0
