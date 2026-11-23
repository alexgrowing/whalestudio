import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ConnectionKillsSeries
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FormalExpMulFormalExpNeg

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory.NablaExpConj

variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]

section Lift

variable (k : Type) [CommRing k]

theorem liftX_hasSubst : HasSubst (fun p : Fin 1 × Fin d => (X (Sum.inl p.2) : AA k d)) :=
  hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _

theorem liftX_one : liftX k (1 : PS k 1 d) = 1 :=
  FormalCalc.subst_one' (liftX_hasSubst k)

theorem liftX_mul (f g : PS k 1 d) : liftX k (f * g) = liftX k f * liftX k g :=
  subst_mul (liftX_hasSubst k) f g

theorem liftX_sum {ι : Type} (s : Finset ι) (f : ι → PS k 1 d) :
    liftX k (∑ i ∈ s, f i) = ∑ i ∈ s, liftX k (f i) :=
  FormalCalc.subst_sum' (liftX_hasSubst k) s f

theorem pderiv_inl_liftX (f : PS k 1 d) (j : Fin d) :
    pderiv k (Sum.inl j) (liftX k f) = liftX k (pderiv k ((0 : Fin 1), j) f) := by
  unfold liftX
  rw [FormalCalc.pderiv_subst (liftX_hasSubst k), Finset.sum_eq_single ((0 : Fin 1), j)]
  · rw [pderiv_X_self, mul_one]
  · rintro ⟨a, b⟩ _ hne
    have hb : b ≠ j := fun h => hne (by subst h; rw [Subsingleton.elim a 0])
    rw [pderiv_X_of_ne (fun h => hb (Sum.inl_injective h)), mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem pderiv_inr_liftX (f : PS k 1 d) (i : Fin d) : pderiv k (Sum.inr i) (liftX k f) = 0 := by
  unfold liftX
  rw [FormalCalc.pderiv_subst (liftX_hasSubst k)]
  refine Finset.sum_eq_zero fun p _ => ?_
  rw [pderiv_X_of_ne Sum.inl_ne_inr, mul_zero]

end Lift

variable (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k]

omit [Algebra ℚ k] in

theorem Dx_liftX (B : FB R d O) (u : Fin d → k) (f : PS k 1 d) :
    Dx k B u (liftX k f) = liftX k (Dof (B.FK k) u f) := by
  simp only [Dx, Dof, pderiv_inl_liftX, liftX_sum, liftX_mul]

omit [Algebra ℚ k] in

theorem Dx_mul (B : FB R d O) (u : Fin d → k) (f G : AA k d) :
    Dx k B u (f * G) = Dx k B u f * G + f * Dx k B u G := by
  simp only [Dx, Derivation.leibniz, smul_eq_mul, Finset.sum_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun t _ => by ring

omit [Algebra ℚ k] in

theorem nabla_liftX_mul (B : FB R d O) (h : PS k 2 d) (m : ℕ) (u φ : Fin d → k) (f : PS k 1 d)
    (G : AA k d) :
    nabla k B h m u φ (liftX k f * G) =
      liftX k f * nabla k B h m u φ G + liftX k (Dof (B.FK k) u f) * G := by
  have e : ∀ c : Fin d → AA k d, ∑ i : Fin d, c i * pderiv k (Sum.inr i) (liftX k f * G) =
      liftX k f * ∑ i : Fin d, c i * pderiv k (Sum.inr i) G := by
    intro c
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Derivation.leibniz, pderiv_inr_liftX, smul_zero, add_zero, smul_eq_mul]
    ring
  unfold nabla
  rw [Dx_mul, Dx_liftX, e, e]
  ring

theorem Dof_expS (F : Fin d → PS k 2 d) (u : Fin d → k) {g : PS k 1 d}
    (hg : constantCoeff g = 0) : Dof F u (FB.expS k g) = FB.expS k g * Dof F u g := by
  have e : ∀ i, pderiv k i (FB.expS k g) = FB.expS k g * pderiv k i g :=
    FormalCalc.pderiv_formalExp hg
  unfold Dof
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [e]
  ring

theorem expS_neg_mul_expS {n : ℕ} {g : PS k n d} (hg : constantCoeff g = 0) :
    FB.expS k (-g) * FB.expS k g = 1 := by
  rw [mul_comm]
  exact FormalCalc.formalExp_mul_formalExp_neg hg

theorem main : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O) (h : PS k 2 d) (m : ℕ) (u φ : Fin d → k) (g : PS k 1 d), constantCoeff g = 0 → ∀ G : AA k d, liftX k (FB.expS k (-g)) * nabla k B h m u φ (liftX k (FB.expS k g) * G) = nabla k B h m u φ G + liftX k (Dof (B.FK k) u g) * G := by
  intro R _ d O _ _ k _ _ _ B h m u φ g hg G
  have e : liftX k (FB.expS k (-g)) * liftX k (FB.expS k g) = 1 := by
    rw [← liftX_mul, expS_neg_mul_expS k hg, liftX_one]
  rw [nabla_liftX_mul, Dof_expS k _ u hg, liftX_mul]
  linear_combination (nabla k B h m u φ G + liftX k (Dof (B.FK k) u g) * G) * e

end GlobalTheory.NablaExpConj
