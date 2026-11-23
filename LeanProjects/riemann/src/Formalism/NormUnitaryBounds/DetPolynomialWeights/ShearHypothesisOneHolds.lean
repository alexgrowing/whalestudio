import Formalism.NormUnitaryBounds.Statement
import Formalism.NormUnitaryBounds.DetPolynomialWeights.NatDegreeAevalLe

open MvPolynomial

noncomputable section

namespace Formalism.NormUnitaryCountingLemmas.H1OnPoints

variable {R : Type*} [CommRing R]

lemma core {B : Type*} [CommRing B] [Algebra R B] {N n : ℕ} {ν : Fin (N + 1) → ℕ}
    {F : MvPolynomial (Fin (N + 1) × Fin n) R} (hF : F ∈ H R ν)
    (x : Fin (N + 1) → Fin n → B) (u : Fin n → B) (c : Fin (N + 1) → B)
    (hc : IsLeftRegular (c 0)) :
    (aeval (fun p : Fin (N + 1) × Fin n =>
      Polynomial.C (x p.1 p.2) + Polynomial.X * Polynomial.C (c p.1 * u p.2)) F).natDegree
        ≤ ν 0 := by
  have hW : IsWeightedHomogeneous (blockWt (N + 1) n) F ν :=
    (mem_weightedHomogeneousSubmodule _ _ _ _).mp (Submodule.mem_inf.mp hF).1
  set φ : Fin (N + 1) × Fin n → Polynomial B := fun p =>
    Polynomial.C (x p.1 p.2) + Polynomial.X * Polynomial.C (c p.1 * u p.2) with hφ
  let y : Fin (N + 1) × Fin n → Polynomial B := fun p =>
    if p.1 = 0 then Polynomial.C (x 0 p.2) + Polynomial.X * Polynomial.C (c 0 * u p.2)
    else Polynomial.C (c 0 * x p.1 p.2 - c p.1 * x 0 p.2)
  let lam : Fin (N + 1) → Polynomial B := fun j => if j = 0 then 1 else Polynomial.C (c 0)
  let ℓ : B := ∏ j, (if j = 0 then 1 else c 0) ^ ν j
  have hsc := aeval_scale F hW lam φ
  have hfun : (fun p : Fin (N + 1) × Fin n => lam p.1 * φ p) = fun p =>
      y p + if p.1 ∈ Finset.univ.erase 0 then Polynomial.C (c p.1) * y (0, p.2) else 0 := by
    funext p
    obtain ⟨j, k⟩ := p
    by_cases hj : j = 0
    · subst hj
      simp [lam, y, φ]
    · simp only [lam, y, φ, hj, if_false, Finset.mem_erase, ne_eq, not_false_eq_true,
        Finset.mem_univ, and_true, if_true, map_sub, map_mul]
      ring
  have hsh := shear_multi hF y (fun j => Polynomial.C (c j)) (Finset.univ.erase 0) (by simp)
  rw [hfun, hsh] at hsc
  have hdeg := natDegree_aeval_le F hW y (by
    intro p
    by_cases h : p.1 = 0
    · simp only [y, h, if_true]
      have : Polynomial.C (x 0 p.2) + Polynomial.X * Polynomial.C (c 0 * u p.2) =
          Polynomial.C (c 0 * u p.2) * Polynomial.X + Polynomial.C (x 0 p.2) := by ring
      rw [this]
      exact Polynomial.natDegree_linear_le
    · simp only [y, h, if_false]
      exact (Polynomial.natDegree_C _).le)
  have hprodC : (∏ j, lam j ^ ν j) = Polynomial.C ℓ := by
    simp only [lam, ℓ, map_prod, map_pow]
    refine Finset.prod_congr rfl fun j _ => ?_
    split_ifs <;> simp
  have hℓ : IsLeftRegular ℓ := by
    refine Finset.prod_induction _ (fun b : B => IsLeftRegular b) (fun a b ha hb => ha.mul hb)
      (isRegular_one : IsRegular (1 : B)).left fun j _ => IsLeftRegular.pow _ ?_
    split_ifs
    · exact (isRegular_one : IsRegular (1 : B)).left
    · exact hc
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero] at hdeg ⊢
  intro e he
  have h0 := hdeg e he
  rw [hsc, hprodC, Polynomial.coeff_C_mul] at h0
  exact hℓ (h0.trans (mul_zero ℓ).symm)

end Formalism.NormUnitaryCountingLemmas.H1OnPoints

namespace Formalism.NormUnitaryCountingLemmas

open Formalism.NormUnitaryCountingLemmas.H1OnPoints in
theorem shear_hypothesis_one_holds : H1 := by
  intro R _ N n ν F hF A _ _ x u c
  let g : Polynomial A →ₐ[R] A := (Polynomial.aeval (0 : A)).restrictScalars R
  have hreg : IsLeftRegular (Polynomial.C (c 0) + Polynomial.X : Polynomial A) := by
    rw [add_comm]
    exact (Polynomial.monic_X_add_C _).isRegular.left
  have hc := core (B := Polynomial A) hF (fun j k => Polynomial.C (x j k))
    (fun k => Polynomial.C (u k)) (fun j => Polynomial.C (c j) + if j = 0 then Polynomial.X else 0)
    (by simpa using hreg)
  refine le_trans (le_of_eq ?_) ((Polynomial.natDegree_map_le (f := (g : Polynomial A →+* A))).trans hc)
  congr 1
  rw [← Polynomial.coe_mapAlgHom, ← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  congr 1
  congr 1
  funext p
  by_cases h : p.1 = 0 <;> simp [g, h]

end Formalism.NormUnitaryCountingLemmas
