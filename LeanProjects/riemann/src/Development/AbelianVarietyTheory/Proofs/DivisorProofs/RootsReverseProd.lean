import Mathlib
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr

noncomputable section

open Polynomial CategoryTheory

namespace GlobalTheory.DualLabel

theorem roots_reverse_prod {K : Type} [Field K] (s : Multiset K) (hs : (0 : K) ∉ s) :
    ((s.map fun x => X - C x).prod.reverse).roots = s.map (·⁻¹) := by
  induction s using Multiset.induction_on with
  | empty => simp [reverse]
  | cons a s ih =>
    rw [Multiset.mem_cons, not_or] at hs
    have ha : a ≠ 0 := fun h => hs.1 h.symm
    have hX : (X : K[X]).reverse = 1 := by simp [reverse]
    have e : (X - C a : K[X]).reverse = C (-a) * (X - C a⁻¹) := by
      rw [sub_eq_add_neg, ← C_neg, reverse_add_C, natDegree_X, hX, mul_sub, ← C_mul, neg_mul,
        mul_inv_cancel₀ ha]
      simp [add_comm]
    have hm : (s.map fun x => X - C x).prod ≠ 0 :=
      (monic_multiset_prod_of_monic _ _ fun x _ => monic_X_sub_C x).ne_zero
    rw [Multiset.map_cons, Multiset.prod_cons, reverse_mul_of_domain, e, roots_mul, roots_C_mul _ (neg_ne_zero.2 ha),
      roots_X_sub_C, ih hs.2, Multiset.map_cons, Multiset.singleton_add]
    exact mul_ne_zero (mul_ne_zero (C_ne_zero.2 (neg_ne_zero.2 ha)) (X_sub_C_ne_zero _))
      (by rwa [Ne, reverse_eq_zero])

theorem monic_normRev {K : Type} [Field K] {f : K[X]} (h0 : f.coeff 0 ≠ 0) :
    (C (f.coeff 0)⁻¹ * f.reverse).Monic := by
  rw [Monic, leadingCoeff_mul, leadingCoeff_C, reverse_leadingCoeff, trailingCoeff_eq_coeff_zero h0,
    inv_mul_cancel₀ h0]

theorem rootsBar_normRev {K : Type} [Field K] {f : K[X]} (hm : f.Monic) (h0 : f.coeff 0 ≠ 0) :
    Formalism.IrreducibleCountingLemmas.TYPES.rootsBar K (C (f.coeff 0)⁻¹ * f.reverse) =
      (Formalism.IrreducibleCountingLemmas.TYPES.rootsBar K f).map (·⁻¹) := by
  have hz : (0 : AlgebraicClosure K) ∉ Formalism.IrreducibleCountingLemmas.TYPES.rootsBar K f := fun h => by
    rw [Formalism.IrreducibleCountingLemmas.TYPES.rootsBar, mem_roots (hm.map _).ne_zero, IsRoot, ← coeff_zero_eq_eval_zero,
      coeff_map] at h
    exact h0 ((map_eq_zero _).1 h)
  have e : f.reverse.map (algebraMap K (AlgebraicClosure K)) = (f.map (algebraMap K (AlgebraicClosure K))).reverse := by
    rw [reverse, reverse, reflect_map, natDegree_map]
  have hf := (IsAlgClosed.splits (f.map (algebraMap K (AlgebraicClosure K)))).eq_prod_roots_of_monic (hm.map _)
  rw [Formalism.IrreducibleCountingLemmas.TYPES.rootsBar, Polynomial.map_mul, map_C, roots_C_mul _ (by simpa using h0), e, hf]
  exact roots_reverse_prod _ hz

theorem eq_of_rootsBar_eq {K : Type} [Field K] {f g : K[X]} (hf : f.Monic) (hg : g.Monic)
    (h : Formalism.IrreducibleCountingLemmas.TYPES.rootsBar K f = Formalism.IrreducibleCountingLemmas.TYPES.rootsBar K g) : f = g := by
  apply map_injective (algebraMap K (AlgebraicClosure K)) (algebraMap K (AlgebraicClosure K)).injective
  rw [(IsAlgClosed.splits (f.map (algebraMap K (AlgebraicClosure K)))).eq_prod_roots_of_monic (hf.map _),
    (IsAlgClosed.splits (g.map (algebraMap K (AlgebraicClosure K)))).eq_prod_roots_of_monic (hg.map _)]
  exact congrArg (fun s => (s.map fun a => X - C a).prod) h

theorem lab_dual : ∀ {K : Type} [Field K] [Fintype K] [DecidableEq K] {C : Formalism.IrreducibleCountingLemmas.TYPES.LabelConv K}
    (O : Formalism.IrreducibleCountingLemmas.TYPES.LabelMap K C), Formalism.IrreducibleCountingLemmas.TYPES.LabelMapEquivariant O →
    ∀ (d : ℕ) (τ τ' : FDRep ℂ (GL (Fin d) K)), 1 ≤ d → Simple τ → Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal K τ → Simple τ' →
    Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal K τ' →
    (∀ γ : GL (Fin d) K, LinearMap.trace ℂ τ'.V (τ'.ρ γ) = LinearMap.trace ℂ τ.V (τ.ρ γ⁻¹)) →
    O.lab d τ' = Polynomial.C ((O.lab d τ).coeff 0)⁻¹ * (O.lab d τ).reverse := by
  intro K _ _ _ C O hO d τ τ' hd hs hc hs' hc' htr
  have h := hO.2 d τ τ' hd hs hc hs' hc' htr
  obtain ⟨hm, hi, hX, -⟩ := O.lab_spec d τ hd hs hc
  have h0 := Formalism.L2.NT.coeff_zero_ne_of_monic_irr hm hi hX
  refine eq_of_rootsBar_eq (O.lab_spec d τ' hd hs' hc').1 (monic_normRev h0) ?_
  rw [h, rootsBar_normRev hm h0]

end GlobalTheory.DualLabel
