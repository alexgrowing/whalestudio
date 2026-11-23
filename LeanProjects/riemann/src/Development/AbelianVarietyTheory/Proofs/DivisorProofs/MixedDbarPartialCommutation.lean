import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarEqZeroOfHolomorphic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgeContrSelfApply

set_option autoImplicit false
noncomputable section
open Matrix GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.FlatAcyc
open scoped Real ContDiff

namespace GlobalTheory.TorsionForm.FlatAcyc.Cross

theorem wedge_finsum {m : ℕ} {ι : Type} (s : Finset ι) (i : Fin m) (w : ι → Ext m) :
    wedge i (∑ k ∈ s, w k) = ∑ k ∈ s, wedge i (w k) := map_sum (wedgeR i) w s

theorem contr_finsum {m : ℕ} {ι : Type} (s : Finset ι) (i : Fin m) (w : ι → Ext m) :
    contr i (∑ k ∈ s, w k) = ∑ k ∈ s, contr i (w k) := map_sum (contrR i) w s

theorem d01_const_smul {g m : ℕ} (c : ℂ) {F : (Fin g → ℂ) → Ext m} {z : Fin g → ℂ}
    (hF : DifferentiableAt ℝ F z) (v : Fin g → ℂ) :
    d01 (fun z' => c • F z') z v = c • d01 F z v := by
  rw [d01_smul (φ := fun _ => c) (differentiableAt_const c) hF]
  simp [d01]

theorem anticomm {g : ℕ} (c d : Fin g) (Y : Ext (0 + 0 + g)) :
    wedge (dzb 0 d) (contr (dzb 0 c) Y) + contr (dzb 0 c) (wedge (dzb 0 d) Y) =
      if c = d then Y else 0 := by
  split_ifs with h
  · subst h; exact wedge_contr_add _ _
  · rw [wedge_contr_of_ne (fun e => h (dzb_bijective.1 e).symm)]; simp

theorem dbarF_dbarAdjF_add {g : ℕ} (G : Matrix (Fin g) (Fin g) ℂ) (ψ : (Fin g → ℂ) → ℂ)
    (f : (Fin g → ℂ) → Ext (0 + 0 + g)) (hf : Differentiable ℝ f) (hψ : Differentiable ℝ ψ)
    (hf01 : ∀ v, Differentiable ℝ (fun z => d01 f z v)) (hf10 : ∀ v, Differentiable ℝ (fun z => d10 f z v))
    (hψ10 : ∀ v, Differentiable ℝ (fun z => d10 ψ z v))
    (hmix : ∀ z v w, d01 (fun z' => d10 f z' v) z w = d10 (fun z' => d01 f z' w) z v)
    (z : Fin g → ℂ) :
    dbarF (dbarAdjF G ψ f) z + dbarAdjF G ψ (dbarF f) z =
      -(∑ a, ∑ c, G a c • (d10 (fun z' => d01 f z' (ev c)) z (ev a) + d10 ψ z (ev a) • d01 f z (ev c))) -
      ∑ a, ∑ c, ∑ d, (G a c * d01 (fun z' => d10 ψ z' (ev a)) z (ev d)) •
        wedge (dzb 0 d) (contr (dzb 0 c) (f z)) := by
  set X : Fin g → Fin g → Ext (0 + 0 + g) := fun a d =>
    d10 (fun z' => d01 f z' (ev d)) z (ev a) + d10 ψ z (ev a) • d01 f z (ev d) with hX
  have h1 : dbarAdjF G ψ (dbarF f) z =
      -∑ a, ∑ c, ∑ d, G a c • contr (dzb 0 c) (wedge (dzb 0 d) (X a d)) := by
    have e : ∀ a, d10 (dbarF f) z (ev a) + d10 ψ z (ev a) • dbarF f z =
        ∑ d, wedge (dzb 0 d) (X a d) := by
      intro a
      have : d10 (dbarF f) z (ev a) =
          ∑ d, wedge (dzb 0 d) (d10 (fun z' => d01 f z' (ev d)) z (ev a)) := by
        have := d10_finset_sum' Finset.univ (F := fun d z' => wedge (dzb 0 d) (d01 f z' (ev d))) (P := z)
          (fun d _ => (wedgeR (dzb 0 d)).differentiableAt.comp z (hf01 _ z)) (ev a)
        refine this.trans (Finset.sum_congr rfl fun d _ => ?_)
        exact dz_wedge_comm _ (hf01 _ z) _
      rw [this, dbarF, Finset.smul_sum, ← Finset.sum_add_distrib]
      simp only [hX, wedge_add, wedge_smul]
    simp only [dbarAdjF, e, contr_finsum, Finset.smul_sum]
  have hd : ∀ a, DifferentiableAt ℝ (fun z' => d10 f z' (ev a) + d10 ψ z' (ev a) • f z') z :=
    fun a => (hf10 _ z).add ((hψ10 _ z).smul (hf z))
  have hd2 : ∀ a c, DifferentiableAt ℝ
      (fun z' => contr (dzb 0 c) (d10 f z' (ev a) + d10 ψ z' (ev a) • f z')) z :=
    fun a c => (contrR (dzb 0 c)).differentiableAt.comp z (hd a)
  have hd3 : ∀ a c, DifferentiableAt ℝ
      (fun z' => G a c • contr (dzb 0 c) (d10 f z' (ev a) + d10 ψ z' (ev a) • f z')) z :=
    fun a c => (hd2 a c).const_smul (G a c)
  have h2 : ∀ d, d01 (dbarAdjF G ψ f) z (ev d) =
      -∑ a, ∑ c, G a c • contr (dzb 0 c)
        (X a d + d01 (fun z' => d10 ψ z' (ev a)) z (ev d) • f z) := by
    intro d
    have e0 : dbarAdjF G ψ f = fun z' => -∑ a, ∑ c,
        G a c • contr (dzb 0 c) (d10 f z' (ev a) + d10 ψ z' (ev a) • f z') := rfl
    rw [e0, d01_neg, d01_sum _ (fun a _ => DifferentiableAt.fun_sum fun c _ => hd3 a c)]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [d01_sum _ (fun c _ => hd3 a c)]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [d01_const_smul _ (hd2 a c), dbar_contraction_comm _ (hd a),
      dbar_add_vector (F := fun z' => d10 f z' (ev a)) (G := fun z' => d10 ψ z' (ev a) • f z')
        (hf10 _ z) ((hψ10 _ z).smul (hf z)), d01_smul (φ := fun z' => d10 ψ z' (ev a)) (hψ10 _ z) (hf z), hmix]
    simp only [hX]
    congr 2
    abel
  have h3 : dbarF (dbarAdjF G ψ f) z =
      -(∑ a, ∑ c, ∑ d, G a c • wedge (dzb 0 d) (contr (dzb 0 c) (X a d))) -
      ∑ a, ∑ c, ∑ d, (G a c * d01 (fun z' => d10 ψ z' (ev a)) z (ev d)) •
        wedge (dzb 0 d) (contr (dzb 0 c) (f z)) := by
    rw [dbarF]
    simp only [h2, wedge_neg, wedge_finsum, wedge_smul, contr_add, contr_smul, wedge_add,
      Finset.sum_neg_distrib]
    rw [Finset.sum_comm, sub_eq_add_neg, ← neg_add, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [smul_add, mul_smul]
  have h4 : (∑ a, ∑ c, ∑ d, G a c • wedge (dzb 0 d) (contr (dzb 0 c) (X a d))) +
      ∑ a, ∑ c, ∑ d, G a c • contr (dzb 0 c) (wedge (dzb 0 d) (X a d)) =
      ∑ a, ∑ c, G a c • X a c := by
    simp only [← Finset.sum_add_distrib, ← smul_add, anticomm, ← Finset.smul_sum,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [h1, h3, ← h4]
  abel

end GlobalTheory.TorsionForm.FlatAcyc.Cross
