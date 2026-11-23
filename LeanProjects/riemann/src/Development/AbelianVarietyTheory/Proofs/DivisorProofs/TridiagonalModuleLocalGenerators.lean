import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TriModOfBlockTriangular
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx GlobalTheory.ConstLat GlobalTheory.LatChain Filter Topology
open scoped Classical

set_option autoImplicit false

namespace GlobalTheory.LatChain

theorem lc_gens_of_triMod : ∀ (K : Type) [Field K] (N : ℕ) (R : Subring K) (γ b : K) (A : Matrix (Fin N) (Fin N) K)
    (d y : Fin N → K), γ ∈ R → b ∈ R → A ∈ R.matrix → (∀ l, y l ∈ R) → TriMod R (γ * b) A d →
    (∀ i : Fin N, d i ∈ R ∧ Lc R (gens γ y i.succ) ((A.mulVec y) i - d i * y i)) ∧
      ∀ i s, Lc R (gens γ y i) (gens γ (A.mulVec y) i s) := by
  intro K _ N R γ b A d y hγ hb hA hy hT
  obtain ⟨E, hE, htri, hdiag⟩ := hT
  have hτR : ∀ k l, (A - (γ * b) • E) k l ∈ R := fun k l => by
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    exact R.sub_mem (hA k l) (R.mul_mem (R.mul_mem hγ hb) (hE k l))
  have hEy : ∀ k, b * (E.mulVec y) k ∈ R := fun k => by
    refine R.mul_mem hb ?_
    simp only [Matrix.mulVec, dotProduct]
    exact R.sum_mem fun l _ => R.mul_mem (hE k l) (hy l)
  have hlow : ∀ k l, l < k → (A - (γ * b) • E) k l = 0 := fun k l h => htri h
  have hAy : ∀ k, (A.mulVec y) k = ∑ l, (A - (γ * b) • E) k l * y l + γ * (b * (E.mulVec y) k) := fun k => by
    simp only [Matrix.mulVec, dotProduct, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun l _ => by ring
  refine ⟨fun i => ⟨hdiag i ▸ hτR i i, ?_⟩, fun i s => ?_⟩
  · refine ⟨fun s => s.elim (b * (E.mulVec y) i) fun l => (A - (γ * b) • E) i l,
      fun s => by cases s with | none => exact hEy i | some l => exact hτR i l, ?_⟩
    rw [Fintype.sum_option]
    simp only [gens, Option.elim_none, Option.elim_some]
    have key : ∀ l, (A - (γ * b) • E) i l * y l = (A - (γ * b) • E) i l * (if ((i.succ : Fin (N + 1)) : ℕ) ≤ l then y l else 0)
        + if l = i then (A - (γ * b) • E) i i * y i else 0 := by
      intro l
      rcases lt_trichotomy l i with h | h | h
      · rw [hlow i l h]; simp [h.ne]
      · subst h; simp
      · have h' : ((i.succ : Fin (N + 1)) : ℕ) ≤ l := by rw [Fin.val_succ]; exact h
        rw [if_pos h', if_neg h.ne', add_zero]
    rw [hAy i, Finset.sum_congr rfl fun l _ => key l, Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ i,
      if_pos (Finset.mem_univ _), ← hdiag i]
    ring
  · cases s with
    | none =>
      refine ⟨fun s => s.elim 1 fun _ => 0, fun s => by cases s with | none => exact R.one_mem | some _ => exact R.zero_mem, ?_⟩
      simp [Fintype.sum_option, gens]
    | some k =>
      by_cases hik : (i : ℕ) ≤ k
      · refine ⟨fun s => s.elim (b * (E.mulVec y) k) fun l => (A - (γ * b) • E) k l,
          fun s => by cases s with | none => exact hEy k | some l => exact hτR k l, ?_⟩
        rw [Fintype.sum_option]
        simp only [gens, Option.elim_none, Option.elim_some, if_pos hik]
        have key : ∀ l, (A - (γ * b) • E) k l * (if (i : ℕ) ≤ l then y l else 0) = (A - (γ * b) • E) k l * y l := by
          intro l
          by_cases hil : (i : ℕ) ≤ l
          · rw [if_pos hil]
          · rw [if_neg hil, hlow k l (by rw [Fin.lt_def]; omega)]; simp
        rw [hAy k, Finset.sum_congr rfl fun l _ => key l]
        ring
      · refine ⟨fun _ => 0, fun _ => R.zero_mem, ?_⟩
        simp [gens, hik]

end GlobalTheory.LatChain
