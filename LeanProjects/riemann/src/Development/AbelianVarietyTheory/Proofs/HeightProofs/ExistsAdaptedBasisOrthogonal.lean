import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsOrthogonalBasisDotProductApplyEq
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockCompare

theorem exists_orthogonal_basis_mem_or_mem {E V : Type} [Field E] {c : E →+* E} [AddCommGroup V]
    [Module E V] [FiniteDimensional E V] (h2 : (2 : E) ≠ 0) (B : V →ₗ[E] V →ₛₗ[c] E)
    (hB : ∀ x y, c (B x y) = B y x) {P N : Submodule E V} (hc : IsCompl P N)
    (ho : ∀ x ∈ P, ∀ y ∈ N, B y x = 0) {n : ℕ} (hn : Module.finrank E V = n) :
    ∃ b : Module.Basis (Fin n) E V, (∀ i j, i ≠ j → B (b i) (b j) = 0) ∧ ∀ i, b i ∈ P ∨ b i ∈ N := by
  obtain ⟨u, hu⟩ := GlobalTheory.HermDiag.exists_orthogonal_basis_fin h2 _ (B.domRestrict₁₂ P P)
    (fun y z => hB y z) rfl
  obtain ⟨v, hv⟩ := GlobalTheory.HermDiag.exists_orthogonal_basis_fin h2 _ (B.domRestrict₁₂ N N)
    (fun y z => hB y z) rfl
  let w := (u.prod v).map (Submodule.prodEquivOfIsCompl P N hc)
  have hl : ∀ i, w (Sum.inl i) = u i := fun i => by
    simp [w, Module.Basis.prod_apply]
  have hr : ∀ i, w (Sum.inr i) = v i := fun i => by
    simp [w, Module.Basis.prod_apply]
  have hcard : Fintype.card (Fin (Module.finrank E P) ⊕ Fin (Module.finrank E N)) = n := by
    rw [← hn, Module.finrank_eq_card_basis w]
  have hw : ∀ i j, i ≠ j → B (w i) (w j) = 0 := by
    rintro (i | i) (j | j) hij
    · rw [hl, hl]; exact hu i j fun h => hij (by rw [h])
    · rw [hl, hr, ← hB, ho _ (u i).2 _ (v j).2, map_zero]
    · rw [hl, hr]; exact ho _ (u j).2 _ (v i).2
    · rw [hr, hr]; exact hv i j fun h => hij (by rw [h])
  refine ⟨w.reindex (Fintype.equivFinOfCardEq hcard), fun i j hij => ?_, fun i => ?_⟩
  · simp only [Module.Basis.reindex_apply]
    exact hw _ _ fun h => hij (Equiv.injective _ h)
  · rw [Module.Basis.reindex_apply]
    rcases (Fintype.equivFinOfCardEq hcard).symm i with k | k
    · rw [hl]; exact Or.inl (u k).2
    · rw [hr]; exact Or.inr (v k).2

theorem exists_adapted_of_isOrthDec : ∀ (D : D7) (V : HSp D) (s : InvFam V) (P N : Submodule D.host.E V.V) (τ₀ : D.what₂.Tau), IsOrthDec V τ₀ P N → (∀ τ, (∀ x ∈ P, s τ x = x) ∧ ∀ x ∈ N, s τ x = -x) → ∃ b : Module.Basis (Fin V.rank) D.host.E V.V, Adapted V b s := by
  intro D V s P N τ₀ h hs
  obtain ⟨b, hb, hm⟩ := exists_orthogonal_basis_mem_or_mem two_ne_zero V.hT.flip
    (fun x y => V.herm.eq y x) h.compl (fun x hx y hy => h.orth x hx y hy) V.rank_eq
  refine ⟨b, fun i j hij => hb j i hij.symm, fun τ i => ?_⟩
  exact (hm i).imp ((hs τ).1 _) ((hs τ).2 _)

end GlobalTheory.FockCompare
