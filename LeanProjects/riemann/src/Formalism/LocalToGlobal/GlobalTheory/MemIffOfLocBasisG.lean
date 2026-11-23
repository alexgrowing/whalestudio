import Formalism.LocalToGlobal.GlobalTheory.ActAllMemIntSpanAtG

open MvPolynomial

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.ColValS

open Formalism.BasicNotions Formalism.MainNotions.flipTwoThree

theorem subAll_comp {K : Type} [Field K] {ι : Type} {n : ℕ} (g h : ι → Matrix (Fin n) (Fin n) K)
    (p : MvPolynomial (ι × Fin n × Fin n) K) :
    subAll g (subAll h p) = subAll (fun τ => g τ * h τ) p := by
  have : (subAll g).comp (subAll h) = subAll (fun τ => g τ * h τ) := by
    apply MvPolynomial.algHom_ext
    intro v
    obtain ⟨τ, a, c⟩ := v
    simp only [AlgHom.comp_apply, subAll, aeval_X, map_sum, map_mul, aeval_C, MvPolynomial.algebraMap_eq,
      Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun b _ => ?_))
    first | ring | (rw [C_mul]; ring)
  exact congrArg (fun φ => φ p) this

theorem actAll_comp {K : Type} [Field K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n)
    (g h : ι → Matrix (Fin n) (Fin n) K) (p : MvPolynomial (ι × Fin n × Fin n) K) :
    actAll lam g (actAll lam h p) = actAll lam (fun τ => g τ * h τ) p := by
  have e1 : ∀ (g : ι → Matrix (Fin n) (Fin n) K) q,
      actAll lam g q = (∏ τ, (g τ).det ^ (lam τ).detShift) • subAll g q := fun _ _ => rfl
  rw [e1, e1, e1, map_smul, subAll_comp, smul_smul]
  congr 1
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun τ _ => ?_)
  rw [Matrix.det_mul, mul_zpow]

section Change

variable {LL : Type} [Field LL] [NumberField LL] [StarRing LL] (Pl : Rows.Places LL) (w : Pl.Pl) {n : ℕ}
  (Q : HLat LL) (e : Q.ι ≃ Fin n)

theorem exists_change (γ γ' : Matrix (Fin n) (Fin n) LL) (h : LocBasisG Pl w Q e γ) (h' : LocBasisG Pl w Q e γ') :
    ∃ k : Matrix (Fin n) (Fin n) (intW Pl w), γ = γ' * k.map (intW Pl w).subtype := by
  have hv : ∀ a, (∑ i, γ i a • Q.b (e.symm i)) ∈
      Submodule.span (intW Pl w) (Set.range fun a : Fin n => ∑ i, γ' i a • Q.b (e.symm i)) := by
    intro a
    rw [← h'.2, h.2]
    exact Submodule.subset_span ⟨a, rfl⟩
  choose c hc using fun a => (Submodule.mem_span_range_iff_exists_fun (intW Pl w)).1 (hv a)
  refine ⟨Matrix.of fun b a => c a b, ?_⟩
  have li : LinearIndependent LL (fun i => Q.b (e.symm i)) := Q.b.linearIndependent.comp e.symm e.symm.injective
  ext i a
  have e2 : ∑ i, (γ' * (Matrix.of fun b a => c a b).map (intW Pl w).subtype) i a • Q.b (e.symm i) =
      ∑ b, c a b • ∑ i, γ' i b • Q.b (e.symm i) := by
    simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply, Finset.sum_smul, Finset.smul_sum, smul_smul,
      Subring.smul_def, Subring.coe_subtype]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun j _ => ?_))
    rw [mul_comm]
  have key : ∑ i, (γ i a - (γ' * (Matrix.of fun b a => c a b).map (intW Pl w).subtype) i a) • Q.b (e.symm i) = 0 := by
    rw [Finset.sum_congr rfl (fun i _ => sub_smul _ _ _), Finset.sum_sub_distrib, e2, hc a, sub_self]
  exact sub_eq_zero.1 ((Fintype.linearIndependent_iff.1 li) _ key i)

theorem exists_change_inv (γ γ' : Matrix (Fin n) (Fin n) LL) (h : LocBasisG Pl w Q e γ)
    (h' : LocBasisG Pl w Q e γ') :
    ∃ k : Matrix (Fin n) (Fin n) (intW Pl w), IsUnit k.det ∧ γ'⁻¹ = k.map (intW Pl w).subtype * γ⁻¹ := by
  obtain ⟨k, hk⟩ := exists_change Pl w Q e γ γ' h h'
  obtain ⟨k2, hk2⟩ := exists_change Pl w Q e γ' γ h' h
  have hkk : k2 * k = 1 := by
    have h1 : γ * ((k2 * k).map (intW Pl w).subtype) = γ * 1 := by
      rw [Matrix.map_mul, ← Matrix.mul_assoc, ← hk2, ← hk, Matrix.mul_one]
    have h2 := congrArg (fun M => γ⁻¹ * M) h1
    simp only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ h.1, Matrix.one_mul] at h2
    apply Matrix.map_injective Subtype.val_injective
    exact h2.trans (Matrix.map_one _ rfl rfl).symm
  refine ⟨k, IsUnit.of_mul_eq_one k2.det ?_, ?_⟩
  · rw [mul_comm, ← Matrix.det_mul, hkk, Matrix.det_one]
  · calc γ'⁻¹ = γ'⁻¹ * (γ * γ⁻¹) := by rw [Matrix.mul_nonsing_inv _ h.1, Matrix.mul_one]
      _ = γ'⁻¹ * (γ' * k.map (intW Pl w).subtype) * γ⁻¹ := by rw [← hk, Matrix.mul_assoc]
      _ = k.map (intW Pl w).subtype * γ⁻¹ := by
        rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ h'.1, Matrix.one_mul]

end Change

theorem mem_iff_of_locBasisG {LL : Type} [Field LL] [NumberField LL] [StarRing LL] (Pl : Rows.Places LL) {Tau : Type}
    [Fintype Tau] (w : Pl.Pl) {n : ℕ} (lam : Tau → DomWeight n) (Q : Tau → HLat LL) (e : ∀ τ, (Q τ).ι ≃ Fin n)
    (γ γ' : Tau → Matrix (Fin n) (Fin n) LL) (h : ∀ τ, LocBasisG Pl w (Q τ) (e τ) (γ τ))
    (h' : ∀ τ, LocBasisG Pl w (Q τ) (e τ) (γ' τ)) (p : MvPolynomial (Tau × Fin n × Fin n) LL) :
    actAll lam (fun τ => (γ τ)⁻¹) p ∈ IntSpanAtG Pl w lam ↔ actAll lam (fun τ => (γ' τ)⁻¹) p ∈ IntSpanAtG Pl w lam := by
  have one : ∀ (γ γ' : Tau → Matrix (Fin n) (Fin n) LL), (∀ τ, LocBasisG Pl w (Q τ) (e τ) (γ τ)) →
      (∀ τ, LocBasisG Pl w (Q τ) (e τ) (γ' τ)) →
      actAll lam (fun τ => (γ τ)⁻¹) p ∈ IntSpanAtG Pl w lam → actAll lam (fun τ => (γ' τ)⁻¹) p ∈ IntSpanAtG Pl w lam := by
    intro γ γ' h h' hp
    choose k hk hkγ using fun τ => exists_change_inv Pl w (Q τ) (e τ) (γ τ) (γ' τ) (h τ) (h' τ)
    rw [show (fun τ => (γ' τ)⁻¹) = fun τ => (k τ).map (intW Pl w).subtype * (γ τ)⁻¹ from funext hkγ, ← actAll_comp]
    exact actAll_mem_intSpanAtG Pl w lam k hk hp
  exact ⟨one γ γ' h h', one γ' γ h' h⟩

theorem mem_iff_of_locBasis (D : D7) (w : D.what₂.places.Pl) {n : ℕ} (lam : D.what₂.Tau → DomWeight n)
    (Q : D.what₂.Tau → HLat D.what₂.LL) (e : ∀ τ, (Q τ).ι ≃ Fin n) (γ γ' : D.what₂.Tau → Matrix (Fin n) (Fin n) D.what₂.LL)
    (h : ∀ τ, LocBasis D w (Q τ) (e τ) (γ τ)) (h' : ∀ τ, LocBasis D w (Q τ) (e τ) (γ' τ))
    (p : MvPolynomial (D.what₂.Tau × Fin n × Fin n) D.what₂.LL) :
    actAll lam (fun τ => (γ τ)⁻¹) p ∈ IntSpanAt D w lam ↔ actAll lam (fun τ => (γ' τ)⁻¹) p ∈ IntSpanAt D w lam :=
  mem_iff_of_locBasisG D.what₂.places w lam Q e γ γ' h h' p

end Formalism.L2.GlobalTheoryTheory.ColValS
