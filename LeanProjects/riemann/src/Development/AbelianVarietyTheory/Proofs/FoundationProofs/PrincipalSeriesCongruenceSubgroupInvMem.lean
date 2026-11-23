import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.OrderedConst
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsTrivialOnUnitsModConductorUnitCharacterValuePr

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

noncomputable section

namespace GlobalTheory.PsType

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

def congrAlg (ψ : Fin n → kˣ →* ℂˣ) (hψ : Ordered ψ) :
    Subalgebra 𝒪[k] (Matrix (Fin n) (Fin n) 𝒪[k]) where
  carrier := {M | ∀ i j : Fin n, i < j → Triv (ψ i / ψ j) ((M i j : 𝒪[k]) : k)}
  mul_mem' := by
    intro A B hA hB i j hij
    simp only [Set.mem_setOf_eq] at hA hB
    rw [Matrix.mul_apply]
    push_cast
    refine Finset.sum_induction _ (fun x => Triv (ψ i / ψ j) x) (fun x y hx hy => triv_add _ x y hx hy)
      (triv_zero _) ?_
    intro l _
    have hAv : valuation k ((A i l : 𝒪[k]) : k) ≤ 1 := (A i l).2
    have hBv : valuation k ((B l j : 𝒪[k]) : k) ≤ 1 := (B l j).2
    have h1 : valuation k ((A i l : 𝒪[k]) : k) * valuation k ((B l j : 𝒪[k]) : k) ≤
        valuation k ((B l j : 𝒪[k]) : k) := mul_le_of_le_one_left' hAv
    have h2 : valuation k ((A i l : 𝒪[k]) : k) * valuation k ((B l j : 𝒪[k]) : k) ≤
        valuation k ((A i l : 𝒪[k]) : k) := mul_le_of_le_one_right' hBv
    rcases le_or_gt l i with hli | hil
    · refine triv_mono _ ((B l j : 𝒪[k]) : k) _ (by rw [map_mul]; exact h1) ?_
      exact hψ l i j j hli hij.le le_rfl _ (hB l j (lt_of_le_of_lt hli hij))
    rcases le_or_gt j l with hjl | hlj
    · refine triv_mono _ ((A i l : 𝒪[k]) : k) _ (by rw [map_mul]; exact h2) ?_
      exact hψ i i j l le_rfl hij.le hjl _ (hA i l hil)
    · have e : ψ i / ψ l * (ψ l / ψ j) = ψ i / ψ j := div_mul_div_cancel _ _ _
      rw [← e]
      exact triv_mul _ _ _ (triv_mono _ ((A i l : 𝒪[k]) : k) _ (by rw [map_mul]; exact h2) (hA i l hil))
        (triv_mono _ ((B l j : 𝒪[k]) : k) _ (by rw [map_mul]; exact h1) (hB l j hlj))
  one_mem' := by
    intro i j hij
    simp [Matrix.one_apply_ne hij.ne, triv_zero]
  add_mem' := by
    intro A B hA hB i j hij
    simp only [Set.mem_setOf_eq] at hA hB
    simpa using triv_add _ _ _ (hA i j hij) (hB i j hij)
  zero_mem' := by
    intro i j hij
    simp [triv_zero]
  algebraMap_mem' := by
    intro c i j hij
    simp [Matrix.algebraMap_eq_diagonal, Matrix.diagonal_apply_ne _ hij.ne, triv_zero]

theorem inv_val_mem_adjoin {R : Type} [CommRing R] {m : ℕ} (g : GL (Fin m) R) :
    ((g⁻¹ : GL (Fin m) R) : Matrix (Fin m) (Fin m) R) ∈ Algebra.adjoin R {(g : Matrix (Fin m) (Fin m) R)} := by
  set A : Matrix (Fin m) (Fin m) R := (g : Matrix (Fin m) (Fin m) R)
  set p := A.charpoly
  have hCH : Polynomial.aeval A p = 0 := Matrix.aeval_self_charpoly A
  have hdec : p.divX * Polynomial.X + Polynomial.C (p.coeff 0) = p := Polynomial.divX_mul_X_add p
  have hdet : A.det = (-1) ^ Fintype.card (Fin m) * p.coeff 0 := Matrix.det_eq_sign_charpoly_coeff A
  have hu : IsUnit (p.coeff 0) := by
    have h := (Matrix.isUnit_iff_isUnit_det A).mp (Units.isUnit g)
    rw [hdet] at h
    exact isUnit_of_mul_isUnit_right h
  obtain ⟨u, hu⟩ := hu
  have h1 : Polynomial.aeval A p.divX * A = -algebraMap R _ (p.coeff 0) := by
    rw [← hdec] at hCH
    simp only [map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C] at hCH
    exact eq_neg_of_add_eq_zero_left hCH
  have key : ((-(↑u⁻¹ : R)) • Polynomial.aeval A p.divX) * A = 1 := by
    rw [smul_mul_assoc, h1, Algebra.algebraMap_eq_smul_one, ← hu, neg_smul_neg, smul_smul,
      Units.inv_mul, one_smul]
  have e : ((g⁻¹ : GL (Fin m) R) : Matrix (Fin m) (Fin m) R) = (-(↑u⁻¹ : R)) • Polynomial.aeval A p.divX :=
    Units.inv_eq_of_mul_eq_one_left key
  rw [e]
  exact Subalgebra.smul_mem _ (Polynomial.aeval_mem_adjoin_singleton R A) _

end GlobalTheory.PsType

open GlobalTheory.PsType in

theorem GlobalTheory.PsType.grp_inv_mem : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ), Ordered ψ → ∀ a ∈ grp ψ, a⁻¹ ∈ grp ψ := by
  intro k _ _ _ _ n ψ hψ a ha
  obtain ⟨haK, hat⟩ := ha
  obtain ⟨g, rfl⟩ := haK
  have hg : (g : Matrix (Fin n) (Fin n) 𝒪[k]) ∈ congrAlg ψ hψ := fun i j hij => hat i j hij
  have hinv : ((g⁻¹ : GL (Fin n) 𝒪[k]) : Matrix (Fin n) (Fin n) 𝒪[k]) ∈ congrAlg ψ hψ :=
    Algebra.adjoin_le (Set.singleton_subset_iff.mpr hg) (inv_val_mem_adjoin g)
  refine ⟨inv_mem ⟨g, rfl⟩, ?_⟩
  intro i j hij
  rw [← map_inv]
  exact hinv i j hij
