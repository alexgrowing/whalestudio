import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.CochainExpansions.EtaExpand
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharExponentOfInfinityType

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.WigAlg Formalism.REAL
open scoped Classical

namespace PositivityTheory.Rg.Cz.Coch

open PositivityTheory.Rg.Cz

variable {E : Type} [Field E] [NumberField E] {a : ℕ}
variable {M : Type} [AddCommGroup M] [Module ℂ M] [Module ℝ M] [IsScalarTower ℝ ℂ M] {q N : ℕ}

def hY (τ : E →+* ℂ) (j i : Fin a) (z : ℂ) : Herm E a :=
  ⟨Matrix.single j i (atEmb τ z) + star (Matrix.single j i (atEmb τ z)), IsSelfAdjoint.add_star_self _⟩

omit [NumberField E] in
theorem hY_ent [IsTotallyComplex E] (τ τ' : E →+* ℂ) (h : τ' ≠ barE E τ) (j i j' i' : Fin a) :
    coord τ' ((hY τ j i (1 / 2)).1 j' i') - Complex.I * coord τ' ((hY τ j i (Complex.I / 2)).1 j' i') =
      if τ' = τ ∧ j' = j ∧ i' = i then 1 else 0 := by
  have hc : ∀ z, coord τ' (atEmb τ z) = if τ' = τ then z else 0 := fun z => by
    rw [GlobalTheory.CuspRep.InfType.coord_atEmb', if_neg h, add_zero]
  have he : ∀ z, coord τ' ((hY τ j i z).1 j' i') =
      (if j = j' ∧ i = i' then coord τ' (atEmb τ z) else 0) +
        (if j = i' ∧ i = j' then star (coord τ' (atEmb τ z)) else 0) := by
    intro z
    simp only [hY, Matrix.add_apply, Matrix.star_apply, Matrix.single_apply]
    rw [map_add]
    congr 1
    · split_ifs <;> simp
    · split_ifs <;> simp [PositivityTheory.Rg.Cz.J.coord_star]
  rw [he, he, hc, hc]
  clear he hc
  by_cases h1 : τ' = τ
  · subst h1
    clear h
    have hP : (τ' = τ' ∧ j' = j ∧ i' = i) ↔ (j = j' ∧ i = i') :=
      ⟨fun h => ⟨h.2.1.symm, h.2.2.symm⟩, fun h => ⟨rfl, h.1.symm, h.2.symm⟩⟩
    rw [if_congr hP rfl rfl]
    by_cases hp : j = j' ∧ i = i' <;> by_cases hq : j = i' ∧ i = j'
    · simp only [if_pos hp, if_pos hq]; simp [Complex.ext_iff]; norm_num
    · simp only [if_pos hp, if_neg hq]; simp [Complex.ext_iff]; norm_num
    · simp only [if_neg hp, if_pos hq]; simp [Complex.ext_iff]; norm_num
    · simp only [if_neg hp, if_neg hq]; simp
  · simp [h1]

theorem om_ne [IsTotallyComplex E] (tl : Fin N → (E →+* ℂ)) (η : TV a M (Fin q ⊕ (Fin N ⊕ Fin N)))
    (h1 : ∀ k k', tl k ≠ barE E (tl k')) (h3 : altPair tl η ≠ 0) : om tl η ≠ 0 := by
  intro h0
  apply h3
  funext J
  set I : Fin q → Fin a := fun p => J (Sum.inl p)
  set P : Fin N → Fin a := fun j => J (Sum.inr (Sum.inl j))
  set Q : Fin N → Fin a := fun j => J (Sum.inr (Sum.inr j))
  let A : Fin N → Herm E a := fun j => hY (tl j) (Q j) (P j) (1 / 2)
  let B : Fin N → Herm E a := fun j => hY (tl j) (Q j) (P j) (Complex.I / 2)
  have hz : cEv (fun v => om tl η v I) A B = 0 := by
    simp only [h0, AlternatingMap.zero_apply, Pi.zero_apply]
    exact cEv_zero (V := M) A B
  have e2 : ∀ A B : Fin N → Herm E a, cEv (fun v => mm tl η v I) A B = ∑ x : Fin N → Fin a, ∑ y : Fin N → Fin a,
      (∏ k, (coord (tl k) ((A k).1 (y k) (x k)) - Complex.I * coord (tl k) ((B k).1 (y k) (x k)))) •
        η (Sum.elim I (Sum.elim x y)) := fun A B => by
    have := cEv_prod2 (V := M) (fun x y k (h : Herm E a) => coord (tl k) (h.1 (y k) (x k)))
      (fun x y => η (Sum.elim I (Sum.elim x y))) A B
    rw [show (fun v => mm tl η v I) = fun v => ∑ x : Fin N → Fin a, ∑ y : Fin N → Fin a,
      (∏ k, (fun x y k (h : Herm E a) => coord (tl k) (h.1 (y k) (x k))) x y k (v k)) •
        (fun x y => η (Sum.elim I (Sum.elim x y))) x y from funext fun v => mm_apply tl η v I]
    exact this
  have e3 : ∀ σ : Equiv.Perm (Fin N), cEv (fun v => mm tl η (fun i => v (σ i)) I) A B =
      if ∀ k, tl k = tl (σ k) then η (Sum.elim I (Sum.elim (fun k => P (σ k)) (fun k => Q (σ k)))) else 0 := by
    intro σ
    rw [cEv_perm (V := M) (fun v => mm tl η v I), e2]
    have hp : ∀ x y : Fin N → Fin a, (∏ k, (coord (tl k) ((A (σ k)).1 (y k) (x k)) -
        Complex.I * coord (tl k) ((B (σ k)).1 (y k) (x k)))) =
        if (∀ k, tl k = tl (σ k)) ∧ x = (fun k => P (σ k)) ∧ y = (fun k => Q (σ k)) then 1 else 0 := by
      intro x y
      rw [Finset.prod_congr rfl fun k _ => hY_ent (tl (σ k)) (tl k) (h1 k (σ k)) (Q (σ k)) (P (σ k)) (y k) (x k),
        Finset.prod_boole]
      congr 1
      simp only [Finset.mem_univ, true_implies, funext_iff]
      exact propext ⟨fun h => ⟨fun k => (h k).1, fun k => (h k).2.2, fun k => (h k).2.1⟩,
        fun ⟨h1, h2, h3⟩ k => ⟨h1 k, h3 k, h2 k⟩⟩
    simp only [hp, ite_and, ite_smul, one_smul, zero_smul]
    by_cases hσ : ∀ k, tl k = tl (σ k)
    · simp only [eq_true hσ, if_true]
      rw [Fintype.sum_eq_single (fun k => P (σ k)) (fun x hx => by simp only [if_neg hx, Finset.sum_const_zero])]
      rw [Fintype.sum_eq_single (fun k => Q (σ k)) (fun y hy => by simp only [if_neg hy, ite_self])]
      simp only [if_true]
    · simp only [eq_false hσ, if_false, Finset.sum_const_zero]
  have hJ : ∀ σ : Equiv.Perm (Fin N), J ∘ dbl σ = Sum.elim I (Sum.elim (fun k => P (σ k)) (fun k => Q (σ k))) := by
    intro σ
    funext x
    rcases x with x | x | x <;> rfl
  symm
  rw [Pi.zero_apply, ← hz, show (fun v => om tl η v I) = fun v => ∑ σ : Equiv.Perm (Fin N),
    ((Equiv.Perm.sign σ : ℤ)) • mm tl η (fun i => v (σ i)) I from funext fun v => om_apply tl η v I, cEv_sum (V := M)]
  rw [altPair, LinearMap.sum_apply, Finset.sum_apply, colG, Finset.sum_filter]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [e3 σ]
  by_cases hσ : ∀ k, tl k = tl (σ k)
  · rw [if_pos hσ, if_pos fun p => (hσ p).symm, LinearMap.smul_apply, Pi.smul_apply, pm_apply, hJ,
      Int.cast_smul_eq_zsmul]
  · rw [if_neg hσ, if_neg fun h => hσ fun p => (h p).symm, smul_zero]

theorem cochain_holds : Cochain := by
  intro E _ _ _ a M _ _ _ _ ρ q N lab tl η h1 h2 h3
  exact ⟨om tl η, om_ne tl η h1 h3, om_cochain lab tl ρ η h2, fun p p' h X => om_swap tl η p p' h X⟩

end PositivityTheory.Rg.Cz.Coch

end
