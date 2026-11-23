import Development.WeilBound.CoreStatements.VolumeEquality.DegPushDefs
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PVandCount

noncomputable section

namespace SheetDecomposition

open MvPolynomial GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top

section Relabel

variable {Ψ Ψ' : Type} [Fintype Ψ] [DecidableEq Ψ] [Fintype Ψ'] [DecidableEq Ψ'] {N : ℕ} (e : Ψ ≃ Ψ')

theorem degFl_rename (F : RP Ψ N) : degFl (rename (e.prodCongr (Equiv.refl (Fin N))) F : RP Ψ' N) = degFl F := by
  unfold degFl
  have hd : dimFl Ψ' N = dimFl Ψ N := by
    unfold dimFl
    rw [Fintype.card_congr e]
  rw [hd, ← (Equiv.arrowCongr e (Equiv.refl (Equiv.Perm (Fin N)))).sum_comp]
  congr 1
  refine Finset.sum_congr rfl fun σ _ => ?_
  have hp : permExp ((Equiv.arrowCongr e (Equiv.refl (Equiv.Perm (Fin N)))) σ) =
      Finsupp.mapDomain (e.prodCongr (Equiv.refl (Fin N))) (permExp σ) := by
    ext ⟨τ', i⟩
    rw [Finsupp.mapDomain_equiv_apply]
    simp [permExp]
  rw [hp, coeff_rename_mapDomain _ (e.prodCongr (Equiv.refl (Fin N))).injective]
  congr 1
  exact Equiv.prod_comp e.symm (fun τ => ((Equiv.Perm.sign (σ τ) : ℤ) : ℝ))

theorem rename_muSmall (j : ℕ) : (rename (e.prodCongr (Equiv.refl (Fin N))) (muSmall j : RP Ψ N) : RP Ψ' N) = muSmall j := by
  unfold muSmall
  split_ifs
  · simp only [map_sum, rename_X, Equiv.prodCongr_apply, Prod.map_apply, Equiv.refl_apply]
    exact Fintype.sum_equiv e _ _ (fun _ => rfl)
  · simp only [pkLow, map_neg, map_sum, map_pow, rename_X, Equiv.prodCongr_apply, Prod.map_apply,
      Equiv.refl_apply]
    congr 1
    exact Fintype.sum_equiv e _ _ (fun _ => rfl)

theorem rename_fibClass (j : ℕ) : (rename (e.prodCongr (Equiv.refl (Fin N))) (fibClass j : RP Ψ N) : RP Ψ' N) = fibClass j := by
  unfold fibClass
  simp only [map_prod, map_sub, rename_X, Equiv.prodCongr_apply, Prod.map_apply, Equiv.refl_apply]
  exact Fintype.prod_equiv e _ _ (fun _ => rfl)

end Relabel

theorem testRelabel : TestRelabel := by
  intro Ψ _ _ N j
  unfold testDeg
  rw [← degFl_rename (Fintype.equivFin Ψ), map_mul, map_pow, rename_muSmall, rename_fibClass]
  simp [dimX]

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {p q : ℕ}

theorem count_pairs : Fintype.card Ψ * p * q + Fintype.card (PairIx Ψ p q) = dimFl Ψ (p + q) := by
  classical
  have hL : (Finset.univ.filter fun ab : Fin (p + q) × Fin (p + q) => ab.1 < ab.2).card =
      (p + q) * (p + q - 1) / 2 := by
    rw [Finset.card_filter, Fintype.sum_prod_type, Finset.sum_comm, ← Finset.sum_range_id,
      ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← Finset.card_filter, Finset.filter_gt_eq_Iio, Fin.card_Iio]
  have hC : ((Finset.univ.filter fun ab : Fin (p + q) × Fin (p + q) => ab.1 < ab.2).filter
      fun ab => ¬ ((ab.1 : ℕ) < p ↔ (ab.2 : ℕ) < p)).card = p * q := by
    have e : ((Finset.univ.filter fun ab : Fin (p + q) × Fin (p + q) => ab.1 < ab.2).filter
        fun ab => ¬ ((ab.1 : ℕ) < p ↔ (ab.2 : ℕ) < p)) =
        (Finset.univ.filter fun a : Fin (p + q) => (a : ℕ) < p) ×ˢ
          (Finset.univ.filter fun b : Fin (p + q) => ¬ (b : ℕ) < p) := by
      ext ⟨a, b⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product, Fin.lt_iff_val_lt_val]
      omega
    have h1 : (Finset.univ.filter fun a : Fin (p + q) => (a : ℕ) < p).card = p := by
      rw [Fin.card_filter_val_lt]
      omega
    have h2 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin (p + q))))
      (fun a : Fin (p + q) => (a : ℕ) < p)
    rw [h1, Finset.card_univ, Fintype.card_fin] at h2
    rw [e, Finset.card_product, h1]
    congr 1
    omega
  have hS : Fintype.card {ab : Fin (p + q) × Fin (p + q) // ab.1 < ab.2 ∧ ((ab.1 : ℕ) < p ↔ (ab.2 : ℕ) < p)} +
      p * q = (p + q) * (p + q - 1) / 2 := by
    rw [Fintype.card_subtype, ← hL, ← hC, ← Finset.filter_filter]
    exact Finset.card_filter_add_card_filter_not _
  rw [Fintype.card_prod]
  unfold dimFl
  rw [← hS]
  ring

def muCoef (Ψ : Type) (p q : ℕ) : Ψ × Fin (p + q) → ℤ := fun x => if p ≤ (x.2 : ℕ) then 1 else 0

def fibCoef (t : PairIx Ψ p q) : Ψ × Fin (p + q) → ℤ := fun x =>
  (if x = (t.1, t.2.1.2) then 1 else 0) - if x = (t.1, t.2.1.1) then 1 else 0

theorem sum_muCoef {A : Type} [AddCommGroup A] (x : Ψ × Fin (p + q) → A) :
    ∑ r, muCoef Ψ p q r • x r = ∑ τ, ∑ i ∈ Finset.univ.filter (fun i : Fin (p + q) => p ≤ (i : ℕ)), x (τ, i) := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [muCoef]
  split_ifs <;> simp

theorem sum_fibCoef {A : Type} [AddCommGroup A] (x : Ψ × Fin (p + q) → A) (t : PairIx Ψ p q) :
    ∑ r, fibCoef t r • x r = x (t.1, t.2.1.2) - x (t.1, t.2.1.1) := by
  simp [fibCoef, sub_smul, Finset.sum_sub_distrib, ite_smul]

theorem test_factor {n r : ℕ} (e : Fin r ≃ PairIx Ψ p q) (hq : q ≤ p) (hn : n = Fintype.card Ψ * p * q) :
    (muSmall p ^ dimX Ψ (p + q) p * fibClass p : RP Ψ (p + q)) =
      ∏ j : Fin (n + r), ∑ x, Fin.append (fun _ : Fin n => muCoef Ψ p q) (fun j => fibCoef (e j)) j x • X x := by
  have hN : p + q - p ≤ p := by omega
  have hmu : (muSmall p : RP Ψ (p + q)) = ∑ x, muCoef Ψ p q x • (X x : RP Ψ (p + q)) := by
    rw [sum_muCoef (X : Ψ × Fin (p + q) → RP Ψ (p + q))]
    unfold muSmall
    rw [if_pos hN]
  have hdim : dimX Ψ (p + q) p = n := by
    unfold dimX
    rw [hn, Nat.add_sub_cancel_left]
    ring
  have hfib : (fibClass p : RP Ψ (p + q)) = ∏ i : Fin r, ∑ x, fibCoef (e i) x • (X x : RP Ψ (p + q)) := by
    simp only [sum_fibCoef]
    rw [Fintype.prod_equiv e _ (fun t : PairIx Ψ p q => (X (t.1, t.2.1.2) - X (t.1, t.2.1.1) : RP Ψ (p + q)))
      (fun _ => rfl)]
    unfold fibClass
    rw [Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [← Finset.prod_subtype_eq_prod_filter, Finset.subtype_univ]
    try rfl
  rw [Fin.prod_univ_add, hmu, hdim, hfib]
  simp only [Fin.append_left, Fin.append_right, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end SheetDecomposition
