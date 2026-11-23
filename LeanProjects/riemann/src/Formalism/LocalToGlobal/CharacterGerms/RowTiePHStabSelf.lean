import Formalism.LocalToGlobal.CharacterGerms.RowTiePHStab
import Formalism.LocalToGlobal.CharacterGerms.RowTiePCartSelfSt

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ MvPowerSeries

variable {C : Type} [Field C]

section Rename₂

theorem coeff_rename_outside {σ τ : Type} [Finite σ] (φ : σ → τ) (F : MvPowerSeries σ C) (ν : τ →₀ ℕ) {s : τ}
    (hs : ν s ≠ 0) (hr : ∀ x, φ x ≠ s) :
    coeff ν (MvPowerSeries.subst (fun x => (X (φ x) : MvPowerSeries τ C)) F) = 0 := by
  refine coeff_subst_rename_out φ F ν fun e' he => hs ?_
  rw [← he]
  exact Finsupp.mapDomain_notin_range _ _ (by rintro ⟨x, hx⟩; exact hr x hx)

variable {dd : ℕ}

theorem coeff_hCol (h : PS C 2 dd) (col c1 c2 : Fin 2) (i j : Fin dd) :
    coeff (E2 ((0 : Fin 2), (c1, i)) ((1 : Fin 2), (c2, j))) (hCol col h) =
      if c1 = col ∧ c2 = col then coeff (E2 ((0 : Fin 2), i) ((1 : Fin 2), j)) h else 0 := by
  unfold hCol
  split_ifs with hc
  · obtain ⟨h1, h2⟩ := hc
    rw [h1, h2]
    have hφ : Function.Injective (fun p : Fin 2 × Fin dd => (p.1, (col, p.2))) := by
      intro a b hab
      simp only [Prod.mk.injEq] at hab
      exact Prod.ext hab.1 hab.2.2
    have he : E2 ((0 : Fin 2), (col, i)) ((1 : Fin 2), (col, j)) =
        (E2 ((0 : Fin 2), i) ((1 : Fin 2), j)).mapDomain (fun p : Fin 2 × Fin dd => (p.1, (col, p.2))) := by
      simp [E2, Finsupp.mapDomain_add, Finsupp.mapDomain_single]
    rw [he, coeff_subst_rename_inj _ hφ]
  · by_cases h1 : c1 = col
    · have h2 : c2 ≠ col := fun h2 => hc ⟨h1, h2⟩
      refine coeff_rename_outside _ h (E2 _ _) (s := ((1 : Fin 2), (c2, j))) ?_ ?_
      · simp [E2, Finsupp.single_apply]
      · intro x hx
        simp only [Prod.mk.injEq] at hx
        exact h2 hx.2.1.symm
    · refine coeff_rename_outside _ h (E2 _ _) (s := ((0 : Fin 2), (c1, i))) ?_ ?_
      · simp [E2, Finsupp.single_apply]
      · intro x hx
        simp only [Prod.mk.injEq] at hx
        exact h1 hx.2.1.symm

end Rename₂

section Self

variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} {I0 : Type} [Fintype I0]

theorem coeff_E2_sum_hCol_eq_ite (h : PS C 2 dd) (c1 c2 : Fin 2) (i j : Fin dd) :
    coeff (E2 ((0 : Fin 2), (c1, i)) ((1 : Fin 2), (c2, j))) (∑ col, hCol col h) =
      if c1 = c2 then coeff (E2 ((0 : Fin 2), i) ((1 : Fin 2), j)) h else 0 := by
  rw [map_sum]
  simp only [coeff_hCol]
  rw [Fin.sum_univ_two]
  by_cases h12 : c1 = c2
  · subst h12
    fin_cases c1 <;> simp
  · fin_cases c1 <;> fin_cases c2 <;> simp_all

theorem FBChart.self_raw_first_pairing_eq (Y : FBChart C V O dd) (p : SelfData Y d I0) (w v : Fin 2 × Fin dd → C) :
    (Y.rawSelf p).sg1 w v = -∑ col, bil Y.h (fun i => w (col, i)) (fun j => v (col, j)) := by
  have hsg : ∀ x : Fin 2 × Fin dd, MvPowerSeries.coeff (Finsupp.single x 1) ((Y.rawSelf p).sg v) =
      -∑ i : Fin 2 × Fin dd, v i *
        (if x.1 = i.1 then MvPowerSeries.coeff (E2 ((0 : Fin 2), x.2) ((1 : Fin 2), i.2)) Y.h else 0) := by
    intro x
    show (-∑ i, v i * MvPowerSeries.coeff ((Finsupp.single x 1).mapDomain (fun y => ((0 : Fin 2), y)) +
      Finsupp.single ((1 : Fin 2), i) 1) (∑ col, hCol col Y.h)) = _
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finsupp.mapDomain_single]
    rw [show Finsupp.single ((0 : Fin 2), x) 1 + Finsupp.single ((1 : Fin 2), i) 1 =
      E2 ((0 : Fin 2), (x.1, x.2)) ((1 : Fin 2), (i.1, i.2)) from rfl, coeff_E2_sum_hCol_eq_ite]
  simp only [RawChart.sg1, hsg, bil, Fintype.sum_prod_type, Fin.sum_univ_two]
  simp only [Fin.isValue, if_true, zero_ne_one, one_ne_zero, if_false, mul_zero, Finset.sum_const_zero,
    add_zero, zero_add, Finset.mul_sum, mul_neg, Finset.sum_neg_distrib, neg_add]
  congr 1 <;> (congr 1; exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring)

end Self

theorem hStabSelf_holds : HStabSelfSt := by
  intro C _ _ V O _ _ dd Y d _ I0 _ p g c q hty
  have hne : p.ty0 c ≠ p.ty0 q + p.hd := by
    rcases fin_two_eq_zero_or_eq_one g with rfl | rfl
    · exact hty
    · intro e
      apply hty
      show p.ty0 c + p.hd = p.ty0 q
      rw [e, add_assoc, p.hd_two, add_zero]
  obtain ⟨a, ha⟩ := p.em_sep _ _ hne
  have hb := Y.bil_ad a (p.e c) (p.e q)
  rw [p.e_eig c a, p.e_eig q (star a), p.em_conj, bil_smul_left, bil_smul_right, ← sub_mul] at hb
  have hint : V.Ge 0 (bil (Y.B.ad a) (p.e c) (p.e q)) := bil_int (Y.intAd a) (p.e_int c) (p.e_int q)
  rw [hb] at hint
  have hβ : V.Ge 0 (bil Y.h (p.e c) (p.e q)) := by
    unfold VF.Ge at hint ⊢
    rwa [V.v.map_mul, ha, zero_add] at hint
  have hgm : ∀ a r s, V.Ge 0 (p.gm a r s) := by
    obtain ⟨M, hM⟩ := p.gm_lim 0
    intro a r s
    have h1 : V.Ge 0 (p.gm a r s - p.em a (M r s)) := by simpa using hM a r s
    have h2 := h1.add (p.em_int a (M r s))
    simpa using h2
  show V.Ge 0 ((Y.rawSelf p).sg1 (fun x => p.gm (p.ty0 c) x.1 g * p.e c x.2)
    (fun x => p.gm (p.ty0 q) x.1 (1 - g) * p.e q x.2))
  rw [Y.self_raw_first_pairing_eq]
  apply VF.Ge.neg
  apply VF.Ge.sum
  intro col _
  show V.Ge 0 (bil Y.h (p.gm (p.ty0 c) col g • p.e c) (p.gm (p.ty0 q) col (1 - g) • p.e q))
  rw [bil_smul_left, bil_smul_right]
  exact (hgm _ _ _).mul_int ((hgm _ _ _).mul_int hβ)

end Formalism.L2.FormalSeriesBounds
