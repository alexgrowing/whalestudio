import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.RowTie

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

theorem placesOver_finite_of_ne_zero (E : Type) [Field E] [NumberField E] (p : ℕ) (hp : p ≠ 0) :
    (placesOver E p).Finite := by
  have h0 : Ideal.span {((p : ℕ) : 𝓞 E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp
  refine (Ideal.finite_factors h0).subset fun v hv => ?_
  show v.asIdeal ∣ _
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  exact hv

theorem isoLoc_perm {Pa Pa' : List (Part A.CG)} (h : Pa.Perm Pa') (w : PlE H) :
    isoLoc N A Pa w = isoLoc N A Pa' w := by
  induction h with
  | nil => rfl
  | cons p _ ih =>
    simp only [isoLoc, List.foldr_cons] at ih ⊢
    rw [ih]
  | swap p q l =>
    simp only [isoLoc, List.foldr_cons]
    rw [← A.lpSum_assoc (spehLoc N A q w), A.lpSum_comm (spehLoc N A q w) (spehLoc N A p w), A.lpSum_assoc]
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem locV_eq_of_pt (i : N.Loc) {P P' : A.AV i} {x : N.X i} (hx : A.ptV i P = some x)
    (hx' : A.ptV i P' = some x) {w : PlE H} (hso : SplitOut N i w) (hg : ∀ k, w ∉ placesOver H.E (H.g k))
    (hd : w ∉ placesOver H.E (if N.l i = H.pde then H.pde' else H.pde)) :
    A.locV i P w = A.locV i P' w := by
  set c : ℝ := (1 - (R.nV : ℝ)) / 2
  have u : A.unr (A.lpTw (A.locV i P w) c) :=
    (A.unr_tw _ _).2 (A.locV_unr i P w hso.1 hso.2.2.2 hg hd)
  have u' : A.unr (A.lpTw (A.locV i P' w) c) :=
    (A.unr_tw _ _).2 (A.locV_unr i P' w hso.1 hso.2.2.2 hg hd)
  have h1 := congrArg Polynomial.roots ((A.pt_loc i P x hx w hso).symm.trans (A.pt_loc i P' x hx' w hso))
  rw [Polynomial.roots_multiset_prod_X_sub_C, Polynomial.roots_multiset_prod_X_sub_C] at h1
  have e : A.lpTw (A.locV i P w) c = A.lpTw (A.locV i P' w) c := by
    rw [A.unr_eq_lpUnr _ u, A.unr_eq_lpUnr _ u', h1]
  have back : ∀ a : A.LP w, A.lpTw (A.lpTw a c) (-c) = a := fun a => by
    rw [A.lpTw_add, add_neg_cancel, A.lpTw_zero]
  rw [← back (A.locV i P w), e, back]

theorem locOfPt_of_splitBC : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N)
    (i : N.Loc), GlobalTheory.RowTie.BCEx N A i → GlobalTheory.RowTie.SplitBC N A i → GlobalTheory.ThetaExh.LocOfPt N A i := by
  intro R H what₂ N A i hBC hS P P' x hx hx' w hw
  obtain ⟨Pa, hPa⟩ := hBC P
  obtain ⟨Pa', hPa'⟩ := hBC P'
  have hd0 : (if N.l i = H.pde then H.pde' else H.pde) ≠ 0 := by
    split_ifs
    exacts [H.pde'_prime.ne_zero, H.pde_prime.ne_zero]
  have hfin : (placesOver H.E (N.l i) ∪ (N.S i : Set (PlE H)) ∪ (N.Q i : Set (PlE H)) ∪
      placesOver H.E (H.g 0) ∪ placesOver H.E (H.g 1) ∪
      placesOver H.E (if N.l i = H.pde then H.pde' else H.pde)).Finite := by
    refine ((((( placesOver_finite_of_ne_zero _ _ (N.lPrime i).out.ne_zero).union (N.S i).finite_toSet).union
      (N.Q i).finite_toSet).union (placesOver_finite_of_ne_zero _ _ (H.g_prime 0).ne_zero)).union
      (placesOver_finite_of_ne_zero _ _ (H.g_prime 1).ne_zero)).union (placesOver_finite_of_ne_zero _ _ hd0)
  have hev : ∀ᶠ v in Filter.cofinite, IsSplitPl H v → A.locV i P v = A.locV i P' v := by
    rw [Filter.eventually_cofinite]
    refine hfin.subset fun v hv => ?_
    by_contra hn
    simp only [Set.mem_union, Finset.mem_coe, not_or] at hn
    obtain ⟨⟨⟨⟨⟨hl, hSv⟩, hQv⟩, hg0⟩, hg1⟩, hdv⟩ := hn
    refine hv fun hsp => locV_eq_of_pt N A i hx hx' ⟨hsp, hl, hSv, hQv⟩ ?_ hdv
    intro k
    fin_cases k
    exacts [hg0, hg1]
  have hperm := hS P P' hev Pa Pa' hPa hPa'
  rw [← hPa.2.2.2.1 w hw, ← hPa'.2.2.2.1 w hw]
  exact isoLoc_perm N A hperm w

end GlobalTheory.RowTie
