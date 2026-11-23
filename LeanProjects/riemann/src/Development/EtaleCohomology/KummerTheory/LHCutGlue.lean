import Development.EtaleCohomology.KummerTheory.FinalTheorems

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory.LHCut

theorem ghostSec_of (hG : Ghost) (h1 : Corep) (h2 : HomKill) : GhostSec := by
  intro Λ _ S C hi hz N m hl j hj U x hx
  have : C.IsStrictlyGE (-1) := (CochainComplex.isStrictlyGE_iff _ _).2 (fun i hi => hz i hi)
  obtain ⟨P, z, hP⟩ := h1 Λ S U
  obtain ⟨f, rfl⟩ := (hP (C.X j)).2 x
  obtain ⟨g, hg⟩ := hG (SlShv Λ S) C hi N m (fun j hj => h2 Λ S C N j (hl j hj)) j hj P f
    ((hP _).1 (hx.trans rfl))
  refine ⟨(g.hom.app (op U)).hom z, ?_⟩
  have := congrArg (fun φ : P ⟶ C.X j => (φ.hom.app (op U)).hom z) hg
  refine this.trans ?_
  generalize N ^ (m + 1) = k
  induction k with
  | zero => simp only [zero_smul]; rfl
  | succ k ih => rw [succ_nsmul, succ_nsmul, ← ih]; rfl

theorem glob_of (h1 : ConeCx) (h2 : GhostSec) : Glob := by
  intro Λ _ I J K μ hJ hK X S p r M γ hc N m hl j hj U x hx
  obtain ⟨C, hi, hz, e, he, hd⟩ := h1 Λ μ hJ hK p r M γ hc
  have hloc : ∀ j : ℤ, j < m → CxLoc C N j := by
    intro j hj U x hx u
    obtain ⟨V, g, hg, y, hy⟩ := hl j hj U (e j U x) (by rw [← hd j (j + 1) rfl, hx, map_zero]) u
    refine ⟨V, g, hg, (e _ V).symm y, (e j V).injective ?_⟩
    rw [hd (j - 1) j (by omega), AddEquiv.apply_symm_apply, hy, map_nsmul, he]
  obtain ⟨y, hy⟩ := h2 Λ S C hi hz N m hloc j hj U ((e j U).symm x) ((e (j + 1) U).injective (by
    rw [hd j (j + 1) rfl, AddEquiv.apply_symm_apply, hx, map_zero]))
  refine ⟨e _ U y, ?_⟩
  rw [← hd (j - 1) j (by omega), hy, map_nsmul, AddEquiv.apply_symm_apply]

theorem clsMore_of (hD : Dict) : ClsMore := by
  intro Λ _ I X n
  obtain ⟨_, d2, d3, d4, _⟩ := hD Λ I X n
  have h0 : IsCls (0 : CochainComplex.HomComplex.CohomologyClass ((chains Λ).obj (sch.obj X)) I n) 0 := by
    obtain ⟨a, ha⟩ := d2 0
    have := (d4 _ _ _ _ ha (d4 _ _ _ _ ha ha).2).1
    rwa [add_neg_cancel, add_neg_cancel] at this
  refine ⟨h0, ?_, ?_, ?_⟩
  · intro N x a h
    induction N with
    | zero => rw [zero_nsmul, zero_nsmul]; exact h0
    | succ N ih => rw [succ_nsmul, succ_nsmul]; exact (d4 _ _ _ _ ih h).1
  · intro ι _ x a h
    classical
    induction (Finset.univ : Finset ι) using Finset.induction_on with
    | empty => rw [Finset.sum_empty, Finset.sum_empty]; exact h0
    | insert t s ht ih => rw [Finset.sum_insert ht, Finset.sum_insert ht]; exact (d4 _ _ _ _ (h t) ih).1
  · intro m hm x x' a a' h h'
    obtain rfl : m = n - 1 := by omega
    have := (d3 _ _ (d4 _ _ _ _ h (d4 _ _ _ _ h' h').2).1).2
    rwa [← sub_eq_add_neg, ← sub_eq_add_neg, sub_eq_zero] at this

theorem lh_of (hD : Dict) (hG : Ghost) (h1 : LocKer) (h2 : LocCok) (h3 : LocCone) (h4 : ExIso) (h5 : ConeCx) (h6 : Corep)
    (h7 : HomKill) : LH :=
  goal_of hD h1 h2 h3 (glob_of h5 (ghostSec_of hG h6 h7)) h4

end LateralTheory.KummerTheory.LHCut
