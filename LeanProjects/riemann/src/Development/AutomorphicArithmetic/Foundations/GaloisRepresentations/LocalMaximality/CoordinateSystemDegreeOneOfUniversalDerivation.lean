import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.LiftFactorization

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private lemma acx_eq_zero {σ E : Type} [LinearOrder σ] [AddCommGroup E] [Module ℂ E]
    (A : Finset σ → Submodule ℂ E) (w : σ → Module.End ℂ E) (n : ℤ) (c : Finset σ → E)
    (hc : c ∈ (acx A w).C n) (s : Finset σ) (hs : A s = ⊥) : c s = 0 := by
  have h : c s ∈ (if (s.card : ℤ) = n then A s else ⊥) :=
    Submodule.mem_pi.1 (show c ∈ Submodule.pi Set.univ
      (fun s : Finset σ => if (s.card : ℤ) = n then A s else ⊥) from hc) s (Set.mem_univ _)
  rw [hs, ite_self, Submodule.mem_bot] at h
  exact h

theorem UpperTheory.Gal.productCup_of_system.coordinateSystem_degree_one_of_universalDerivation :
    L1 → SysOk → WdUni → CechKoszulSystemBoundaryCriterion := by
  intro hL hOk hU
  intro d S E _ _ _ _ T κ _ _ n z N hG hAdm hKE c hc hbig hcol
  obtain ⟨hW, -, -⟩ := hOk d S E T κ n z hG hAdm
  set A : Finset (Two d ⊕ₗ κ) → Submodule ℂ E := fun s => mixF (fun I J =>
    Submodule.map (T.act ↑(∏ l ∈ rgt s, T.u n (pk I) (pk J) l)) (T.M I J)) (lft s) with hA
  have hu := fun (b : Finset (Two d)) (L : Finset κ) => hU (Two d) κ E (T.wt z) (fun _ => 0) b L
  have hcolA : ∀ b : Finset (Two d), (lft b).Nonempty → (rgt b).Nonempty →
      colA A (T.wt z) b = T.colCx n z (lft b) (rgt b) := by
    intro b h1 h2
    simp only [colA, Sys.colCx, kosT]
    congr 1
    funext L
    simp only [hA, (hu b L).2.1, (hu b L).2.2.1, mixF, if_pos (And.intro h1 h2)]
  have hbot : ∀ b : Finset (Two d), ¬ ((lft b).Nonempty ∧ (rgt b).Nonempty) → ∀ L, A (uni b L) = ⊥ := by
    intro b h L
    simp only [hA, (hu b L).2.1, mixF, if_neg h]
  have hcC : c ∈ (acx A (T.wt z)).C N := hc.1
  refine hL (Two d) κ E A (T.wt z) (d : ℤ) N hW ?_ c hc ?_ ?_
  · intro b
    by_cases h : (lft b).Nonempty ∧ (rgt b).Nonempty
    · rw [hcolA b h.1 h.2]
      exact hKE _ _ h.1 h.2
    · intro m _ x hx
      have hx1 : x ∈ (colA A (T.wt z) b).C m := hx.1
      have hx0 : x = 0 := funext fun L =>
        acx_eq_zero (fun L => A (uni b L)) (fun l => T.wt z (inrE l)) m x hx1 L (hbot b h L)
      rw [hx0]
      exact Submodule.zero_mem _
  · intro b L hlt
    exact hbig b L (by exact_mod_cast hlt)
  · intro b hb
    by_cases h : (lft b).Nonempty ∧ (rgt b).Nonempty
    · rw [hcolA b h.1 h.2]
      have hU2 := hU (Fin (d + 1)) (Fin (d + 1)) E (fun _ => 0) (fun _ => 0) (lft b) (rgt b)
      have hs : uni (lft b) (rgt b) = b := hU2.2.2.2.2 b
      have := hcol (lft b) (rgt b) h.1 h.2 (by rw [← hb, ← hU2.2.2.2.1, hs])
      rw [hs] at this
      exact this
    · have h0 : col c b = 0 := funext fun L => acx_eq_zero A (T.wt z) N c hcC (uni b L) (hbot b h L)
      rw [h0]
      exact Submodule.zero_mem _
