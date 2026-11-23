import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.LiftSubstStart

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial Formalism.MainNotions.LemmaBAlt

def psiRes (X : Loc) [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [Algebra (WF X.p X.n') O] (w : O)
    (g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n')) (j : Fin (numSeg X.TT)) (a : Fin (X.m + 1)) :
    O ⧸ Ideal.span {w} :=
  Ideal.Quotient.mk (Ideal.span {w}) (psiO X.p X.n' O ((topStart X j : X.TT).val.val : ℤ) (g⁻¹ 0 a))

def LocalResidueBound : Prop :=
  ∀ (X : Loc) [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra (WF X.p X.n') O] (S : UniformizedDVR X.p O), S.SqP → D1num X → 2 ≤ numSeg X.TT →
    ∀ (j0 : Fin (numSeg X.TT)) (g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n')), IsGLW g →
      ratPlane X.p X.n' 1 g ≠ ratPlane X.p X.n' 1 1 →
      psiRes X O S.w g j0 0 = 0 ∨ ∃ c : Fin X.m,
        ∏ j : Fin (numSeg X.TT), psiRes X O S.w g j 0 ^ (X.p ^ segG X.TT j - 1) =
          ∏ j : Fin (numSeg X.TT), psiRes X O S.w g j c.succ ^ (X.p ^ segG X.TT j - 1)

theorem map_xvL (X : Loc) [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [Algebra (WF X.p X.n') O] (w : O)
    (g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n')) (j : Fin (numSeg X.TT)) (a : Fin (X.m + 1)) :
    map (Ideal.Quotient.mk (Ideal.span {w})) (xvL X O w g j a) =
      C (psiRes X O w g j a) * MvPolynomial.X ((topStart X j, true), 0) := by
  have hw0 : Ideal.Quotient.mk (Ideal.span {w}) w = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self w)
  unfold xvL psiRes
  rw [map_sum, Finset.sum_eq_single 0]
  · simp [Formalism.MainNotions.LemmaBAlt.dW, Formalism.MainNotions.ColumnSystems.hhLetters]
    try ring
  · intro b _ hb
    have hb1 : 1 ≤ b.val := Nat.one_le_iff_ne_zero.mpr (fun h => hb (Fin.ext h))
    simp [Formalism.MainNotions.LemmaBAlt.dW, Formalism.MainNotions.ColumnSystems.hhLetters, hb1, hw0]
  · intro h
    exact absurd (Finset.mem_univ 0) h

theorem loc4Div_of (h : LocalResidueBound) : LocalDivisibilityBound := by
  intro X _ O _ _ _ _ S hS hD hn j0 g hg hne
  rw [MvPolynomial.C_dvd_iff_map_hom_eq_zero (Ideal.Quotient.mk (Ideal.span {S.w})) S.w
    (fun x => by rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton])]
  unfold locExpr
  simp only [map_mul, map_prod, map_sub, map_pow, map_xvL]
  rcases h X O S hS hD hn j0 g hg hne with h0 | ⟨c, hc⟩
  · rw [h0]
    simp
  · apply mul_eq_zero_of_right
    apply Finset.prod_eq_zero (Finset.mem_univ c)
    simp only [mul_pow, Finset.prod_mul_distrib, ← map_pow, ← map_prod]
    rw [hc, sub_self]

end Formalism.MainNotions.ColumnSystems.Pf
