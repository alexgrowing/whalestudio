import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.KeyMinorDvd

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial Formalism.MainNotions.LemmaBAlt

def xvL (X : Loc) [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [Algebra (WF X.p X.n') O] (w : O)
    (g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n')) (j : Fin (numSeg X.TT)) (a : Fin (X.m + 1)) :
    MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) O :=
  ∑ b : Fin (X.m + 1), C (dW O w (hhLetters X.TT) 1 (topStart X j, true) b) * MvPolynomial.X ((topStart X j, true), b) *
    C (psiO X.p X.n' O ((topStart X j : X.TT).val.val : ℤ) (g⁻¹ b a))

def locExpr (X : Loc) [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [Algebra (WF X.p X.n') O] (w : O)
    (g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n')) (j0 : Fin (numSeg X.TT)) :
    MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) O :=
  xvL X O w g j0 0 * ∏ c : Fin X.m, (∏ j : Fin (numSeg X.TT), xvL X O w g j 0 ^ (X.p ^ segG X.TT j - 1) -
    ∏ j : Fin (numSeg X.TT), xvL X O w g j c.succ ^ (X.p ^ segG X.TT j - 1))

theorem liftSubst_start (X : Loc) [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra (WF X.p X.n') O] (w : O)
    (g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n')) (hg : IsGLW g) (j : Fin (numSeg X.TT)) (a : Fin (X.m + 1)) :
    liftSubst X.p X.n' O w 1 (hhLetters X.TT) g (MvPolynomial.X ((topStart X j, true), a)) =
      MvPolynomial.map (algebraMap O (KK O)) (xvL X O w g j a) := by
  rw [liftSubst_X_vec X.p X.n' O w (hhLetters X.TT) 1 g hg (topStart X j, true) a rfl]
  simp only [xvL, map_sum, map_mul, map_C, map_X, sigMat_apply]
  rfl

theorem locR_lift (X : Loc) [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra (WF X.p X.n') O] (w : O)
    (g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n')) (hg : IsGLW g) (j0 : Fin (numSeg X.TT)) :
    liftSubst X.p X.n' O w 1 (hhLetters X.TT) g (locR O X j0) =
      MvPolynomial.map (algebraMap O (KK O)) (locExpr X O w g j0) := by
  unfold locR locC locExpr
  simp only [map_mul, map_prod, map_sub, map_pow, liftSubst_start X O w g hg]

def LocalDivisibilityBound : Prop :=
  ∀ (X : Loc) [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra (WF X.p X.n') O] (S : UniformizedDVR X.p O), S.SqP → D1num X → 2 ≤ numSeg X.TT →
    ∀ (j0 : Fin (numSeg X.TT)) (g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n')), IsGLW g →
      ratPlane X.p X.n' 1 g ≠ ratPlane X.p X.n' 1 1 →
      (C S.w : MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) O) ∣ locExpr X O S.w g j0

theorem loc4Ord_of (h : LocalDivisibilityBound) : LocalOrderBound := by
  intro X _ O _ _ _ _ S hS hD h2 j0 g hg hpl
  obtain ⟨Q, hQ⟩ := h X O S hS hD h2 j0 g hg hpl
  unfold InWjRg
  rw [locR_lift X O S.w g hg j0, hQ]
  intro m
  refine ⟨Q.coeff m, ?_⟩
  rw [coeff_map, coeff_C_mul, pow_one, map_mul]

end Formalism.MainNotions.ColumnSystems.Pf
