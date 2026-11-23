import Mathlib
import Formalism.HermitianCurvature.StatementTBB
import Formalism.HermitianCurvature.HermitianCurvatureProofs.cut_PtwCut
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory

namespace GlobalTheory

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in

theorem beta_fold_cut_eq_beta_fold_of_cut : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (s : ℂ) (w : List (Bool × ℝ)) (χ : ℝ → ℝ) (δ ε ε₁ : ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), C6.IsCut0 χ → (∀ x, x < δ → χ x = 0) → 0 < ε → 0 < ε₁ → ε₁ < δ * ε → B.CkOn ⊤ (B.GV P.k P.r) F → B.beta p.T.base (List.foldr (fun (a : Bool × ℝ) G => s • Q.CV P.k P.r (a.2 : ℂ) G) ((D.cutF p.T.base χ F ε₁)) w) (D.cutF p.T.base χ F ε) = B.beta p.T.base (List.foldr (fun (a : Bool × ℝ) G => s • Q.CV P.k P.r (a.2 : ℂ) G) (F) w) (D.cutF p.T.base χ F ε) := by
  intro Wp Wq _ _ _ _ _ _ P p s w χ δ ε ε₁ F hχ hδ hε hε₁ hlt hF
  unfold B.beta betaBig
  refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
  by_cases hq : bcWeight P.k P.r (Tz P.k P.r p.T.base.z) (Tz P.k P.r p.T.base.z') q = 0
  · simp only [hq, Complex.ofReal_zero, zero_mul]
  obtain ⟨hgG, -⟩ := Formalism.FourierDecayAlt.P.CutBP.bigCell_pos p q hq
  by_cases hG : Gf P.k P.r p.T.base.z p.T.base.z' (bigCell P.k P.r q.1 (p.T.base.μsec q.2)) < δ * ε
  · have h0 : B.JF p.T.base (D.cutF p.T.base χ F ε) (bigCell P.k P.r q.1 (p.T.base.μsec q.2)) = 0 := by
      rw [Formalism.FourierDecayAlt.P.CutBP.jf_congr_level p.T.base (Y := fun _ => 0) hgG (fun x _ hGx => by
        unfold D.cutF
        rw [hGx, hδ _ ((div_lt_iff₀ hε).2 hG)]
        simp)]
      unfold B.JF besselJ
      simp
    have h1 : B.hsVec (0 : Wq →L[ℂ] Wp) = 0 := by
      unfold B.hsVec
      ext i
      simp
    simp only [h0, h1, inner_zero_left]
  · have hge : ε₁ < Gf P.k P.r p.T.base.z p.T.base.z' (bigCell P.k P.r q.1 (p.T.base.μsec q.2)) :=
      lt_of_lt_of_le hlt (not_lt.1 hG)
    have hU : IsOpen {x : B.Mat P.k P.r | ε₁ < Gf P.k P.r p.T.base.z p.T.base.z' x} :=
      isOpen_lt continuous_const (Formalism.FourierDecayAlt.P.JCx1.contDiff_Gf p.T.base.z p.T.base.z').continuous
    have he : ∀ x ∈ {x : B.Mat P.k P.r | ε₁ < Gf P.k P.r p.T.base.z p.T.base.z' x} ∩ B.GV P.k P.r,
        D.cutF p.T.base χ F ε₁ x = F x := by
      intro x hx
      unfold D.cutF
      rw [hχ.2.2 _ ((one_le_div hε₁).2 (le_of_lt hx.1))]
      simp
    have hcut := Formalism.FourierDecayAlt.P.JCTx6.Link2.ckOn_cutF p.T.base hχ hF ε₁
    have hlev : ∀ x ∈ B.GV P.k P.r, Gf P.k P.r p.T.base.z p.T.base.z' x =
        Gf P.k P.r p.T.base.z p.T.base.z' (bigCell P.k P.r q.1 (p.T.base.μsec q.2)) →
        x ∈ {x : B.Mat P.k P.r | ε₁ < Gf P.k P.r p.T.base.z p.T.base.z' x} ∩ B.GV P.k P.r :=
      fun x hx hGx => ⟨by show ε₁ < _; rw [hGx]; exact hge, hx⟩
    have key := Formalism.FourierDecayAlt.P.CutBP.jf_congr_level p.T.base hgG (fun x hx hGx =>
      Formalism.FourierDecayAlt.P.CutBP.fold_congr_open s hU hcut hF he w x (hlev x hx hGx))
    exact congrArg (fun A => (bcWeight P.k P.r (Tz P.k P.r p.T.base.z) (Tz P.k P.r p.T.base.z') q : ℂ) *
      inner ℂ (B.hsVec (B.JF p.T.base (D.cutF p.T.base χ F ε) (bigCell P.k P.r q.1 (p.T.base.μsec q.2))))
        (B.hsVec A)) key

end GlobalTheory
