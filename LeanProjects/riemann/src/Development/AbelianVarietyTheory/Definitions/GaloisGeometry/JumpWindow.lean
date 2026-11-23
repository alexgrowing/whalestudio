import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

noncomputable section

namespace GlobalTheory.BlockWindow

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain

def JointTB (D : D7) (HW : HWOf D.loc) (_F : FonOf D.loc D.locA HW) (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i) (M0 h0 cB : ℕ) : Prop :=
  D.nd.l i ≠ 2 ∧ ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
    Br.inert D.nbr i w hw = IK (D.nbr i w hw).Kw ∧ (D.nbr i w hw).Kw.1 ≤ Ks (D.nbr i w hw).Kw 1 ∧
    ∀ (CL : FinExt (D.nd.l i)) (h : (D.nbr i w hw).LL.1 ≤ CL.1) (hs : Good (D.nbr i w hw).Kw 1 CL)
      (Y : LocLat (Br.G D.nbr i w hw) ℚ_[D.nd.l i] ↥CL.1 ↥(OL CL)),
      IsCrys (Br.PD D.loc D.nbr i w hw) Y.ρ →
      (∀ τ, JumpsInV (Br.PD D.loc D.nbr i w hw) Y.ρ τ
        {a | IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (rTwO D.nd i r π)))) τ a}) →
      (∀ a ∈ LocalSituation.Jset (LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i w hw).Kw 1 CL hs) Y,
        -(M0 : ℤ) ≤ a ∧ a ≤ h0) ∧
      ∀ e < D.R.t,
        LocalSituation.cTBY (LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i w hw).Kw 1 CL hs) Y M0 h0 e ≤ cB

def JumpWindow (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i)
    (h₁ : ℕ) : Prop :=
  ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (CL : FinExt (D.nd.l i)) (h : (D.nbr i w hw).LL.1 ≤ CL.1) (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥CL.1),
    ∃ U : Finset ℤ, U.card ≤ D.R.nV ∧ (∀ u ∈ U, -(h₁ : ℤ) ≤ u ∧ u + 1 ≤ h₁) ∧
      ∀ a, IsJumpV (Br.PD D.loc D.nbr i w hw)
        (matRep (mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (rTwO D.nd i r π)))) τ a → a ∈ U

theorem JointTB.mono {D : D7} {HW : HWOf D.loc} {F : FonOf D.loc D.locA HW} {i : D.nd.Loc}
    {r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))} {π : D.nd.X i} {M0 h0 cB cB' : ℕ} (hle : cB ≤ cB')
    (h : JointTB D HW F i r π M0 h0 cB) : JointTB D HW F i r π M0 h0 cB' := by
  refine ⟨h.1, fun w hw => ?_⟩
  obtain ⟨h1, h2, h3⟩ := h.2 w hw
  refine ⟨h1, h2, fun CL hL hs Y hc hY => ?_⟩
  obtain ⟨k1, k2⟩ := h3 CL hL hs Y hc hY
  exact ⟨k1, fun e he => (k2 e he).trans hle⟩

end GlobalTheory.BlockWindow

end
