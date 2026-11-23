import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JumpWindow
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinrankMaxUnramifiedSubfieldPadicFinExtPos
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.JumpWindowAndBlockExponentOfEmbeddingsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValuationLtOneIffNorm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankLeOfSubsetClosureRange
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalFieldUnramified
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicValNatFinrankKs

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.BlockWindow

theorem jointTB_of_jumpWindow : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i) (h₁ : ℕ), D.nd.l i ∉ D.host.small → D.nd.l i ≠ D.host.q → D.nd.l i ≠ D.host.d → D.R.t ≤ h₁ → GlobalTheory.BlockWindow.JumpWindow D i r π h₁ → GlobalTheory.BlockWindow.JointTB D HW F i r π h₁ h₁ (GlobalTheory.HubLoc.cBnum (D.nd.l i) h₁ D.R.t (4 * D.R.n * D.R.nV)) := by
  intro D HW F i r π h₁ hsm hq hd ht hJ
  have h2 : D.nd.l i ≠ 2 := fun e => hsm (e ▸ D.host.toHostRaw.two_mem_small)
  refine ⟨h2, fun w hw => ?_⟩
  obtain ⟨hK0, hK1, -⟩ := GlobalTheory.HubLoc.localField_unramified D i hsm hq hd w hw
  have hKur : (D.nbr i w hw).Kw.1 ≤ MaximalUnramifiedExtension (D.nd.l i) := by
    rw [← hK0]; exact inf_le_right
  refine ⟨GlobalTheory.BridgeInertia.inertEq D i w hw, hK1, fun CL h hs Y hc hY => ?_⟩
  have hs1 : (LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i w hw).Kw 1 CL hs).W.s = 1 :=
    (HW (D.nd.l i)).W_s _ 1 _ hs
  have hell : LocalSituation.ell (LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i w hw).Kw 1 CL hs) = D.nd.l i :=
    (D.loc (D.nd.l i)).PD_p _
  haveI : CharZero (LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i w hw).Kw 1 CL hs).Qp :=
    inferInstanceAs (CharZero ℚ_[D.nd.l i])
  haveI : FiniteDimensional (LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i w hw).Kw 1 CL hs).Qp
      (LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i w hw).Kw 1 CL hs).K := (D.nbr i w hw).Kw.2
  have hcard : Nat.card (↥(D.nbr i w hw).Kw.1 →ₐ[ℚ_[D.nd.l i]] ↥CL.1) =
      Module.finrank ℚ_[D.nd.l i] ↥(D.nbr i w hw).Kw.1 :=
    GlobalTheory.HubLoc.card_emb _ _ fun τ x => h ((D.nbr i w hw).LL_split τ x)
  have hdeg := GlobalTheory.bridge_finrank_le D i w hw
  obtain ⟨hv1, hv2⟩ := GlobalTheory.HubLoc.padicValNat_finrank_Ks (D.nd.l i) (D.nbr i w hw).Kw
  have hgK : LocalSituation.gK (LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i w hw).Kw 1 CL hs) = 0 := by
    unfold LocalSituation.gK
    rw [hs1, hell]
    exact hv2 hKur
  have hvd : ∀ m : ℕ, 0 < m → LocalSituation.vdegMs (LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i w hw).Kw 1 CL hs) m = m - 1 := by
    intro m hm
    unfold LocalSituation.vdegMs
    rw [hs1, hell]
    exact hv1 m hm
  have key := GlobalTheory.T.jumpWindow_and_blockExponent_of_embeddings (LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i w hw).Kw 1 CL hs) Y h₁ D.R.nV (4 * D.R.n) D.R.t
    hs1 hcard hdeg hgK (hvd _ (by unfold LocalSituation.mN; omega)) ht (fun τ => by
      obtain ⟨U, hU1, hU2, hU3⟩ := hJ w hw CL h τ
      exact ⟨U, hU1, hU2, fun a ha => hU3 a (hY τ a ha)⟩)
  refine ⟨key.1, fun e he => (key.2 e he).trans (le_of_eq ?_)⟩
  rw [hell]

end GlobalTheory.BlockWindow
