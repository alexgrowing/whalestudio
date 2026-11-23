import Mathlib
import Development.AutomorphicArithmetic.ResidueCharacters.ExistsUnion
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JumpWindow
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinrankMaxUnramifiedSubfieldPadicFinExtPos
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValuationLtOneIffNorm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankLeOfSubsetClosureRange

noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations

namespace UpperTheory.N

variable {D : D7}

theorem block_condition_at_places_of_jump_window (i : D.nd.Loc) (N : ℕ) (hK : TBK (D.loc (D.nd.l i))) (hC : CycAt N i)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i) (h : ℕ) (ht : D.R.t ≤ h)
    (hJ : GlobalTheory.BlockWindow.JumpWindow D i r π h) :
    TruncatedSeriesCountingIdentities.admTB i r π (cBL (D.nd.l i) N h (4 * D.R.n * D.R.nV) D.R.t) := by
  intro w hw C _
  have hcard : Nat.card (↥(D.nbr i w hw).Kw.1 →ₐ[ℚ_[D.nd.l i]] ↥C.LL.1) ≤ 4 * D.R.n := by
    rw [GlobalTheory.HubLoc.card_emb _ _ fun τ x => C.le ((D.nbr i w hw).LL_split τ x)]
    exact GlobalTheory.bridge_finrank_le D i w hw
  haveI : Finite (↥(D.nbr i w hw).Kw.1 →ₐ[ℚ_[D.nd.l i]] ↥C.LL.1) := by
    haveI := (D.nbr i w hw).Kw.2
    infer_instance
  obtain ⟨U, h1, h2, h3⟩ := exists_union (4 * D.R.n) D.R.nV h hcard
    (fun τ a => IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i r π))) τ a) (fun τ => by
      obtain ⟨U, a, b, c⟩ := hJ w hw C.LL C.le τ
      exact ⟨U, a, fun u hu => ⟨(b u hu).1, by have := (b u hu).2; omega⟩, c⟩)
  rw [GlobalTheory.BridgeInertia.inertEq D i w hw]
  exact hK N h _ D.R.t (D.nbr i w hw).Kw C.LL (hC w hw C) ht _ U h1 h2 (fun τ a ha => h3 τ a ha)

end UpperTheory.N

end
