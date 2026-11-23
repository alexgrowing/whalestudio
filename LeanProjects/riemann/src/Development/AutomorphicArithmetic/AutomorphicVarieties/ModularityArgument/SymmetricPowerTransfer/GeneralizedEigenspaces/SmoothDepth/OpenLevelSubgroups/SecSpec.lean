import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.ContCoef
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.CLocConjAlt

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z.Sym.Al

theorem UpperTheory.V.Z.Sym.Al.secSpec :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (w : Plc L), IsSplitAt w →
        (∀ g, secW n w g ∈ locU n w) ∧ (∀ g, cLoc w (secW n w g) = g) ∧ (∀ x ∈ locU n w, secW n w (cLoc w x) = x) ∧ Continuous (secW n w) := by
  intro L _ _ _ n w hw
  obtain ⟨e, he⟩ := GlobalTheory.T.splitPlace_unitaryLocalPoints_equiv_GL L n w hw
  have hs : ∀ y, cLoc w (e.symm y : UA L n) = y := fun y => by rw [← he, e.apply_symm_apply]
  have h : ∃ j : GL (Fin n) (Kw w) →* UA L n, (∀ g, j g ∈ locU n w) ∧ ∀ g, cLoc w (j g) = g :=
    ⟨(locU n w).subtype.comp e.symm.toMulEquiv.toMonoidHom, fun g => (e.symm g).2, hs⟩
  have h1 : (∀ g, secW n w g ∈ locU n w) ∧ ∀ g, cLoc w (secW n w g) = g := by
    unfold secW; rw [dif_pos h]; exact h.choose_spec
  have h2 : ∀ g, secW n w g = (e.symm g : UA L n) := fun g => by
    have : e ⟨_, h1.1 g⟩ = g := by rw [he]; exact h1.2 g
    exact (congrArg Subtype.val ((e.symm_apply_eq.2 this.symm) : e.symm g = ⟨_, h1.1 g⟩)).symm
  refine ⟨h1.1, h1.2, fun x hx => ?_, ?_⟩
  · rw [h2, ← he ⟨x, hx⟩, e.symm_apply_apply]
  · rw [show (secW n w : _ → _) = fun g => (e.symm g : UA L n) from funext h2]
    exact continuous_subtype_val.comp e.symm.continuous
