import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.LocVol

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.TypedSets Formalism.L2.SG.LocVol

theorem finJac_of {D : D7} (X : HidaSetting D) (u u' : D.what₂.Word) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ)
    (hJ : ∀ v : PlX X, JacLocAt X u u' ψ v) : FinJac X u u' ψ := by
  intro hP hT
  obtain ⟨-, -, -, hUo, -, hZm, -, hPP, -, -, hjm, -⟩ := hP
  have hJ' : ∀ v : PlX X, ZZX X u u' ψ v * jacX X v = localVolumeUnit X ψ v * ∏ l : Fin (D.R.rS + 1), PPX X u u' ψ l v :=
    fun v => hJ v (fun hv => hT ⟨v, hv⟩)

  have hL : HasProd (fun v : PlX X => ZZX X u u' ψ v * jacX X v)
      ((∏' v : PlX X, ZZX X u u' ψ v) * ∏' v : PlX X, jacX X v) := hZm.hasProd.mul hjm.hasProd

  set S : Set (PlX X) := {v | TypAt X v} with hSdef
  have hfin : Finite S := by
    have : Set.Finite S := (typSet X.B.I.F (D.host.g 0) (D.host.g 1)).finite_toSet
    exact this.to_subtype
  have hUS : HasProd (fun x : S => localVolumeUnit X ψ x.1) (∏' x : S, localVolumeUnit X ψ x.1) := Multipliable.of_finite.hasProd
  have hUSc : HasProd (fun x : (Sᶜ : Set (PlX X)) => localVolumeUnit X ψ x.1) (∏' v : OrdX X, localVolumeUnit X ψ v.1) := hUo.hasProd
  have hU : HasProd (localVolumeUnit X ψ) ((∏' x : S, localVolumeUnit X ψ x.1) * ∏' v : OrdX X, localVolumeUnit X ψ v.1) :=
    hUS.mul_isCompl isCompl_compl hUSc
  have hPPh : HasProd (fun v : PlX X => ∏ l : Fin (D.R.rS + 1), PPX X u u' ψ l v)
      (∏ l : Fin (D.R.rS + 1), ∏' v : PlX X, PPX X u u' ψ l v) :=
    hasProd_prod fun l _ => (hPP l).1.hasProd
  have hR := hU.mul hPPh
  have hLR : (∏' v : PlX X, ZZX X u u' ψ v) * ∏' v : PlX X, jacX X v =
      ((∏' x : S, localVolumeUnit X ψ x.1) * ∏' v : OrdX X, localVolumeUnit X ψ v.1) *
        ∏ l : Fin (D.R.rS + 1), ∏' v : PlX X, PPX X u u' ψ l v := by
    refine hL.unique ?_
    simpa only [hJ'] using hR
  have hTyp : (∏ p : TypX X, localVolumeUnit X ψ p.1) = ∏' x : S, localVolumeUnit X ψ x.1 := by
    rw [← tprod_fintype (L := SummationFilter.unconditional (TypX X)) (fun p : TypX X => localVolumeUnit X ψ p.1)]
    rfl
  show (∏' v : PlX X, ZZX X u u' ψ v) * ∏' v : PlX X, jacX X v =
    ((∏' v : OrdX X, localVolumeUnit X ψ v.1) * ∏ p : TypX X, localVolumeUnit X ψ p.1) *
      ∏ l : Fin (D.R.rS + 1), ∏' v : PlX X, PPX X u u' ψ l v
  rw [hLR, hTyp]
  ring

end Formalism.L2.SG.Pf
