import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RationalUnitaryGroupStructure

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SepPer

theorem ratPt_mulVec_ratV : ∀ (D : D7) (V : HSp D) (γ : GA D V), γ ∈ GQ V → ∀ y : Fin V.rank → D.host.E,
    ∃ z : Fin V.rank → D.host.E, mt V γ *ᵥ ratV y = ratV z := by
  intro D V γ hγ y
  obtain ⟨e, he⟩ := GlobalTheory.Ker.Grp.exists_equiv V
  have h : mt V γ = ((e.symm ⟨γ, hγ⟩).1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (incA D) := by
    have := he (e.symm ⟨γ, hγ⟩)
    rw [Equiv.apply_symm_apply] at this
    exact this
  refine ⟨((e.symm ⟨γ, hγ⟩).1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ y, ?_⟩
  rw [h]
  funext i
  simp only [ratV]
  exact (RingHom.map_mulVec (incA D) _ y i).symm

end GlobalTheory.SepPer

end
