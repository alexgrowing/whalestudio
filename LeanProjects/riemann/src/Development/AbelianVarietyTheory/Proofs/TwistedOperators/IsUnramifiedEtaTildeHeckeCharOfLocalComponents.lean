import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TameOnOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoInfMulProd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TameHeckeCharTrivialOnFiniteUnitsCongOne

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.StepLaw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.EtaTildeOfComponents

theorem isEtaTilde_of_chrEq : ∀ (D : D7) (C : Formalism.L2.Host.CharFrame D) (η : (AE D)ˣ →* Circle), ChrEq η C.eta → ResEta D η 1 → IsEtaTilde D η := by
  intro D C η hc hres
  have hE := C.isEta

  have hInf : C.eta.HasInfQ (tauE D) (fun _ => (1 / 2 : ℚ)) := by
    refine ⟨fun _ => 1, fun _ => by norm_num, fun k => ?_⟩
    rw [hE.inf k]
    exact (Fintype.prod_equiv D.eTau _ _ (fun _ => rfl)).symm
  have h1 : 1 ∈ intAE D := by
    apply AddSubgroup.subset_closure
    refine ⟨1, fun v => ?_, 1, rfl⟩
    simp [evalV, (v.adicCompletionIntegers D.host.F).one_mem]
  refine ⟨hc.1, ?_, hres, fun τ => GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D η C.eta _ hc hInf τ⟩

  intro x hx1 hx2 hx3
  refine GlobalTheory.tame_heckeChar_eq_one_of_finUnit D η C.eta hc ?_ 1 (fun P _ => hE.unr P) x ⟨hx1, hx2, hx3⟩
    ⟨finPart D (x : AE D) - 1, sub_mem hx2 h1, (one_nsmul _).symm⟩
  intro P y hy _
  exact hE.unr P y hy

end GlobalTheory.EtaTildeOfComponents
