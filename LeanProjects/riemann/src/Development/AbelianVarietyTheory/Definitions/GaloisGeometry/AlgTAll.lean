import Mathlib
import Formalism.LocalToGlobal.InertKernelTheory.StatementAlgT
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.VacuumEntireAndNormalizedJetsAlgebraic
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TranslateMomentsAllOfJetMomR

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

namespace GlobalTheory.ThLoc.Alg

theorem algTAll : Formalism.L2.KerInert.AlgTAll := by
  intro D cc δ B χ hcc hδ hχ N N' L L' hA t ht α
  have hC : StandardLatticesGL3.Crv D cc δ := ⟨hcc, hδ⟩
  have hT := GlobalTheory.Mem.Col2.JetAlgebraic.ta_thMoved B hC hA.2.2.1 hA.2.2.2
  have h := (GlobalTheory.Mem.Col2.JetAlgebraic.TA.comb (cc := cc) (δ := δ) (Finset.univ : Finset Unit)
    (fun _ => Base.chiFac χ N N' L L') (fun _ => B.thMoved N N' L L')
    (fun _ => GlobalTheory.MomT.FromComb.chiFac_mem hχ hA) (fun _ => hT)).2
  have e : (fun z => ∑ _a ∈ (Finset.univ : Finset Unit), Base.chiFac χ N N' L L' * B.thMoved N N' L L' z) =
      B.eNat χ N N' L L' := by
    funext z
    simp [Base.eNat]
  rw [e] at h
  obtain ⟨a, ha, hat⟩ := ht
  exact h t (GlobalTheory.ThetaAlgebraic.sat_of_nsmul ha
    (GlobalTheory.Mem.Col2.JetAlgebraic.la_le_sat hC hA.2.2.1 hA.2.2.2 hat)) α

end GlobalTheory.ThLoc.Alg
