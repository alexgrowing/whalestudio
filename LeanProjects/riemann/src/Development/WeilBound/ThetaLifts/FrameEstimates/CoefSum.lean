import Development.WeilBound.ThetaLifts.FrameEstimates.CoefSumB
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.ThetaDistributionHeisenbergInvariant

noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem annih : Annih := fun F _ _ ψ hψ u hu => by
  obtain ⟨c, hc⟩ := (GlobalTheory.CompanionTheory.AdeleAnn.unitary_and_annihilator_eq F ψ hψ.1
    (fun h => by
      obtain ⟨x, hx⟩ := GlobalTheory.StdCharFromIsStd.exists_ne_one hψ
      exact hx (by rw [h]; rfl)) hψ.2.1).2 u fun a => hu _ ⟨a, rfl⟩
  exact ⟨c, hc.symm⟩

theorem coefSum : CoefSum := coefSum_of_annih annih

end PositivityTheory.ThKEst

end
