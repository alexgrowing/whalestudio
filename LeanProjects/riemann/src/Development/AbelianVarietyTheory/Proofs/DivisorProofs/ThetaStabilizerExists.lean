import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedAdelicLatticeClosureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelativelyCompactStabilizerStatement

noncomputable section

namespace GlobalTheory.StabHaar

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

theorem stabEx : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.ThK.StabEx := by
  intro _ F E _ _ _ _ _ σ B n X r s hB hX
  have hc : IsCompact ((stabK (σ := σ) B X : Subgroup (UA σ X.J)) : Set (UA σ X.J)) := by
    obtain ⟨C, hC, hsub⟩ := GlobalTheory.T.relatively_compact_stabilizer F E σ B n X r s hB hX
    exact hC.of_isClosed_subset (isClosed_stabK B X (GlobalTheory.T.isClosed_adelic_lattice_closure F E n X hX.lat)) hsub
  obtain ⟨μK, hμK⟩ := exists_haar_of_isCompact _ hc
  obtain ⟨μ, hμ⟩ := exists_haar_idele (F := F) (E := E)
  exact ⟨stabK B X, μK, μ, isStab_stabK B X, hc, hμK, hμ⟩

end GlobalTheory.StabHaar
