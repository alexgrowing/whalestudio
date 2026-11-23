import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.SmoothGaloisGeometry.CompSm
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.SmoothGaloisGeometry.SmoothSndOfIsStrictlySemistable
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.SmoothGaloisGeometry.SsModelAlgebraMapInjective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SemistableGenericFibreLocalizationStatement

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

namespace CrystallineSemistableComparison

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem Model.smooth_q [FiniteDimensional ℚ_[l] K] (M : Model l K) (hM : M.Good) : Smooth M.q := by
  obtain ⟨-, ϖ, hϖ, hss⟩ := hM
  have := OK_away hϖ
  have := OK_dvr (l := l) (K := K)
  exact smooth_snd_of_isStrictlySemistable ϖ M.p hss
    (fun m r h1 h2 ↦ GlobalTheory.T.semistable_generic_fibre_localization (OK l K) ϖ hϖ m r h1 h2 K)

theorem compGood : ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K],
    CompM (Model.Good (l := l) (K := K)) := by
  intro l _ K _
  refine compM_of _ isOpenImmersion_gen (fun M hM U hU ↦ M.good_sub hM U hU) (fun M hM ↦ M.noetherianSpace hM) ?_
  intro M hM
  have := good_flat M hM
  exact ⟨good_isNormalScheme M hM, good_isLocallyNoetherian M hM, Flat.generalizingMap M.p, M.smooth_q hM⟩

end CrystallineSemistableComparison
