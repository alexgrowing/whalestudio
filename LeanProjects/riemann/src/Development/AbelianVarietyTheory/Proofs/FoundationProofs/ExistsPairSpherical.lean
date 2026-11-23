import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SphericalPair
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes

noncomputable section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

namespace GlobalTheory.NormSum.Inhab

theorem om_vac {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (hc : Crv D cc δ) {a d : ℕ}
    {e0 : VC D a d → ℂ} (he : e0 ∈ Th D (tor0 D cc δ) (stdL D a) (stdL D d)) (W : WeilO D cc δ a d e0)
    (h1 : ∀ u, IntU D u → W.chV.f u = 1) (h2 : ∀ u, IntU D u → W.chV'.f u = 1)
    (k : GA D a) (hk : k ∈ intG D a) (k' : GA D d) (hk' : k' ∈ intG D d) : W.Om k k' e0 = e0 := by
  obtain ⟨x, x', hx, hx', h⟩ := (VacInt.vacuum_eigen D (GlobalTheory.InducedType.induced_type D).1 cc δ hc a d e0 he W).2.1 k hk k' hk'
  rw [h, h1 x' hx', h2 x hx]
  simp

end GlobalTheory.NormSum.Inhab
