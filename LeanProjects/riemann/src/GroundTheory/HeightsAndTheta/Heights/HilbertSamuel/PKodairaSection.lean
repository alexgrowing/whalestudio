import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsKodairaSection
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsKodairaGeneric
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsChartDenominator
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSectionSupBound
import GroundTheory.HeightsAndTheta.Heights.Intersections.Statements
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsAntisym
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem nefOnGenericDeg_of_semipos (hN : NefOnGenericOfSemipos.Statement)
    (hD : GroundTheory.Heights₂.Heights.Inter.DegreeGeneric.Statement) {P P0 : Ideal (MRing ι)} {M : HermLine ι}
    (hP0 : P0 ≤ P) (hs : IsSemipositiveRel P0 P M) : NefOnGenericDeg P M.a := by
  classical
  intro W hW hPW
  have h1 : 0 ≤ geomDeg W M 1 := hN K ι P P0 M hP0 hs W hW hPW
  have h2 := hD K ι W 1 (fun _ => M) hW (fun _ => hs.1)
  have h3 : geomDeg W M 1 = (genDeg W 1 M.a : ℝ) := by
    rw [geomDeg, genDeg]
    convert h2 using 2
    rfl
  exact_mod_cast h3 ▸ h1

theorem continuousOn_zcomb_fsH {M : HermLine ι} (hM : IsSmoothHerm M) (k : ℤ) :
    ContinuousOn (HermLine.zcomb M (fsH ι) k (-1)).h {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  have hH : ContinuousOn (fsH ι).h {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} :=
    (GroundTheory.Heights₂.Heights.Inter.isSmoothHerm_ofMetrics_fs (ι := ι) 1).continuousOn
  exact (hM.continuousOn.zpow₀ k fun z hz => Or.inl (M.pos z hz).ne').mul
    (hH.zpow₀ (-1) fun z hz => Or.inl ((fsH ι).pos z hz).ne')

theorem KodairaSection.proof (hN : NefOnGenericOfSemipos.Statement)
    (hD : GroundTheory.Heights₂.Heights.Inter.DegreeGeneric.Statement) (hK : KodairaGeneric.Statement)
    (hC : ChartDenominator.Statement) (hS : SectionSupBound.Statement) : KodairaSection.Statement := by
  intro K _ ι _ Ω _ _ y D M P0 hD1 har hb hM
  obtain ⟨k, e, hk, he0, heQ⟩ :=
    hK K ι Ω y D M.a hD1 har hb (nefOnGenericDeg_of_semipos hN hD hM.normalForm_baseLattice_le_dualSpan_sup_line hM.semipos) hM.big
  obtain ⟨n, hn, hne⟩ := hC K ι Ω y _ 1 e heQ
  have ha : (HermLine.zcomb M (fsH ι) k (-1)).a = (k : ℤ) • M.a - 1 := by
    funext i
    simp [HermLine.zcomb, fsH, HermLine.ofMetrics]
    ring
  obtain ⟨C, hC0, hB⟩ := hS K ι Ω y (HermLine.zcomb M (fsH ι) k (-1)) 1 ((n : Ω) * e)
    (continuousOn_zcomb_fsH hM.semipos.1 k) (by rw [ha]; exact hne)
  exact ⟨k, (n : Ω) * e, C, hk, hC0, mul_ne_zero (Nat.cast_ne_zero.mpr (by omega)) he0, hne, hB⟩

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
