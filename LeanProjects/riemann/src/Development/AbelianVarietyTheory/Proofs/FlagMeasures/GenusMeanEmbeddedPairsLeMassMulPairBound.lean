import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PerRowC
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiscNResNeZero
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsCMFieldOfStar
import Formalism.SharpRestriction.CuspSpanNormBounds.KappaEndpoints
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.KappaEndpoints Formalism.L2.SG.RowsConc GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PairsRow

theorem main : GlobalTheory.Mass.MaxMass → Formalism.HermitianLatticesTheory.SiegelMassRatio → HostC → LatticeNormalizationCondition →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Std D large₂ →
    ∀ (W : Submodule D.host.E (VS D).V) (HW : Formalism.HermitianLatticeCounting.S6.HermSpace D.host.E W), GlobalTheory.DegAsm.IsEmb (F0 X u) HW W.subtype →
    Module.finrank D.host.E W = D.R.k → GlobalTheory.Mass.PD HW.B.flip → ∀ Λ ∈ Y.what₂ u, ∀ x x' : ℕ, 1 ≤ x → 1 ≤ x' →
      GlobalTheory.Mass.orbSum (Formalism.HermitianLatticesTheory.isom HW.B.flip) (Formalism.HermitianLatticesTheory.genus HW.B.flip (GlobalTheory.DegAsm.lat0 (F0 X u) W.subtype Λ))
                   (fun L => (((GlobalTheory.DegCnt.Trip HW (gS D) L D.R.rS x x').encard : ℕ∞) : ℝ≥0∞)) ≤
        ENNReal.ofReal (Formalism.HermitianLatticesTheory.mass HW.B.flip (GlobalTheory.DegAsm.lat0 (F0 X u) W.subtype Λ) *
          GlobalTheory.DegAsm.pairBd D.host.E D.R.k (gS D) D.R.rS (Tu D u) x x') := by
  intro hMax hSi hHost hLat D large₂ X Y u hStd W HW hEmb hk hpd Λ hΛ x x' hx hx'
  obtain ⟨hK, -, -, hv1, -, -, -, -, -, -, -, hg, hT⟩ := hHost D large₂ hStd
  have hv : 1 ≤ Formalism.HermitianLatticesTheory.vInv D.host.E := by
    rw [(hHost D large₂ hStd).2.2.1]; exact hv1
  obtain ⟨hTp, hTP⟩ := hT u
  obtain ⟨hI, he⟩ := hLat D large₂ X Y u hStd W HW hEmb Λ hΛ
  have hk3 : 3 ≤ Module.finrank D.host.E W := by
    rw [hk]; have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have : FiniteDimensional D.host.E W := Module.finite_of_finrank_pos (by omega)
  have h := GlobalTheory.DegCnt.PairMean.main Formalism.MainNotions.KappaEndpoints.mk_core hMax hSi D.host.E W HW hK
    (GlobalTheory.OrthoLattice.hasOrtho D.host.E hK) hv hpd hk3 (Tu D u) (GlobalTheory.DegAsm.lat0 (F0 X u) W.subtype Λ) _ hTp hTP hI he rfl
    _ rfl (gS D) D.R.rS x x' _ hg hx hx' rfl
  rw [hk] at h
  refine h.trans (le_of_eq ?_)
  unfold GlobalTheory.DegAsm.pairBd
  simp only [mul_assoc]

end GlobalTheory.PairsRow
