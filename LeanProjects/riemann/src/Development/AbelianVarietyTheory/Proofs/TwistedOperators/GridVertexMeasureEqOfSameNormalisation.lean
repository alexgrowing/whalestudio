import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpqLocallyCompactGroup
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsChainPols
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.HaarNorm

theorem measLevW_unique {D : D7} (V : HSp D) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D)))
    (good : ∀ ρ : D.what₂.Tau, Measure (UpqT (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2) → Prop)
    (hg : ∀ ρ m, good ρ m → m.IsHaarMeasure) {μ μ' : Measure (GA D V)}
    (h : Formalism.IndefR.Lev.IsMeasLevW V K good μ) (h' : Formalism.IndefR.Lev.IsMeasLevW V K good μ') : μ = μ' := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  obtain ⟨hμ, ⟨θ, hθ⟩, hθall⟩ := h
  obtain ⟨⟨A, hA⟩, hAall⟩ := hθall θ hθ
  obtain ⟨⟨m, hm⟩, hmall⟩ := hAall A hA
  have e := hmall m hm
  have e' := ((h'.2.2 θ hθ).2 A hA).2 m hm
  have hμ' := h'.1
  have hB : ∀ ρ : D.what₂.Tau, ∃ B : Set (UpqT (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2),
      MeasurableSet B ∧ m ρ B ≠ 0 ∧ m ρ B ≠ ⊤ := by
    intro ρ
    obtain ⟨j1, j2, j3, -, j5, -⟩ := GlobalTheory.UpqTopology.upq_lcsc (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2
    haveI := hg ρ (m ρ) (hm ρ)
    obtain ⟨C, hC, hC1⟩ := exists_compact_mem_nhds (1 : UpqT (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2)
    exact ⟨C, hC.measurableSet, (by first | exact (Measure.measure_pos_of_mem_nhds (m ρ) hC1).ne' | exact (measure_pos_of_nonempty_interior (m ρ) ⟨1, mem_interior_iff_mem_nhds.2 hC1⟩).ne'), hC.measure_lt_top.ne⟩
  choose B hBm hB0 hBt using hB
  set S := {h : GA D V | Lev.finE V h ∈ K ∧
      ∀ ρ, ∃ b ∈ B ρ, UpqT.mat b * A ρ = A ρ * infMat D.sp.cm.sig V.gram (θ ρ) h}
  have hS : μ S = ∏ ρ, m ρ (B ρ) := e B hBm
  have hS' : μ' S = ∏ ρ, m ρ (B ρ) := e' B hBm
  have hp0 : ∏ ρ, m ρ (B ρ) ≠ 0 := Finset.prod_ne_zero_iff.2 fun ρ _ => hB0 ρ
  have hpt : ∏ ρ, m ρ (B ρ) ≠ ⊤ := ENNReal.prod_ne_top fun ρ _ => hBt ρ
  have hc := Measure.isMulLeftInvariant_eq_smul μ' μ
  have hcS : μ' S = (Measure.haarScalarFactor μ' μ : ENNReal) * μ S := by
    conv_lhs => rw [hc]
    rfl
  rw [hS, hS'] at hcS
  have hc1 : (Measure.haarScalarFactor μ' μ : ENNReal) = 1 := by
    have := (ENNReal.mul_left_inj hp0 hpt).1 (hcS.symm.trans (one_mul _).symm)
    exact this
  rw [hc, ENNReal.coe_eq_one.1 hc1, one_smul]

theorem vol_nu_eq_of_isAt : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (M M' : Vol G) (X : Node) (K : Subgroup (GL (Fin (G.V X).rank) (Lev.EAf D))), M.IsAt X K → M'.IsAt X K → M.ν X = M'.ν X := by
  intro D T L sc G M M' X K h h'
  unfold GlobalTheory.FunObj.Vol.IsAt at h h'
  split_ifs at h h'
  · exact measLevW_unique _ _ _ (fun _ _ hm => hm.1) h.1 h'.1
  · exact measLevW_unique _ _ _ (fun _ _ hm => hm.1) h.1 h'.1

end GlobalTheory.HaarNorm
