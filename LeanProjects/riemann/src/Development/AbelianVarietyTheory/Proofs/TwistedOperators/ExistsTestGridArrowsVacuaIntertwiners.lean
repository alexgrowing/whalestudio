import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NodeAgree
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsWRepOfNegSp
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsVacX
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsNonzeroRealIntertwinerGridArrowStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsWeilRowArrow
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsVacThRows
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridRowArrowExistsCommonRealIntertwinerStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsWeilOfEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsVacOfNodeAgree
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsColIntertwiner
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsWrepOfEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsVacTrueOfAgree
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDownArrowRealIntertwinerWithAdjointStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChainStepCharactersEqGridRowZeroRanks
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChainIntertwinersRowZeroUnitVacua
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsGridCosetDataEqWeilCosetVectorsStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GridJoin

theorem exists_arrows : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → HostHyp D → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ {F : Face D A}, GlobalTheory.Hk3.Core R F → sc.cGap = 1 → ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ G : GlobalTheory.Grid.GridPre R, G.IsSpaces → G.IsChars → SpAgree G W → (∀ i, i < D.R.m → ∀ κ : G'.CosAt i, IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) G.idem (latO (G'.pS (.chi i 0)) (G'.pT (.chi i 0)) (G'.latS (.chi i 0) : Set _) (G'.latT (.chi i 0) : Set _) fun _ => True) 1 (W.vac i) (cosInd G.idem κ) (W.cosVec i κ)) → ∃ X ωT vacT ItT ωC vacC ItC dn ItU vC, (withArr G X ωT vacT ItT ωC vacC ItC dn ItU vC).IsArrows ∧ (withArr G X ωT vacT ItT ωC vacC ItC dn ItU vC).IsData ∧ ArrAgree (withArr G X ωT vacT ItT ωC vacC ItC dn ItU vC) W := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc hDC hHC hH hS F hR hsc G' W hW G hsp hch hag hcos
  have wX := GlobalTheory.GridJoin.exists_omX_of_agree hDC hHC hH hR hsc W hW G hsp hch hag hcos
  have vX := GlobalTheory.GridJoin.exists_vacX hDC hHC hH hR hsc W hW G hsp hch hag hcos
  have iX := GlobalTheory.T.exists_nonzero_real_intertwiner_grid_arrow hDC hHC hH hS hR hsc W hW G hsp hch hag hcos
  have wT := GlobalTheory.JoinArrows.exists_weil_rowArrow hDC hHC hH hR hsc W hW G hsp hch hag hcos
  have vT := GlobalTheory.GridJoin.exists_isVac_th_rows hDC hHC hH hR hsc W hW G hsp hch hag hcos
  have iT := GlobalTheory.T.gridRowArrow_exists_common_realIntertwiner hDC hHC hH hS hR hsc W hW G hsp hch hag hcos
  have wC := GlobalTheory.GridJoin.omCol_of_weil hDC hHC hH hR hsc W hW G hsp hch hag hcos
  have vC := GlobalTheory.GridJoin.exists_isVac_col hDC hHC hH hR hsc W hW G hsp hch hag hcos
  have iC := GlobalTheory.GridJoin.ColIt.exists_col_intertwiner hDC hHC hH hR hsc W hW G hsp hch hag hcos
  have wD := GlobalTheory.GridJoin.core_arrows_weil hDC hHC hH hR hsc W hW G hsp hch hag hcos
  have vD := GlobalTheory.GridJoin.exists_isVac_down hDC hHC hH hR hsc W hW G hsp hch hag hcos
  have iD := GlobalTheory.T.exists_downArrow_realIntertwiner_with_adjoint hDC hHC hH hR hsc W hW G hsp hch hag hcos
  have r0w := GlobalTheory.GridJoin.testGridRowZeroArrows_weil_vacua_agree hDC hHC hH hR hsc W hW G hsp hch hag hcos
  have r0i := GlobalTheory.GridJoin.RowArrows.chainIntertwiners_rowZero_unitVacua hDC hHC hH hR hsc W hW G hsp hch hag hcos
  have dT := GlobalTheory.T.exists_gridCosetData_eq_weilCosetVectors hDC hHC hH hR hsc W hW G hsp hch hag hcos
  have hXa : ∀ i j, ∃ a : GlobalTheory.Grid.ArrS (G.V (i + 1) j) (G.V i j), i < D.R.m → j ≤ D.R.m →
      a.Is R.ψ R.θ true (G.chiAt (D.R.m - i) (rkV D (i + 1) j)) (G.chiAt (D.R.m - i) (rkV D i j)) ∧
      HEq (a.ω.toSgn true) (W.om (.chi i j)) ∧ (j = 0 → HEq a.vac (W.vac i)) := by
    intro i j
    by_cases h : i < D.R.m ∧ j ≤ D.R.m
    · obtain ⟨ω, hω, hωa⟩ := wX i j h.1 h.2
      obtain ⟨f, hf, hf0⟩ := vX i j h.1 h.2
      obtain ⟨It, hIt⟩ := iX i j h.1 h.2 ω f hω hf
      exact ⟨⟨ω, f, It⟩, fun _ _ => ⟨⟨hω, hf, hIt⟩, hωa, hf0⟩⟩
    · exact ⟨⟨1, 0, 0⟩, fun a b => absurd ⟨a, b⟩ h⟩
  choose X hX using hXa
  have hTa : ∀ i j, ∃ (ω : T → GlobalTheory.Grid.WRep (G.nV i j).V (G.nV i (j + 1)).V) (f : WO (G.nV i j).V (G.nV i (j + 1)).V → ℂ)
      (It : GlobalTheory.Grid.Pol (G.nV i j) (G.nV i (j + 1)) →ₗ[ℂ] SmT (G.nV i (j + 1)).M →ₗ[ℂ] SmT (G.nV i j).M),
      i + 1 ≤ D.R.m → j < D.R.m → ∀ t, (⟨ω t, f, It⟩ : GlobalTheory.Grid.ArrS (G.nV i j) (G.nV i (j + 1))).Is R.ψ R.θ false
        (GlobalTheory.Grid.GridPre.muAt R t (j + 1) (rkV D (i + 1) j)) (GlobalTheory.Grid.GridPre.muAt R t (j + 1) (rkV D (i + 1) (j + 1))) ∧
        HEq (ω t) (W.om (.mu t (i + 1) j)) := by
    intro i j
    by_cases h : i + 1 ≤ D.R.m ∧ j < D.R.m
    · choose ω hω hωa using fun t => wT t i j h.1 h.2
      obtain ⟨f, hf⟩ := vT i j h.1 h.2
      obtain ⟨It, hIt⟩ := iT i j h.1 h.2 ω f hω hf
      exact ⟨ω, f, It, fun _ _ t => ⟨⟨hω t, hf, hIt t⟩, hωa t⟩⟩
    · exact ⟨fun _ => 1, 0, 0, fun a b => absurd ⟨a, b⟩ h⟩
  choose ωT vacT ItT hT using hTa
  have hCa : ∀ j, ∃ (ω : T → GlobalTheory.Grid.WRep (G.Xp j).V (G.nX j).V) (f : WO (G.Xp j).V (G.nX j).V → ℂ)
      (It : GlobalTheory.Grid.Pol (G.Xp j) (G.nX j) →ₗ[ℂ] SmT (G.Xp j).M →ₗ[ℂ] SmT (G.nX j).M),
      j < D.R.m → ∀ t, (⟨ω t, f, It⟩ : GlobalTheory.Grid.ArrT (G.Xp j) (G.Xp (j + 1))).Is R.ψ R.θ false
        (R.toLevCh.mu t (j + 1)) (R.toLevCh.mu t (j + 1)) ∧ HEq (ω t) (W.om (.top t j)) := by
    intro j
    by_cases h : j < D.R.m
    · choose ω hω hωa using fun t => wC t j h
      obtain ⟨f, hf⟩ := vC j h
      obtain ⟨It, hIt⟩ := iC j h ω f hω hf
      exact ⟨ω, f, It, fun _ t => ⟨⟨hω t, hf, hIt t⟩, hωa t⟩⟩
    · exact ⟨fun _ => 1, 0, 0, fun a => absurd a h⟩
  choose ωC vacC ItC hC using hCa
  have hDa : ∀ i, ∃ (a : GlobalTheory.Grid.ArrT (G.P (i + 1)) (G.P i))
      (U : GlobalTheory.Grid.Pol (G.P (i + 1)) (G.P i) →ₗ⋆[ℂ] SmT (G.P i).M →ₗ[ℂ] SmT (G.P (i + 1)).M), i < D.R.m →
      a.Is R.ψ R.θ true (G.chi (D.R.m - i)) (G.chi (D.R.m - i)) ∧ a.IsAdj U ∧ HEq (a.ω.toSgn true) (W.om (.core i)) := by
    intro i
    by_cases h : i < D.R.m
    · obtain ⟨ω, hω, hωa⟩ := wD i h
      obtain ⟨f, hf⟩ := vD i h
      obtain ⟨It, U, hIt, hU⟩ := iD i h ω f hω hf
      exact ⟨⟨ω, f, It⟩, U, fun _ => ⟨⟨hω, hf, hIt⟩, hU, hωa⟩⟩
    · exact ⟨⟨1, 0, 0⟩, 0, fun a => absurd a h⟩
  choose dn ItU hD using hDa
  have hVa : ∀ i, ∃ v : G.toGridSp.Cos R i → (WO (G.V (i + 1) 0).V (G.V i 0).V → ℂ), i < D.R.m →
      (∀ c, GlobalTheory.Grid.IsCosetVec R.ψ true (G.V (i + 1) 0) (G.V i 0) G.idem (G.lvl R) c (X i 0).vac (v c)) ∧
      (∀ c, ∃ κ, HEq (v c) (W.cosVec i κ)) ∧ ∀ κ, ∃ c, HEq (v c) (W.cosVec i κ) := by
    intro i
    by_cases h : i < D.R.m
    · obtain ⟨v, hv⟩ := dT i h (X i 0).vac ((hX i 0 h (Nat.zero_le _)).2.2 rfl)
      exact ⟨v, fun _ => hv⟩
    · exact ⟨fun _ _ => 0, fun h' => absurd h' h⟩
  choose vCo hvC using hVa
  refine ⟨X, fun t i j => ωT i j t, vacT, ItT, fun t j => ωC j t, vacC, ItC, dn, ItU, vCo,
    ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · exact fun i j hi hj => (hX i j hi hj).1
  · intro t i j hi hj
    cases i with
    | zero => exact ⟨(r0w t j hj).1, (r0w t j hj).2.1, r0i t j hj⟩
    | succ i => exact (hT i j hi hj t).1
  · exact fun t j hj => (hC j hj t).1
  · exact fun i hi => (hD i hi).1
  · exact fun i hi => (hD i hi).2.1
  · exact fun i hi c => (hvC i hi).1 c
  · exact fun i j hi hj => (hX i j hi hj).2.1
  · intro t i j hi hj
    cases i with
    | zero => exact (r0w t j hj).2.2
    | succ i => exact (hT i j hi hj t).2
  · exact fun t j hj => (hC j hj t).2
  · exact fun i hi => (hD i hi).2.2
  · exact fun i hi => (hX i 0 hi (Nat.zero_le _)).2.2 rfl
  · exact fun i hi => (hvC i hi).2

end GlobalTheory.GridJoin

end
