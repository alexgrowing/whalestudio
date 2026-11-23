import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HBdNonneg
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestSupportFamiliesStaircaseCosets
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevRowSuccInfUA
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.StabOfMemCongLev
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstVertexParahoricLevelChainTwist
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealDivEqRelIndex
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricChainProjectedLevelOfPattern
import Formalism.LocalToGlobal.IndefiniteReal.ThPinsEx
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.LevTopCong

open GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx

theorem KO_le_symPr {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {G : Grid k} (hs : 1 ≤ G.s) (J : G.Level) (g : G.VertexGroup) {j : ℕ} (hj : j < G.m)
    (hJ : J (G.m, j) = KO k _)
    (hc : ∀ x : GL (Fin (topRank G j)) k, toFrame hs hj (g (G.m, j)) * embX (G.m - 1 - j) x =
      embX (G.m - 1 - j) x * toFrame hs hj (g (G.m, j))) :
    KO k (Fin (topRank G j)) ≤ symPr (conjLevel hs J g hj) := by
  intro x hx
  refine ⟨1, one_mem _, ?_⟩
  rw [one_mul, conjLevel, Subgroup.map_equiv_eq_comap_symm', Subgroup.mem_comap]
  refine ⟨(g (G.m, j))⁻¹ * (toFrame hs hj).symm (embX _ x) * g (G.m, j), ?_, ?_⟩
  · rw [hJ]
    have e : toFrame hs hj ((g (G.m, j))⁻¹ * (toFrame hs hj).symm (embX _ x) * g (G.m, j)) = embX _ x := by
      rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, mul_assoc, ← hc, ← mul_assoc, inv_mul_cancel, one_mul]
    exact OneCosetProof.mem_KO_of_frameGL _ (by
      have := GlobalTheory.TwistVertex.embX_mem_KO (c := G.m - 1 - j) hx
      rw [← e] at this
      exact this)
  · simp [mul_assoc]

end GlobalTheory.LevTopCong

namespace GlobalTheory.LevTopCong

open GlobalTheory.SplitWeil GlobalTheory.RootEx

theorem diag_comm_embX {k : Type} [Field k] {n : ℕ} {c : ℕ} (d : Fin c → kˣ) (x : GL (Fin n) k) :
    GlobalTheory.SplitFlip.diagGL (Sum.elim (fun _ => (1 : kˣ)) d) * embX c x =
      embX c x * GlobalTheory.SplitFlip.diagGL (Sum.elim (fun _ => (1 : kˣ)) d) := by
  refine Units.ext ?_
  have e : (diagonal fun i => ((Sum.elim (fun _ => (1 : kˣ)) d i : kˣ) : k)) =
      fromBlocks (1 : Matrix (Fin n) (Fin n) k) 0 0 (diagonal fun p => (d p : k)) := by
    ext (i | i) (j | j) <;> simp [Matrix.diagonal_apply, Matrix.one_apply]
  have hx : (embX c x).val = fromBlocks x.val 0 0 1 := rfl
  rw [Units.val_mul, Units.val_mul, GlobalTheory.SplitFlip.diagGL_val, e, hx, fromBlocks_multiply, fromBlocks_multiply]
  simp

end GlobalTheory.LevTopCong

namespace GlobalTheory.LevTopCong

open GlobalTheory.SplitWeil GlobalTheory.RootEx

theorem KO_le_pr_stair {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] {G : GlobalTheory.SplitFlip.Grid k} (hs : 1 ≤ G.s) (J : G.Level)
    (hJ : ∀ j, 0 < j → j < G.m → J (G.m, j) = KO k _) (ϖ : kˣ) (e : ℕ) (β : Cosets hs J)
    (hβ : ∀ i, β i = DoubleCoset.mk _ _ (stair G ϖ e (i + 1))) {j : ℕ} (hj0 : 0 < j) (hj : j < G.m) :
    KO k (Fin (topRank G j)) ≤ symPr (conjLevel hs J ((Reps.through hs J (stair G ϖ e)).elt β) hj) := by
  refine KO_le_symPr hs J _ hj (hJ j hj0 hj) fun x => ?_
  obtain rfl : β = fun i : Fin (G.m - 2) => DoubleCoset.mk _ _ (stair G ϖ e (i + 1)) := funext hβ
  by_cases h2 : j + 2 ≤ G.m
  · rw [through_elt _ h2, toFrame_stair]
    exact diag_comm_embX _ _
  · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    have e1 : (Reps.through hs J (stair G ϖ e)).elt (fun i : Fin (G.m - 2) => DoubleCoset.mk _ _ (stair G ϖ e (i + 1))) (G.m, i + 1) = 1 := by
      rw [Reps.elt, onColumn_apply]
      simp [show ¬ i < G.m - 2 by omega]
    rw [e1, map_one, one_mul, mul_one]

end GlobalTheory.LevTopCong

open GlobalTheory.SplitWeil in

theorem GlobalTheory.LevTopCong.congLev_le_levTop : ∃ CF0 : ℝ, ∀ CF : ℝ, CF0 ≤ CF → ∀ ε : ℝ, ∃ x₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D), large₂.sc.eps = ε → x₀ ≤ large₂.sc.x → ∀ (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 T : Type) (A : FamIn D.what₂.LL Γ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), HidaSetting large₂ R F → ∀ ch : Choice R, ch.Is → ch.AtScale CF large₂.sc.b → ch.FieldOK → ∀ (Φ : ch.G.Datum), ∀ β ∈ ch.S.supp A.μ0 Φ, ∀ j : Fin D.R.m, congLev D.sp.cm (ch.G.V (.top j)).gram (ch.G.Λ (.top j)) ch.G.modul ≤ ch.S.levTop A.μ0 Φ β j j.2 := by
  obtain ⟨CF0, hB⟩ := GlobalTheory.RowVal.oneAt
  refine ⟨CF0, fun CF hCF ε => ?_⟩
  obtain ⟨x₀, hx⟩ := hB ε CF hCF
  refine ⟨x₀, fun D large₂ hε hx0 Γ _ _ Pl0 T A Ks _ _ _ R F s ch hch hsc _ Φ β hβ j => ?_⟩
  have hone := hx D large₂ hε hx0 Γ Pl0 T A Ks R F s ch hch hsc A.μ0 Φ β hβ
  have hL : R.toLevCh.Is A.μ0 := s.core.lev
  have hQ : R.Q A.μ0 = ∅ := Formalism.IndefR.FWT.Q_base_empty R hL
  obtain ⟨j, hj⟩ := j
  cases j with
  | zero => exact le_rfl
  | succ j =>
    intro g hg
    have hfr := ch.S.βp_is (j + 1) hj.le
    have hSt : g ∈ St (ch.S.βp (j + 1)) :=
      (GlobalTheory.LevSplit.mem_St_iff _ _ hfr g).2 (GlobalTheory.CongMember.stab_of_mem_congLev hg)
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_iInf.2 fun w => ?_,
      Subgroup.mem_iInf.2 fun w' => Subgroup.mem_iInf.2 fun _ => LevRowSucc.KO_of_St rfl _ _ hSt⟩
    have hw0 : w.1 ∈ ch.G.pl.W0 := by
      have h2 := w.2
      simp only [locPl, Finset.mem_union] at h2
      rcases h2 with h2 | h2
      · exact h2
      · have h4 : (w : Pl D.host.E) ∈ R.Q A.μ0 := h2
        rw [hQ] at h4
        exact absurd h4 (Finset.notMem_empty _)
    refine GlobalTheory.LevTopCong.KO_le_pr_stair one_le_sLen _
      (fun i hi0 hi => GlobalTheory.RowVal.givenLevel_inner _ _ _ _ (by change 1 ≤ D.R.m; omega) hi0) _ _ (β w) (hone w hw0)
      j.succ_pos hj ?_
    exact LevRowSucc.KO_of_St _ _ _ hSt
