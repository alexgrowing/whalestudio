import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGAnalytic
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.DataInst
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.InVolumesAtOfSWS
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GlobSet
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.FormulaExplicitAtOfEta
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DensAtD
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BinaryHermitianFormRepresentsTotallyPositive
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.FormulaCOf
import Formalism.HermitianCurvature.HeisenbergConjugationMeasurePreserving
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.TermLoc Formalism.L2.SG.RowsConc Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.FourierDecayAlt GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical ENNReal
open ValuativeRel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.GlueCount

def locSpOf {D : D7} (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (hA : ∀ p, Agree δ M p) : Formalism.L2.SG.CntLocal.LocSp D M where
  V := Vp D
  H p := locHerm M p (hA p).2.2.1
  rank := finrank_Vp
  bc := baseChange₂ D
  bc_smul := baseChange_smul₂
  bc_span := span_baseChange_eq_top
  bc_form p x y := baseChangeAt_form M p (hA p).2.2.1 x y

theorem exists_unif_at {D : D7} (p : PlF D) : ∃ ϖ : 𝒪[(D.s.atP p).Fp], Irreducible ϖ := by
  haveI := (D.s.atP p).lf
  exact IsDiscreteValuationRing.exists_irreducible _

theorem exists_unifs (D : D7) : ∃ ϖ : ∀ p : PlF D, 𝒪[(D.s.atP p).Fp], ∀ p, Irreducible (ϖ p) :=
  ⟨fun p => (exists_unif_at p).choose, fun p => (exists_unif_at p).choose_spec⟩

theorem one_mem_stabFix {D : D7} (U : Submodule D.host.E (VS D).V) (Λ : Submodule (𝓞 D.host.E) (VS D).V) :
    (1 : (VS D).V ≃ₗ[D.host.E] (VS D).V) ∈ Formalism.L2.SG.Pf.Cnt.stabFix (VS D).hT U Λ := by
  refine ⟨(Formalism.L2.SG.Pf.Cnt.isomFix (VS D).hT U).one_mem, ?_⟩
  ext x
  simp [Formalism.HermitianLatticesTheory.gmap]

section Reps
open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.Asm Formalism.L2.SG.CntLocal Module

theorem exists_glueReps (D : D7) (u u' : D.what₂.Word) (hT : (D.mem u).A.T ≡ (D.mem u').A.T [MOD (gS D) ^ 2])
    (F0 : FlagG (VS D) D.R.rS (Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) (hR : IsRowReps D F0 what₂)
    (G' : LFlag (VS D) D.R.rS (Tn u')) (hz : G'.zt = G'.fl.z) (hP : Formalism.MainNotions.S.LocalSplitGroups.TotPos (GZ (Tn u) (Tn u') (ZhatL (lf D F0) G'))) :
    ∃ s, IsGlueReps (VS D).hT (UPair D F0 G') (MMof D F0 G') s := by
  haveI : Fact HermRepUnram := ⟨GlobalTheory.BinaryRep.represents_totallyPositive⟩
  obtain ⟨hLat, -⟩ := mmChar_of local_unimodular_holds D u u' hT F0 what₂ hR _ G' hz rfl hP
  by_cases hI : Formalism.HermitianLatticesTheory.IsIntegralLat (VS D).hT (MMof D F0 G')
  · obtain ⟨hK, hF, hN⟩ := field_dictionary_holds D
    obtain ⟨hC, hPD, hUr, hWr⟩ := perpendicular_definition_holds D u u' hT F0 what₂ hR _ G' hz rfl hP
    have hk : D.R.m + 3 ≤ D.R.k := D.R.m_add_three_le_k
    have hcJ : ∀ 𝔭 : Ideal (𝓞 D.host.F), 𝔭.IsMaximal →
        cJ (VS D).hT (UPair D F0 G') (MMof D F0 G') 𝔭 < finrank D.host.E (orthK (VS D).hT (UPair D F0 G')) := by
      intro 𝔭 _
      have := cJ_le (VS D).hT (UPair D F0 G') (MMof D F0 G') 𝔭
      rw [hWr]
      omega
    have hne := glueExists_holds D.host.E D.host.F (VS D).V hK hF (VS D).hT (VS D).herm hN (UPair D F0 G') hC hPD
      ⟨(VS D).L0, (VS D).standardTuple_isLattice, (VS D).baseLattice_isUnimodular⟩ (MMof D F0 G') hLat hI hcJ
    have hMC : MassConst D.host.E D.host.F (finrank D.host.E (orthK (VS D).hT (UPair D F0 G')))
        (cMass D.host.E D.host.F (D.R.k - 1)) := by
      rw [hWr]
      exact (cMass_spec hK hF (D.R.k - 1) (by omega)).2
    obtain ⟨s, hs1, hs2, hs3, -⟩ := gluing_mass_holds D.host.E D.host.F (VS D).V hK hF (VS D).hT (VS D).herm hN
      (UPair D F0 G') hC hPD (MMof D F0 G') hLat hI hne _ hMC
    exact ⟨s, hs1, hs2, hs3⟩
  · exact ⟨∅, isGlueReps_empty (glueSet_eq_empty (U := UPair D F0 G') hI)⟩

end Reps

theorem glueSum_le : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.L2.SG.Pf.LocCP.LocTied D → 2 * D.R.rS + 2 + D.R.f + 5 ≤ D.R.k → (D.mem u).A.T ≡ (D.mem u').A.T [MOD (gS D) ^ 2] → ∀ G' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E), G'.zt = G'.fl.z → TotPos (Gval (lf D (X.Fu u)) G') → ∃ s : Finset (LV D), Glue (lf D (X.Fu u)) G' s ∧ (s.Nonempty → (∃ Λ, IsRowLat D (X.Fu u) Λ ∧ G' ∈ Formalism.L2.SG.CntLocal.EZ ((Tu D u' : ℕ) : D.host.E) (X.Fu u) Λ (ZhatL (lf D (X.Fu u)) G')) ∧ glueSum (lf D (X.Fu u)) G' s ≤ 2 * (Formalism.L2.SG.Pf.Cnt.cExpl D (X.Fu u) (Y.what₂ u) * Formalism.MainNotions.S.Cnt.massRows D (X.Fu u) (Y.what₂ u) * ∏' p, Formalism.L2.SG.DataInst.alpD u u' p) * Formalism.L2.SG.CntLocal.sqrtAbsNormOfScaledGram ((Tu D u : ℕ) : D.host.E) ((Tu D u' : ℕ) : D.host.E) (ZhatL (lf D (X.Fu u)) G') ^ (D.R.k - 1)) := by
  intro D X Y u u' hTied hk hT G' hz hTP
  haveI : Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram := ⟨GlobalTheory.BinaryRep.represents_totallyPositive⟩
  have hR : IsRowReps D (X.Fu u) (Y.what₂ u) := Y.rowsOK u
  have hP : Formalism.MainNotions.S.LocalSplitGroups.TotPos (Formalism.L2.SG.CntLocal.GZ (Formalism.L2.SG.CntLocal.Tn u) (Formalism.L2.SG.CntLocal.Tn u')
      (ZhatL (lf D (X.Fu u)) G')) := hTP
  obtain ⟨s, hs⟩ := exists_glueReps D u u' hT (X.Fu u) (Y.what₂ u) hR G' hz hP
  obtain ⟨-, hchar⟩ := Formalism.L2.SG.Pf.Cnt.mmChar_of Formalism.L2.SG.Pf.Cnt.local_unimodular_holds D u u' hT (X.Fu u) (Y.what₂ u) hR _ G'
    hz rfl hP
  have e4 := Formalism.L2.SG.Pf.Cnt.lattice_groupoid_holds D u u' hT (X.Fu u) (Y.what₂ u) hR _ G' hz rfl hP s hs
  refine ⟨s, hs, fun hne => ?_⟩
  obtain ⟨Λ, hΛ⟩ := hne
  refine ⟨⟨Λ, (hchar Λ).2 (hs.1 Λ hΛ)⟩, ?_⟩
  have hsum : glueSum (lf D (X.Fu u)) G' s = Formalism.L2.SG.CntLocal.nu (Formalism.L2.SG.CntLocal.Tn u') (X.Fu u) (Y.what₂ u)
      (ZhatL (lf D (X.Fu u)) G') * Formalism.MainNotions.S.Cnt.massRows D (X.Fu u) (Y.what₂ u) := by
    exact e4.symm
  have hpos : 0 < glueSum (lf D (X.Fu u)) G' s := by
    unfold glueSum
    refine Finset.sum_pos (fun Λ' hΛ' => ?_) ⟨Λ, hΛ⟩
    haveI : Finite (Formalism.L2.SG.Pf.Cnt.stabFix (VS D).hT (Formalism.L2.SG.Pf.Cnt.UPair D (X.Fu u) G') Λ') :=
      (hs.2.2 Λ' hΛ').to_subtype
    haveI : Nonempty (Formalism.L2.SG.Pf.Cnt.stabFix (VS D).hT (Formalism.L2.SG.Pf.Cnt.UPair D (X.Fu u) G') Λ') :=
      ⟨⟨1, one_mem_stabFix _ _⟩⟩
    exact inv_pos.2 (Nat.cast_pos.2 Nat.card_pos)
  have hnu : Formalism.L2.SG.CntLocal.nu (Formalism.L2.SG.CntLocal.Tn u') (X.Fu u) (Y.what₂ u) (ZhatL (lf D (X.Fu u)) G') ≠ 0 := by
    intro h0
    rw [hsum, h0, zero_mul] at hpos
    exact lt_irrefl _ hpos
  have hrow : ∃ Λ₁ ∈ Y.what₂ u,
      (Formalism.L2.SG.CntLocal.EZ (Formalism.L2.SG.CntLocal.Tn u') (X.Fu u) Λ₁ (ZhatL (lf D (X.Fu u)) G')).Nonempty := by
    by_contra hno
    push_neg at hno
    apply hnu
    unfold Formalism.L2.SG.CntLocal.nu
    rw [Finset.sum_eq_zero (fun Λ₁ h1 => by simp [Formalism.L2.SG.CntLocal.cntE, hno Λ₁ h1]), zero_div]
  obtain ⟨ϖ, hϖ⟩ := exists_unifs D
  have hfe := Formalism.L2.SG.Pf.formulaExplicitAt_of_eta D Formalism.L2.SG.Pf.Cnt.DualityBasisChange.frameBasisL_holds
    (fun p => Formalism.L2.SG.Pf.AlTieLG.etaLoc_of_tied hTied p) Y.δ Y.M Y.agree (locSpOf Y.δ Y.M Y.agree) u u' hT
    (X.Fu u) (Y.what₂ u) hR ϖ hϖ _ hP
  obtain ⟨-, hbdd, -, hαpos, hDI⟩ := Formalism.L2.SG.Pf.Cnt.densInputT_holds D hTied hk Y.δ Y.M Y.agree
    (locSpOf Y.δ Y.M Y.agree) u u' hT (X.Fu u) (Y.what₂ u) hR ϖ hϖ
  obtain ⟨hk2, P, q, l, hl, hS, hx⟩ := hDI
  have hsd := (Formalism.FourierDecayAlt.Final.tc_densChain Formalism.FourierDecayAlt.Final.tc_densSum Formalism.FourierDecayAlt.Final.tc_densLeTwo
    Formalism.FourierDecayAlt.Final.tc_densSize P q l _ _ _ _ hk2 hl hS hx).2
  have hdle : ∏' p, Formalism.L2.SG.CntLocal.densP (locSpOf Y.δ Y.M Y.agree) Y.δ ϖ (Formalism.L2.SG.CntLocal.Tn u)
      (Formalism.L2.SG.CntLocal.Tn u') (ZhatL (lf D (X.Fu u)) G') p ≤ 2 * ∏' p, Formalism.L2.SG.DataInst.alpD u u' p :=
    (le_csSup hbdd ⟨_, hrow, rfl⟩).trans ((div_le_iff₀ hαpos).1 hsd)
  obtain ⟨Λ₁, hΛ₁, -⟩ := hrow
  have hc : 0 < Formalism.L2.SG.Pf.Cnt.cExpl D (X.Fu u) (Y.what₂ u) :=
    Formalism.L2.SG.Pf.Cnt.cExpl_pos' D u (X.Fu u) (Y.what₂ u) hR ⟨Λ₁, hΛ₁⟩
  have hm : 0 ≤ Formalism.MainNotions.S.Cnt.massRows D (X.Fu u) (Y.what₂ u) :=
    Finset.sum_nonneg (fun _ _ => by unfold Formalism.MainNotions.S.wRow; positivity)
  have hN : 0 ≤ Formalism.L2.SG.CntLocal.sqrtAbsNormOfScaledGram ((Tu D u : ℕ) : D.host.E) ((Tu D u' : ℕ) : D.host.E)
      (ZhatL (lf D (X.Fu u)) G') := Real.sqrt_nonneg _
  have hfe' : Formalism.L2.SG.CntLocal.nu (Formalism.L2.SG.CntLocal.Tn u') (X.Fu u) (Y.what₂ u) (ZhatL (lf D (X.Fu u)) G') =
      Formalism.L2.SG.Pf.Cnt.cExpl D (X.Fu u) (Y.what₂ u) * Formalism.L2.SG.CntLocal.sqrtAbsNormOfScaledGram ((Tu D u : ℕ) : D.host.E)
        ((Tu D u' : ℕ) : D.host.E) (ZhatL (lf D (X.Fu u)) G') ^ (D.R.k - 1) *
      ∏' p, Formalism.L2.SG.CntLocal.densP (locSpOf Y.δ Y.M Y.agree) Y.δ ϖ (Formalism.L2.SG.CntLocal.Tn u)
        (Formalism.L2.SG.CntLocal.Tn u') (ZhatL (lf D (X.Fu u)) G') p := hfe
  rw [hsum, hfe']
  calc _ = (Formalism.L2.SG.Pf.Cnt.cExpl D (X.Fu u) (Y.what₂ u) * Formalism.MainNotions.S.Cnt.massRows D (X.Fu u) (Y.what₂ u) *
        Formalism.L2.SG.CntLocal.sqrtAbsNormOfScaledGram ((Tu D u : ℕ) : D.host.E) ((Tu D u' : ℕ) : D.host.E)
          (ZhatL (lf D (X.Fu u)) G') ^ (D.R.k - 1)) *
        ∏' p, Formalism.L2.SG.CntLocal.densP (locSpOf Y.δ Y.M Y.agree) Y.δ ϖ (Formalism.L2.SG.CntLocal.Tn u)
          (Formalism.L2.SG.CntLocal.Tn u') (ZhatL (lf D (X.Fu u)) G') p := by ring
    _ ≤ (Formalism.L2.SG.Pf.Cnt.cExpl D (X.Fu u) (Y.what₂ u) * Formalism.MainNotions.S.Cnt.massRows D (X.Fu u) (Y.what₂ u) *
        Formalism.L2.SG.CntLocal.sqrtAbsNormOfScaledGram ((Tu D u : ℕ) : D.host.E) ((Tu D u' : ℕ) : D.host.E)
          (ZhatL (lf D (X.Fu u)) G') ^ (D.R.k - 1)) * (2 * ∏' p, Formalism.L2.SG.DataInst.alpD u u' p) :=
      mul_le_mul_of_nonneg_left hdle (by positivity)
    _ = _ := by ring

end GlobalTheory.GlueCount
