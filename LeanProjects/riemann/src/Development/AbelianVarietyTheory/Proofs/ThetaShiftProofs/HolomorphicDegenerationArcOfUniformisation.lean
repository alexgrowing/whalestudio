import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IdealPart
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsHolToHalfPlaneMono
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ChainLevelPtOfSection
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyChainArcWitnessUniversalFamilyStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CmpCongrOfExEq
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsIsFactor
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.SpecPtsIsFibAt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GermsSpecStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CardQkOfTateIsoQ
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.MemThetaShiftZero
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsLatticeVectorRepAndShift
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsRingHomLift
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsHolToCompClm
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PointsFramesEq
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.EqZeroOfRationalPoints
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.SpecPtsNonempty

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.HolomorphicArc

theorem main : ReciprocityTheory.ChartRestriction.G.Out.Laws → ReciprocityTheory.ChartRestriction.G.Out.Laws2 → ReciprocityTheory.ChartRestriction.G.Geo.Tor.ThetaUnifAV →
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.ToroidalArchimedeanCondition := by
  intro L₁ L₂ hU E _ _ _ H D l Xo c O _ β Y bF _ _ a χ W g ty Fu _ hty hrz hχ hgen
  letI := H.starRing
  haveI : NeZero l.A := ⟨l.A_pos.ne'⟩
  haveI : NeZero l.M := ⟨by have := l.three_le; omega⟩
  haveI := Xo.smooth
  haveI : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim Xo.s
  haveI : IsLocallyNoetherian Xo.X := LocallyOfFiniteType.isLocallyNoetherian Xo.s
  obtain ⟨Λ⟩ := GlobalTheory.ArcModel.nonempty_gtAn L₁ L₂ hU E H D l c O β _ a
  obtain ⟨C⟩ := GlobalTheory.T.nonempty_chain_arc_witness_universal_family L₁ L₂ E H D l Xo c O β Y bF a χ W Λ hχ hgen
  choose laA hA using fun v => (GlobalTheory.GtRep.exists_rep_and_shift L₁ L₂ E H D l c O β _ a Λ l.A l.A_pos).1 (a.etaA v)
  choose laM hM using fun v => (GlobalTheory.GtRep.exists_rep_and_shift L₁ L₂ E H D l c O β _ a Λ l.M (le_trans (by norm_num) l.three_le)).1 (a.eta v)
  obtain ⟨levA, levM⟩ := GlobalTheory.ArcPts.chain_levels L₁ L₂ E H D l Xo c O β Y bF a χ W Λ C laA laM hA hM
  have hfin : AnFin Λ.A := (GlobalTheory.ArcThetaSpaces.sections_theta L₁ L₂ E H D l c O β _ a Λ).2.1
  have hover : (C.yF ≫ pullback.fst _ _) ≫ Xo.s =
      spMap ((algebraMap ℂ ℂ⸨X⸩).comp (bF.comp (IntermediateField.inclusion c.le).toRingHom)) := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, C.yF_over, ← spMap_comp]
  have hrat : C.Φ.Rational := GlobalTheory.ConstRational.rational L₁ L₂ E H D l Xo Λ.A _ _ C.Φ laA laM hfin hover levA levM
  obtain ⟨Γ⟩ := GlobalTheory.T.exists_germs_localRing_convergent_divisible.1
  obtain ⟨Ψ⟩ := GlobalTheory.ArcPts.Special.specPts_nonempty L₁ L₂ E H D l _ _ Xo.X Xo.s Xo.univ Λ.A _ C.Φ Γ _ Xo.s _ hover hfin hrat
  obtain ⟨lin, cst, hfac, hEF⟩ := GlobalTheory.ArcPts.exists_isFactor _ Λ.A
  obtain ⟨T₁, hT₁, hol, hfib⟩ :=
    GlobalTheory.SpecFibre.specPts_isFibAt L₁ L₂ E H D l _ _ Xo.X Xo.s Xo.univ Λ.A _ C.Φ Γ Ψ hfin hrat lin cst hfac
  obtain ⟨TA, -, hlA⟩ := GlobalTheory.SpecLevel.level_on_fibre L₁ L₂ E H D l _ _ Xo.X Xo.s Xo.univ Λ.A _ C.Φ Γ Ψ hfin hrat l.A
  obtain ⟨TM, -, hlM⟩ := GlobalTheory.SpecLevel.level_on_fibre L₁ L₂ E H D l _ _ Xo.X Xo.s Xo.univ Λ.A _ C.Φ Γ Ψ hfin hrat l.M
  have hdim := GlobalTheory.ArcPts.finrank_V_eq L₁ L₂ E H D l c O β _ a Λ g ty hty hrz
  have hol' : IsHolTo {w : ℂ | max T₁ (max TA TM) < w.im} Ψ.yw := isHolTo_halfPlane_mono (le_max_left _ _) hol
  obtain ⟨K, -⟩ := GlobalTheory.ArcPts.exists_cmp L₁ L₂ E H D l Xo _ g ty Fu Λ.A lin cst (max T₁ (max TA TM)) Ψ.yw Ψ.pi Ψ.fr laA laM
    rfl hEF hdim hol' (by
      intro w hw
      simp only [max_lt_iff] at hw
      obtain ⟨h₁, h₂, h₃⟩ := hw
      refine ⟨?_, hfib w h₁, fun hs => ⟨fun v => hlA w h₂ hs (hfib w h₁).per _ _ ?_ (levA v),
        fun v hv => hlM w h₃ hs (hfib w h₁).per _ _ ?_ (levM v hv)⟩⟩
      · rw [Ψ.yw_eq w (hT₁.trans_lt h₁)]
        exact over_of_generic _ _ _ _ _ (by rw [Ψ.yT_gen]; exact hover)
      · rw [← map_nsmul_eq_pow _ Xo.univ.etaA_add, Xo.univ.etaA_ker]
      · rw [← map_nsmul_eq_pow _ Xo.univ.eta_add, Xo.univ.eta_ker _ (nsmul_mem v)])
  exact GlobalTheory.ArcPts.nonempty_holArc L₁ L₂ E H D l Xo c O β Y bF a χ W Λ C Γ Ψ g ty Fu laA laM K hrat hA hM lin cst T₁ hfib

end GlobalTheory.HolomorphicArc
