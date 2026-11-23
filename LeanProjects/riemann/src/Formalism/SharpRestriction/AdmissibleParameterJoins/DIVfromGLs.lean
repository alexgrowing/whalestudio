import Formalism.SharpRestriction.AdmissibleParameterJoins.DIVfromGLl
import Formalism.SharpRestriction.AdmissibleParameterJoins.DIVfromGLm
import Formalism.SharpRestriction.GlobalSchurBounds.WachTwistLocalTheory
import Formalism.SharpRestriction.GlobalSchurBounds.JointsF
import Formalism.LocalRingCardinality.IntCastDvdOfDvdIntegers

noncomputable section

namespace Formalism.MainNotions.J

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions.WeilJacquetShalikaLaw Formalism.MainNotions.WeightDegreeSizes

variable {D : D7} {L : SizeData₂ D}

theorem levelColumn_of_sharp_twisted {Dx : DivX D} {T : TwForms D} (h : ∀ u, Formalism.MainNotions.product_first_zeroth_parts.TupleChainSharpColumnValuation Dx T u) : LevelPrimeColumnOtherTuples D Dx T :=
  fun u w hw μ _ hq x hx => h u w hw μ hq x hx

theorem level_column_closed {Dx : DivX D} {T : TwForms D} (h5 : ∀ u, Formalism.MainNotions.product_first_zeroth_parts.Conclusion5Sharp D u)
    (h5T : ∀ u, Formalism.MainNotions.product_first_zeroth_parts.TupleChainSharpColumnValuation Dx T u) : ValuationAtLevelPrime D Dx T :=
  levelColumn_of_sharpBound h5 (levelColumn_of_sharp_twisted h5T)

theorem level_primes_ne_type_primes (D : D7) : LevelPrimeNotTypePrime D :=
  fun u i => (D.T_ne_g u i).symm

theorem sizeData_at_level_primes {X : ErrX D} {K : Formalism.MainNotions.G.Consts} {c : ErrC} (P : ParameterChoice' D L) (hF : L.FDef)
    (hE : L.EDef X K c) : LevelPrimeSizes D L :=
  sizeData_at_level_primes_of_defs P hF hE (level_primes_ne_type_primes D)

theorem periodBound_at_level_closed {Dx : DivX D} {T : TwForms D} {X : ErrX D} {K : Formalism.MainNotions.G.Consts} {c : ErrC} (P : ParameterChoice' D L)
    (hD : DGamDef D) (hF : L.FDef) (hE : L.EDef X K c) (hN : NuAtTDef D L) (hG : LevelPrimeCoprimeStabiliser D) (hp : PeriodClassSumWeyl D)
    (h6T : TwistedChainIntegral D T) (hpT : TwistedPeriodIntegral D Dx T) (h5 : ∀ u, Formalism.MainNotions.product_first_zeroth_parts.Conclusion5Sharp D u)
    (h5T : ∀ u, Formalism.MainNotions.product_first_zeroth_parts.TupleChainSharpColumnValuation Dx T u) (h6 : ∀ u, Formalism.MainNotions.product_first_zeroth_parts.Conclusion6 D u) : PeriodBoundAtLevelPrime D L :=
  periodBound_at_level_of_twisted hD (ETDef_of P hF hE (level_primes_ne_type_primes D)) hN hG hp h6T hpT (levelColumn_of_sharp_twisted h5T) h5 h6

theorem family_level_column_bound {eps : ℝ} (Fm : FamP eps)
    (hE : ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (hx : Fm.x1 < x) (i : Fm.Ix x),
      (∀ u, Formalism.MainNotions.product_first_zeroth_parts.Conclusion5Sharp (Fm.D x i) u) ∧ (∀ u, Formalism.MainNotions.product_first_zeroth_parts.TupleChainSharpColumnValuation (Fm.X x i) (Fm.ex x hx i).tw u) ∧
        LevelPrimeCoprimeStabiliser (Fm.D x i) ∧ ServedHasModel (Fm.Gx x i) Fm.GK) : FamilyLevelPrimeInputs Fm := by
  unfold FamilyLevelPrimeInputs
  obtain ⟨x0, h⟩ := hE
  exact ⟨x0, fun x hx0 hx i => ⟨level_column_closed (h x hx0 hx i).1 (h x hx0 hx i).2.1,
    sizeData_at_level_primes (Fm.params x hx i) (Fm.ex x hx i).fdef (Fm.ex x hx i).err.edef,
    (h x hx0 hx i).2.2.1, (h x hx0 hx i).2.2.2⟩⟩

theorem family_pairing_integrality {eps : ℝ} (Fm : FamP eps)
    (hE : ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (hx : Fm.x1 < x) (i : Fm.Ix x),
      (∀ u, Formalism.MainNotions.product_first_zeroth_parts.Conclusion6 (Fm.D x i) u) ∧ TwistedChainIntegral (Fm.D x i) (Fm.ex x hx i).tw ∧ PeriodClassSumWeyl (Fm.D x i) ∧
        TwistedPeriodIntegral (Fm.D x i) (Fm.X x i) (Fm.ex x hx i).tw) : familyPairing Fm := by
  unfold familyPairing
  obtain ⟨x0, h⟩ := hE
  refine ⟨x0, fun x hx0 hx i => ?_⟩
  obtain ⟨h6, hT, hp0, hpT⟩ := h x hx0 hx i
  exact pairing_integrality_both_sides _ _ (chain_norm_of_sixth h6) hT hp0 hpT

theorem family_periodBound_at_level {eps : ℝ} (Fm : FamP eps) (hS : ServF Fm)
    (hE : ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (hx : Fm.x1 < x) (i : Fm.Ix x),
      ((∀ u, Formalism.MainNotions.product_first_zeroth_parts.Conclusion5Sharp (Fm.D x i) u) ∧ (∀ u, Formalism.MainNotions.product_first_zeroth_parts.TupleChainSharpColumnValuation (Fm.X x i) (Fm.ex x hx i).tw u) ∧
        (∀ u, Formalism.MainNotions.product_first_zeroth_parts.Conclusion6 (Fm.D x i) u)) ∧
      (TwistedChainIntegral (Fm.D x i) (Fm.ex x hx i).tw ∧ PeriodClassSumWeyl (Fm.D x i) ∧
        TwistedPeriodIntegral (Fm.D x i) (Fm.X x i) (Fm.ex x hx i).tw) ∧
      LevelPrimeCoprimeStabiliser (Fm.D x i) ∧ ServedHasModel (Fm.Gx x i) Fm.GK) {C1 C2 : ℝ} (hCL : FamilyPeriodFormCond Fm C1 C2) (hSg : familySizeBoundAtTypePrime Fm C1)
    (hlin : ∀ x (i : Fm.Ix x), PerColSmul (Fm.D x i)) : familyL2Bound Fm ∧ familyFourthComplement Fm := by
  obtain ⟨x0, hE⟩ := hE
  refine l2_and_fourth_complement_family Fm (family_pairing_integrality Fm ⟨x0, fun x hx hx1 i => ?_⟩) hS
    (family_level_column_bound Fm ⟨x0, fun x hx hx1 i => ?_⟩) hCL hSg hlin
  · obtain ⟨⟨_, _, a⟩, ⟨b, c, d⟩, _, _⟩ := hE x hx hx1 i
    exact ⟨a, b, c, d⟩
  · obtain ⟨⟨a, b, _⟩, _, c, d⟩ := hE x hx hx1 i
    exact ⟨a, b, c, d⟩

theorem theta_term_of_integrality (D : D7) (large₂ : SizeData₂ D) (Cn C cL : ℝ) (T : Formalism.MainNotions.TaylorLogMetric.Tor D) (e : Formalism.MainNotions.TaylorLogMetric.FamE D)
    (hth : Formalism.MainNotions.TaylorLogMetric.th22 D T C e) (hfree : Formalism.MainNotions.GlobalTheoryTheory.ThFree D) (hl : Formalism.MainNotions.GlobalTheoryTheory.ThLinkLe D T e)
    (hN : NumsL D large₂ Cn cL) : Formalism.MainNotions.placeRankTwoOne.GenusOneThetaNorm D large₂ (C * (1 + Cn) * cL) :=
  genusOne_theta_norm_bound D large₂ Cn (C * (1 + Cn)) cL (flipTwoThree.second_hypothesis_of_lifting D Cn C large₂.sc.x T e hth hfree hl) hN

theorem family_theta_term_of_integrality {eps : ℝ} (Fm : FamP eps) (C : ℝ) (hT : TuSize Fm) (hDl : DlSize Fm)
    (hfree : ∀ x (i : Fm.Ix x), Formalism.MainNotions.GlobalTheoryTheory.ThFree (Fm.D x i))
    (h22 : ∀ x (i : Fm.Ix x), Formalism.MainNotions.GlobalTheoryTheory.ExistsTwelfthRootCharacterThetaFamily (Fm.D x i) C) : Formalism.MainNotions.placeRankTwoOne.ThetaNormFamily Fm := by
  unfold Formalism.MainNotions.placeRankTwoOne.ThetaNormFamily
  obtain ⟨Cn₀, hN⟩ := numsL_wtsL_fam Fm hT hDl
  obtain ⟨x0, hx0⟩ := hN Cn₀ le_rfl 3 le_rfl
  refine ⟨C * (1 + Cn₀) * 3, x0, fun x hx i => ?_⟩
  obtain ⟨δ, -, χ, -, e, hcl, hl⟩ := h22 x i
  exact theta_term_of_integrality (Fm.D x i) (Fm.L x i) Cn₀ C 3 _ e (by unfold GlobalTheoryTheory.Cl22 at hcl; exact hcl.2.1) (hfree x i) hl (hx0 x hx i).1

end Formalism.MainNotions.J

end
