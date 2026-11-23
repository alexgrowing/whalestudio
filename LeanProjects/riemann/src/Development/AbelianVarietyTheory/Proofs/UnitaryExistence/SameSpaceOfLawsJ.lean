import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.HasDataCondition
import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
import Formalism.LocalToGlobal.ProjectiveLattices.RecCond
import Formalism.LocalToGlobal.ProjectiveLattices.ParCanon
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModuliSchemeLevelMapsHeckePoints
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.BetaExistsOfNeOne
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ShortValTotOfPinned
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedModuliAlgebraicLawsChartWeightIntegrality
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsCharacter
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UnitCOfFiniteCharacter
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ShortThetaSeriesDominantWeightIsCuspFormStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CuspFormsLeSpanShortThetaSeriesStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CoreArithmeticGroupContainsPrincipalCongruenceStatement
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.NumericalConsequencesOfPins

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Theta

namespace GlobalTheory.ShortLaws

theorem sameSpace_of_lawsJ {D : D7} (J : CoreJ D) (T : Top D) (hJ : LawsJ J) (hT : T.toCore = J.toCore) :
    ∀ j, InR D j → ∀ k k', ((T.U j T.σ₀).X k).Gm = ((T.U j T.σ₀).X k').Gm ∧
      ((T.U j T.σ₀).X k).ξ0 = ((T.U j T.σ₀).X k').ξ0 := by
  have key : ∀ C : Core D, C = J.toCore → ∀ j, InR D j → ∀ k k', ((C.U j C.σ₀).X k).Gm = ((C.U j C.σ₀).X k').Gm ∧
      ((C.U j C.σ₀).X k).ξ0 = ((C.U j C.σ₀).X k').ξ0 := by
    rintro C rfl j hj k k'
    obtain ⟨hr, hm⟩ := hJ.modelW j hj J.toCore.σ₀ J.toCore.good_σ₀
    exact ⟨(hm k).1.trans (hm k').1.symm, (hm k).2.trans (hm k').2.symm⟩
  exact key _ hT

theorem lawsSh_of_pinned (hC : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2) {D : D7} (T : Top D) (h : LawsP T) (hb : 0 < badN D)
    (hsp : ∀ j, InR D j → ∀ k k', ((T.U j T.σ₀).X k).Gm = ((T.U j T.σ₀).X k').Gm ∧
      ((T.U j T.σ₀).X k).ξ0 = ((T.U j T.σ₀).X k').ξ0)
    (p : ℕ) (hp : p = D.host.pde ∨ p = D.host.pde')
    (hd : ∀ j, InR D j → ∀ n, (T.dδ j n).pd = p ∧ (T.dδ j n).IsLev ∧ (T.dδ j n).l₂.A = 1 ∧
      (∃ _ : StarRing (𝓞 D.host.E), IsNab (T.dδ j n).Xo₂ (T.dδ j n).c₂ (T.dδ j n).nab₂) ∧
      (∃ m : ℕ, 0 < m ∧ (T.dδ j n).cδ ^ m = 1) ∧
      (∀ y : FrPt (T.dδ j n).Xo₂ (T.dδ j n).c₂ (CAt (T.dδ j n).c₂.F.val.toRingHom), ∃ a : (T.dδ j n).c₂.F,
        evR (T.dδ j n).Xo₂ (T.dδ j n).c₂ (T.dδ j n).cδ y =
          algebraMap (T.dδ j n).c₂.F (CAt (T.dδ j n).c₂.F.val.toRingHom) a) ∧
      ((T.Q.Dw j).p + (T.Q.Dw j).q ≤ n → ∃ ph ψ x₀, ψ ≠ 1 ∧ (T.dδ j n).PhiPin ph ψ x₀ ∧ (T.dδ j n).PsiTie ψ)) :
    LawsSh T := by
  have hM : LawsM T.toCore := h.toLawsCore.toLawsM
  obtain ⟨-, hA, -, -, -, -, hnum⟩ := GlobalTheory.PinNum.numerics_of_pins D T.Q hM.pins
  have hL : ReciprocityTheory.ChartRestriction.G.Out.Laws := GlobalTheory.firstFiveLaws.1
  have hr : ∀ j, InR D j → (T.Q.Dw j).p + (T.Q.Dw j).q = D.R.r := fun j hj => (hnum j hj).1
  have hr1 : ∀ j, InR D j → 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := fun j hj => (hr j hj).symm ▸ (hnum j hj).2.1
  have hb1 : badN D ≠ 1 := by
    have h2 : 2 ∣ badN D := by
      unfold badN
      exact ((D.host.two_dvd_QS.mul_right _).mul_right _).mul_right _
    omega
  have hroot : ∀ j, InR D j → ∀ n, ∃ (Cls : Type) (_ : CommGroup Cls) (_ : Finite Cls)
      (δ : Cls →* (T.dδ j n).c₂.Fˣ)
      (gdet : FrPt (T.dδ j n).Xo₂ (T.dδ j n).c₂ (CAt (T.dδ j n).c₂.F.val.toRingHom) → Cls),
      CMP (T.Q.Xo j) T.Q.c (T.dδ j n) _ Cls δ gdet false := by
    intro j hj n
    obtain ⟨-, hlev, -, -, ⟨m, hm, hm1⟩, hval, -⟩ := hd j hj n
    exact GlobalTheory.RootOfUnityFn.exists_character _ _ _ _ _ _ n (T.dδ j n) m hm hlev.2.2.2.2.2.2.2.1 hm1 hval
  have htot : ∀ j, InR D j → ∀ a n,
      ShortValTot (T.Q.Xo j) T.Q.c (T.nab j) (badN D) D.R.nV a n (T.dδ j n) := by
    intro j hj a n
    obtain ⟨-, hlev, hA2, hnab, -, -, hphi⟩ := hd j hj n
    refine GlobalTheory.shortValTot_of_pinned hL hC _ _ _ _ _ _ n (T.dδ j n)
      (GlobalTheory.moduliScheme_levelMaps_heckePoints.2 _ _ _ (hr1 j hj)).1 (hM.evalWD j hj) (h.allTest j hj)
      (GlobalTheory.Frames.algebraic_laws hL.secBaseChange _ _ _ _ _ _).2.2.1
      (GlobalTheory.Frames.allTest_of_secBaseChange hL.secBaseChange _ _ _ _ _ _) hlev (hA2.trans hA.symm) hnab ?_ _ _ _ a
    intro hn
    obtain ⟨ph, ψ, x₀, -, h1, h2⟩ := hphi hn
    exact ⟨ph, ψ, x₀, h1, h2⟩
  have hpin : ∀ j, InR D j → ∀ n, (T.Q.Dw j).p + (T.Q.Dw j).q ≤ n → ∃ ph ψ x₀, (T.dδ j n).PhiPin ph ψ x₀ := by
    intro j hj n hn
    obtain ⟨ph, ψ, x₀, -, h1, -⟩ := (hd j hj n).2.2.2.2.2.2 hn
    exact ⟨ph, ψ, x₀, h1⟩
  have hunit : ∀ j, InR D j → ∀ n, GlobalTheory.Dict.UnitC (T.dδ j n) := by
    intro j hj n
    obtain ⟨Cls, _, _, δ, gdet, hc⟩ := hroot j hj n
    exact GlobalTheory.Dict.unitC_of_finite_character _ _ _ _ _ _ _ _ Cls δ gdet (hr1 j hj) hc
  refine
    { beta := fun j _ n => GlobalTheory.betaExists_of_ne_one _ _ _ _ _ n _ hb1
      dLev := fun j hj n => (hd j hj n).2.1
      dNab := fun j hj n => (hd j hj n).2.2.2.1
      dPd := ⟨p, hp, fun j hj n => (hd j hj n).1⟩
      dPhi := fun j hj n hn => (hd j hj n).2.2.2.2.2.2 ((hr j hj).symm ▸ hn)
      dRoot := hroot
      shTot := fun j hj a n _ => htot j hj a n
      shCusp := fun j hj a n _ _ => GlobalTheory.T.short_thetaSeries_dominant_weight_isCuspForm hC D.host.E T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c n (T.dδ j n)
        D.R.r (fun σ => Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) (hnum j hj).2.1 (fun σ hσ => hM.unf j hj σ hσ)
        (hd j hj n).2.1 (hd j hj n).2.2.2.1 (hunit j hj n) (hpin j hj n) (T.nab j) (badN D) D.R.nV a
      shNe := ?_ }
  intro j h1 h2
  have hj : InR D j := ⟨h1, h2.le⟩
  refine shortNe0_of_t4Span _ _ _ _ _ _ _ ?_
  refine GlobalTheory.T.cuspForms_le_span_shortThetaSeries hC D.host.E T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c D.R.r
    (fun σ => Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) T.σ₀ T.good_σ₀ (hM.unf j hj _ T.good_σ₀) (hnum j hj).2.1 hA
    (hsp j hj) ?_ (fun a n hdom k => hM.chiTriv j hj _ T.good_σ₀ a n hdom k) (T.nab j) (badN D) D.R.nV (T.dδ j) hb ?_
  · intro k ga hga hv
    refine GlobalTheory.T.coreArithmeticGroup_contains_principalCongruence D T.toCore h.toLawsCore j hj _ T.good_σ₀ k ga hga fun x hx => ?_
    obtain ⟨u, hu, he⟩ := hv x hx
    refine ⟨u, hu, ?_⟩
    rw [he, Nat.cast_smul_eq_nsmul]
    exact add_sub_cancel_left _ _
  · intro n
    refine ⟨(hd j hj n).2.1, (hd j hj n).2.2.2.1, hunit j hj n, ?_, hpin j hj n, fun a _ => htot j hj a n⟩
    rw [(hd j hj n).1]
    have := D.host.pde_mod
    rcases hp with rfl | rfl <;> omega

end GlobalTheory.ShortLaws
