import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.LevelFrameOfLaws
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.WeightedChartPullback.WeightIndep
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.PGAppEqZeroIff
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpandsAtSub
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpansionOfIntegralSectionIsIntegralStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IntegralFamilyLevelOne

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThetaNu

theorem dvd_of_vGe {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V} (hϖ : Irreducible ϖ)
    (D : DegData V (maximalIdeal V)) (F : Type) [Field F] [Algebra (FractionRing V) F]
    (v : AddValuation F (WithTop ℚ)) (hv : ValOver ϖ F v) (k : ℕ) (χ : D.toPre.X)
    (s : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F χ) (DegPre.famε k))) (g : D.toPre.SecB k χ)
    (hg : GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre F χ) (DegPre.famε k) s (D.toPre.famφB χ) (DegPre.famε k) g
      (DegPre.prB D.toPre F).left 1) {r : ℚ} (hr : 0 < r) (h : VGe D F v k χ s r) :
    ∃ g' : D.toPre.SecB k χ, SecIsMul D.toPre.P.A.hom ϖ g g' := by
  obtain ⟨n, a₀, τ, τF, hτ, hva, hsum⟩ := h
  have hb : ∀ i, 0 < v (a₀ i) := fun i => by
    refine lt_of_lt_of_le ?_ (hva i)
    exact_mod_cast hr
  have vc : ∀ (t : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F χ) (DegPre.famε k))) (x : F)
      {Z : Scheme.{0}} (q : Z ⟶ (DegPre.BF D.toPre F).left) (z : Z) (j),
      q z ∈ LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F χ) j →
      gs q z (LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F χ) j) (DegPre.constBF D.toPre F x _ * t.f j) =
        cst (q ≫ (fst (TF (R := V) F) D.toPre.P.A).left) z x *
          gs q z (LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F χ) j) (t.f j) := fun t x Z q z j hz =>
    (gs_mul q z _ hz _ _).trans (congrArg₂ (· * ·) ((gs_res q z le_top hz _).trans
      (gs_pull q (fst (TF (R := V) F) D.toPre.P.A).left z ⊤ trivial _)) rfl)
  have div₁ := H1.dvd_of_comb hϖ D.toPre F v hv g τ a₀ hb (fun Z q z J hJ =>
    (H1.sval_scal hg q z hJ).symm.trans
      ((congrArg (gs _ z _) (hsum _)).trans ((H1.gs_sum q z _ (hJ.mem _ q) _).trans (Finset.sum_congr rfl fun i _ =>
        (vc (τF i) (a₀ i) q z _ (hJ.mem _ q)).trans (congrArg₂ (· * ·) rfl (H1.sval_scal (hτ i) q z hJ))))))
  have := D.toPre.P.isAb.smooth
  exact exists_div_sec D.toPre.P.A.hom hϖ.ne_zero g div₁

theorem isUnit_of_generates {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {I : Ideal R} {D : DegData R I}
    {k : ℕ} {α : D.toPre.X} {s t : D.toPre.SecB k α} (hs : SecBGenerates k α s) {a : R}
    (h : SecIsMul D.toPre.P.A.hom a s t) : IsUnit a := by
  obtain ⟨b, hb, -⟩ := hs t
  have h₁ : SecIsMul D.toPre.P.A.hom 1 s s := fun j => by simp only [scal, resTop, map_one, _root_.one_mul]
  have h₂ : SecIsMul D.toPre.P.A.hom (a * b) s s := fun j => by
    conv_lhs => rw [h j, hb j]
    simp only [scal, resTop, map_mul, _root_.mul_assoc]
  exact IsUnit.of_mul_eq_one b ((hs s).unique h₂ h₁)

theorem main : Laws → ThetaSectionValuationZero := by
  intro _ V _ _ _ ϖ hϖ D Q hQ vK hv A G _ _ U ϑ hϑ s hs E hE
  obtain ⟨g, hgE, hg⟩ := GlobalTheory.T.expansion_of_integral_section_is_integral V ϖ hϖ D A G U.toUnifPre 1 ϑ s hs E hE
  refine ⟨(GlobalTheory.integralFamily_levelOne V ϖ hϖ D Q hQ _ vK hv E g hg).1, ?_⟩
  rintro ⟨r, hr, hν⟩
  have h0 := hν 0
  rw [QForm.Q_zero hϖ D hQ, Int.cast_zero, zero_div, add_zero] at h0
  obtain ⟨g', hg'⟩ := dvd_of_vGe hϖ D _ vK hv 1 0 (E.s 0) (g 0) (hg 0) hr h0
  obtain ⟨f, hfE, hf⟩ := hϑ 0
  have hd := GlobalTheory.expandsAt_sub V _ D A G U.toUnifPre 0 1 ϑ ϑ SecOps.secZero f g
    (fun α => SecOps.secAdd (f α) (SecOps.secNeg (g α))) (fun j => (sub_self _).symm)
    (fun α j => (sub_eq_add_neg _ _).symm) hfE (hgE 0)
  obtain ⟨h, hh⟩ := (GlobalTheory.ExtDiv.main V ϖ hϖ D A G U.toUnifPre 0 1 0 _).1
    (WeightPf.weightIndep V _ D A G U.toUnifPre 0 1 _ _ (fun j => map_zero _) hd 0)
  rw [zero_add, pow_one] at hh
  refine hϖ.not_isUnit (isUnit_of_generates (t := SecOps.secAdd h g') hf fun j => ?_)
  have e₁ : (f 0).f j + - (g 0).f j = _ := hh j
  have e₂ := hg' j
  show _ = _ * (h.f j + g'.f j)
  rw [mul_add, ← e₁, ← e₂, neg_add_cancel_right]

end GlobalTheory.ThetaNu
