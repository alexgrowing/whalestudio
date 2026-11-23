import Mathlib
import Development.AbelianVarietyTheory.Definitions.TorusSections.ExistsSecTie
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import Formalism.LocalToGlobal.ProjectiveLattices.DataAtPointN3
import Formalism.LocalToGlobal.ProjectiveLattices.LiesOverBaseChange
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ETPoint
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformizationLawsAndExpansionStatements
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.FrMapComp
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CardLevGrpAndSpan
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaNullValueExistsUniqueNaturalLinear
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FullLinearLevelCoverBaseChangeTorsor
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.EtaValAtExistsUniqueNatural
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFramedPointBaseChangeAlgHom
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorsionIsoOfLinearUniformisationTriple
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.LeValuationOddLevelThetaConstantIntegralExpansioStatement
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.ExistsExpansionNonnegStatement
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.ExistsAbelianSectionOfUniversalFibreSectionStatement
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.FibPointsMulEquivStatement
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.NormalisedThetaConstantOfUniversalOriginValueStatement
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.ExistsFibIntThStatement
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.ExistsHeisenbergLiftsSpanLatticeClassesStatement
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.SumCosetMinGePhiCDivSqStatement
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.ExistsValuationClosureStatement
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.CardMulLeAddValEtaExprStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR Formalism.L2.Pj GlobalTheory.EtaForm GlobalTheory.EtaVal
open Formalism.MainNotions.DIV.Cons (SCF intO)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EtaVal

theorem mul_le_of_forall_rat_le (N : ℕ) (hN : 0 < N) (x : ℝ) (a : ℤ)
    (h : ∀ q : ℚ, (q : ℝ) ≤ x → (N : ℚ) * q ≤ (a : ℚ)) : (N : ℝ) * x ≤ (a : ℝ) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  by_contra hc
  have h1 : (a : ℝ) / N < x := by
    rw [div_lt_iff₀ hN', mul_comm]; exact not_le.mp hc
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn h1
  have h2 : (N : ℝ) * (q : ℝ) ≤ (a : ℝ) := by exact_mod_cast h q hq2.le
  rw [div_lt_iff₀ hN', mul_comm] at hq1
  linarith

set_option maxHeartbeats 1000000 in

theorem card_mul_phiC_le_valuation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V] [IsAdicComplete (maximalIdeal V) V] [Algebra c.F (FractionRing V)] (y : FrPt Xo c (FractionRing V)) (G : SAB H (Sp V)) (_ : IntSec Xo V y.x y.s G) (P : PELUnif (maximalIdeal V) G) (ϖ : V), Irreducible ϖ → ∀ (Q : P.D.toPre.X → ℤ), QForm.IsQ P.D.toPre ϖ Q → (∀ a, 0 ≤ Q a) → ∀ (cj : E → E), (∀ a, cj a = IsCMField.complexConj E a) → ∀ (β : Formalism.MainNotions.ModuliIntegralCharts.SymB cj P.D.toPre.X), (∀ a, (β : _ →ₗ[ℤ] _ →ₗ[ℤ] ℝ) a a = 2 * (Q a : ℝ)) → ∀ (R : ℕ), Odd R → 1 < R → ∀ (J : Type) [Fintype J] (n : ℕ) (cf : J → ℤ) (xs : J → Fin n → LatMod Dw (R ^ 4)) (val : FractionRing V), GlobalTheory.EtaAn.Spans xs → EtaValAt Xo c R cf xs y val → val ≠ 0 → (Nat.card (LevGrp Dw (R ^ 4)) : ℝ) / (R : ℝ) ^ 4 * Formalism.MainNotions.ModuliIntegralCharts.phiC cj β ≤ (vV V val : ℝ) := by
  intro E _ _ _ H Dw l Xo c V _ _ _ _ hcpl _ y G S P ϖ hϖ Q hQ hQ0 cj hcj β hβ R hR hR1 J _ n cf xs val hsp hval hne
  obtain ⟨hLL, h2, h3, h4, h5⟩ := GlobalTheory.lawsAndExpansions
  have hL : Laws := hLL.1
  have hA : AdmBase V (maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hcpl⟩
  have htors := GlobalTheory.UT.torsionIso_of_pelUnif hLL h2 h3 h4 h5 E H V _ hA G P
  haveI hfin : Finite (LevGrp Dw (R ^ 4)) := (GlobalTheory.EtaCard.card_levGrp_and_span E H Dw R hR1).1
  obtain ⟨v, hv, hvv⟩ := GlobalTheory.T.exists_valuation_algebraicClosure_extending_vV V ϖ hϖ
  let F := AlgebraicClosure (FractionRing V)
  letI : Algebra c.F F := ((algebraMap (FractionRing V) F).comp (algebraMap c.F (FractionRing V))).toAlgebra
  let ψ : FractionRing V →ₐ[c.F] F := { algebraMap (FractionRing V) F with commutes' := fun _ => rfl }
  have hψ : ψ.toRingHom = algebraMap (FractionRing V) F := rfl
  obtain ⟨z, hz⟩ := GlobalTheory.FramedBaseChange.exists_frMap hL E H Dw l Xo c _ F ψ y
  have hzx : z.x = spMap (algebraMap (FractionRing V) F) ≫ y.x := hz.1
  have hR0 : 0 < R := by omega
  have e4 : (R ^ 2) ^ 2 = R ^ 4 := by rw [← pow_mul]
  have hR2 : Odd (R ^ 2) := hR.pow
  obtain ⟨-, hbc, hloc, hex⟩ := GlobalTheory.fullLevel_cover_baseChange_torsor hL E H Dw l Xo (R ^ 4) (pow_pos hR0 4)
  obtain ⟨ev, hev⟩ := hex F z.x
  have hevt : ∀ q, ev q ^ ((R ^ 2) ^ 2) = 1 := by
    rw [e4]
    exact (hbc F F (RingHom.id F) z.x z.x (𝟙 _) (by simp [spMap]) ev hev).2
  have hevs : ∀ p : ptO Xo z.x ⟶ Xo.univ.t.G, p ^ ((R ^ 2) ^ 2) = 1 → ∃ q, ev q = p := by
    rw [e4]
    exact (hloc F z.x ev hev).1
  have hw := fun q => ((GlobalTheory.nullValue_existsUnique_natural_linear hL E H Dw l Xo c (R ^ 2) hR2).1 F z (ev q) (hevt q)).exists
  choose w hw using hw
  have hz' : EtaValAt Xo c R cf xs z (etaExpr (R ^ 4) cf xs w) :=
    ⟨F, inferInstance, inferInstance, AlgHom.id _ _, z, ev, w,
      RingHom.FaithfullyFlat.of_bijective Function.bijective_id, PullbackSections.frMap_refl z, hev, hw, rfl⟩
  have hvalF : algebraMap (FractionRing V) F val = etaExpr (R ^ 4) cf xs w :=
    (GlobalTheory.EtaForm.etaValAt_existsUnique_natural hL E H Dw l Xo c R hR J n cf xs).2 _ F ψ y z hz _ _ hval hz'
  obtain ⟨Φ, w₀, hN, hact, hint⟩ := GlobalTheory.T.exists_fib_normW_of_intSec E H Dw l Xo c V y G S P
  obtain ⟨th, hth⟩ := GlobalTheory.T.exists_abelianSection_of_universalFibreSection E H Dw l Xo V y.x P.A Φ F z.x hzx z.s
  obtain ⟨ϑ, hϑ, hν⟩ := GlobalTheory.T.exists_expandsF_nuGe_zero_of_intTh V hcpl ϖ hϖ P.D Q hQ F v hv P.A G.G G.semi P.U w₀ hN.1 th
    (hint F ψ z th hψ hz hth)
  obtain ⟨tr, htr, htra⟩ := GlobalTheory.T.exists_mulEquiv_ptO_hom_of_eq_spMap_comp E H Dw l Xo V y.x P.A Φ F z.x hzx
  obtain ⟨pt, hpt, hspan⟩ := GlobalTheory.T.exists_heisenbergLifts_span_latticeClasses E H V G P htors F ((R ^ 2) ^ 2) (pow_pos (pow_pos hR0 2) 2)
    (LatMod Dw (R ^ 4)) (fun a => tr (ev a)) (fun a b => by rw [hev.1, map_mul])
    (fun o a => by rw [hev.2.1]; exact htra _ _ (hact o) _)
    (fun a => by rw [← map_pow, hevt, map_one])
    (fun u hu => by
      obtain ⟨a, ha⟩ := hevs (tr.symm u) (by rw [← map_pow, hu, map_one])
      exact ⟨a, by rw [ha, MulEquiv.apply_symm_apply]⟩)
  have hb : ∀ a (q : ℚ), (∀ χ, q ≤ (Q ((R ^ 2) • χ + (pt a).y) : ℚ) / ((R ^ 2) ^ 2 : ℕ)) →
      (q : WithTop ℚ) ≤ v (w a) := by
    intro a q hq
    obtain ⟨t, ht⟩ := GlobalTheory.T.normalisedThetaConstant_of_universal_origin_value E H Dw l Xo c V y.x P.A Φ F z hzx th hth (R ^ 2) hR2 (ev a) (tr (ev a)) (w a)
      (hevt a) (htr _) (hw a)
    exact GlobalTheory.T.le_valuation_oddLevel_thetaConstant_integralExpansion V hcpl ϖ hϖ P.D Q hQ F v hv P.A G.G G.semi P.U w₀ Φ.ρ hN th ϑ hϑ hν (R ^ 2) hR2 (pt a)
      (tr (ev a)) t (w a) (hpt a) ht q hq
  haveI : Module.Finite ℤ P.D.toPre.X := P.D.toPre.finX
  have hcj1 : ∀ a : 𝓞 E, ∃ a' : 𝓞 E, (a' : E) = cj a := fun a => ⟨H.bar a, by rw [H.bar_eq, hcj]⟩
  have hcj2 : (H.w0 : E) + cj H.w0 = 1 := by
    rw [hcj, ← H.bar_eq, GlobalTheory.HostModel.cmHost_bar_halfIntegerGenerator]; simp
  have key : ∀ q : ℚ, (q : ℝ) ≤ Formalism.MainNotions.ModuliIntegralCharts.phiC cj β / (R : ℝ) ^ 4 →
      (Nat.card (LevGrp Dw (R ^ 4)) : ℚ) * q ≤ ((vV V val : ℤ) : ℚ) := by
    intro q hq
    have h := GlobalTheory.T.card_mul_le_val_etaExpr_of_le_sum_val E H Dw (R ^ 4) J n cf xs F v w q (fun g j => by
      refine GlobalTheory.T.le_sum_of_le_phiC_div_sq E cj hcj1 H.w0 hcj2 P.D.toPre.X Q β hβ hQ0 (R ^ 2) (by nlinarith) n
        (fun b => (pt (g (xs j b))).y) (hspan n (fun b => g (xs j b)) ?_) (fun b => v (w (g (xs j b))))
        (fun b => hb _) q ?_
      · have := congrArg (Submodule.map (g : LatMod Dw (R ^ 4) →ₗ[𝓞 E] LatMod Dw (R ^ 4))) (hsp j)
        rw [Submodule.map_span, ← Set.range_comp, Submodule.map_top, LinearEquiv.range] at this
        exact this
      · rw [Nat.cast_pow, ← pow_mul]; exact hq)
    rw [← hvalF, hvv val hne] at h
    exact_mod_cast h
  have := mul_le_of_forall_rat_le _ Nat.card_pos _ _ key
  rw [div_mul_eq_mul_div, mul_div_assoc]
  exact this

end GlobalTheory.EtaVal
