import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TanRel
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionPairingValuesOfFamiliesValues
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DegenerationValuesIntOfAdmissibleBaseStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisationGenericFibreCartesianToModelBundleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyRuleComplexExistenceJetsKeyValueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdaptedLieBasisTorusExtensionModelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanExistenceOfComplexIsomorphicFieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeyRuleLieBasisChangeUnitFactorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKeyDatumBaseChangeThetaJetsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianKeyValueNormOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTranslateTermsJetsBoundedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationValuesNormsEqUniformizerZpowStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentVectorSectionValueEqExpansionSumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricThetaTranslatesExpandSeriesFamiliesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralFormParameterOfDiscreteNormsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticLevelAlgClosedCharZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionSymplecticLabelsOfLevelStructureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeyRuleScaleSectionPowEightStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianKeyValueAdaptedVectorsFieldIsoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationValuesTransportFieldIsoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationDataValuesIsoTransportFormsLevelsFamStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueGenericFibreDualNumberPointOfModelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyRuleConstantAlongDeformationOfClausesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericThetaExpansionScalarNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelStructureBaseChangeLabelsTorsionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtDualNumberTermValueSmulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionValueEqAtFirstOrderOfTangentsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerSeriesDeformationOfBoundedLatticeSeriesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.MBLow.KapFPf

theorem norm_toF_unit {V : Type} [CommRing V] [IsDomain V] {I : Ideal V} {C : Type} [NormedField C]
    [Algebra (FractionRing V) C] (hC : CExt V I C) (u : Vˣ) : ‖toF V C u‖ = 1 := by
  have h1 : ‖toF V C u‖ ≤ 1 := hC.1 u
  have h2 : ‖toF V C ↑u⁻¹‖ ≤ 1 := hC.1 ↑u⁻¹
  have h3 : toF V C u * toF V C ↑u⁻¹ = 1 := by rw [← map_mul, Units.mul_inv, map_one]
  have h4 : ‖toF V C u‖ * ‖toF V C ↑u⁻¹‖ = 1 := by rw [← norm_mul, h3, norm_one]
  nlinarith [norm_nonneg (toF V C u), norm_nonneg (toF V C ↑u⁻¹)]

theorem c_ne_zero : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V],
    IsAdicComplete (IsLocalRing.maximalIdeal V) V → ∀ (D : DegData V (IsLocalRing.maximalIdeal V))
    (x : KeyIn (FractionRing V)) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G →
    ∀ (U : Unif (IsLocalRing.maximalIdeal V) D x.P G) (w₀ : GlobalTheory.UT.W0 U.toUnifPre), GlobalTheory.UT.NormW U.toUnifPre w₀ x.rig →
    ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C]
      [Algebra (FractionRing V) C], CExt V (IsLocalRing.maximalIdeal V) C →
    ∀ (N : NumD C) (ν : NumOf D.toPre C N) (th : GlobalTheory.UT.SecA x.P C 1) (ϑ : Fam D.toPre C 1) (c : C),
      IsPolAVSectionInverseImage x.P (TFK (R := V) C) x.th th → U.ExpandsF C 1 w₀ th ϑ → ν.FamV ϑ (c • N.vth) → c ≠ 0 := GlobalTheory.T.genericThetaExpansion_scalar_ne_zero

theorem level_labels : ∀ (K C : Type) [Field K] [Field C] [IsAlgClosed C] (f : K →+* C) (P : PolAV (Sp K))
    (P' : PolAV (Sp C)) (io : (Over.mk (spMap f) ⟶ P.A) ≃* (baseOver (Sp C) ⟶ P'.A)),
    (∀ (k : ℕ) a b (z : Γ(Sp C, ⊤)ˣ), WeilIs P'.A P'.L k (io a) (io b) z → WeilIs P.A P.L k a b z) →
    ∀ (g k : ℕ) (hg : P'.g = g) (ζ : Cˣ) (lev : Out.Level P' k (unitOn ζ)), 2 ≤ k →
      IsPrimitiveRoot ζ k ∧
      (∀ a b, io.symm (levelPoint lev hg (a + b)) = io.symm (levelPoint lev hg a) * io.symm (levelPoint lev hg b)) ∧
      Function.Injective (fun a => io.symm (levelPoint lev hg a)) ∧
      (∀ z : Over.mk (spMap f) ⟶ P.A, z ^ k = 1 → ∃ a, io.symm (levelPoint lev hg a) = z) ∧
      ∀ i j, WeilIs P.A P.L k (io.symm (levelPoint lev hg (Pi.single i 1))) (io.symm (levelPoint lev hg (Pi.single j 1)))
        (unitOn (ζ ^ stdSymp g i j)) := GlobalTheory.T.levelStructure_baseChange_labels_torsion

theorem jc_smul : ∀ {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
    {N : NumD F} (ν : NumOf D F N) {k : ℕ} (s : Fam D F k) (a : F) (gm : GtPt D (TE R F)) (α : N.X),
    jc ν (a • s) gm α = TrivSqZeroExt.inl a * jc ν s gm α := GlobalTheory.T.torusExtDualNumberTermValue_smul

theorem fst_indep : ∀ (K C : Type) [Field K] [Field C] [Algebra K C] (P : PolAV (Sp K))
    (ρ : LB.Gen (P.L.pull (eSec P.A))) (k : ℕ) (t : LB.Sec (LPow P.A P.L (k : ℤ) (Over.mk (spMap (algebraMap K C)))))
    (i₀ : P.L.ι), ⊤ ≤ (spMap (algebraMap K C) ≫ eSec P.A) ⁻¹ᵁ P.L.U i₀ →
    ∀ (v w : epsR K ⟶ P.A), IsTangent v → IsTangent w →
    ∀ (yv yw : Sp (DualNumber C) ⟶ (Over.mk (spMap (algebraMap K C)) ⊗ P.A).left),
      yv ≫ (fst (Over.mk (spMap (algebraMap K C))) P.A).left = spMap (algebraMap C (DualNumber C)) →
      yv ≫ (snd (Over.mk (spMap (algebraMap K C))) P.A).left = spMap (dualMap (algebraMap K C)) ≫ v.left →
      yw ≫ (fst (Over.mk (spMap (algebraMap K C))) P.A).left = spMap (algebraMap C (DualNumber C)) →
      yw ≫ (snd (Over.mk (spMap (algebraMap K C))) P.A).left = spMap (dualMap (algebraMap K C)) ≫ w.left →
    ∀ (a b a' b' : C),
      valR yv ((LPow P.A P.L (k : ℤ) (Over.mk (spMap (algebraMap K C)))).U fun _ => i₀) (t.f fun _ => i₀) =
        TrivSqZeroExt.inl (valR (spMap (algebraMap K C)) ((P.L.pull (eSec P.A)).U fun _ => i₀) (ρ.s fun _ => i₀).val ^ k) *
          (TrivSqZeroExt.inl a + TrivSqZeroExt.inr b) →
      valR yw ((LPow P.A P.L (k : ℤ) (Over.mk (spMap (algebraMap K C)))).U fun _ => i₀) (t.f fun _ => i₀) =
        TrivSqZeroExt.inl (valR (spMap (algebraMap K C)) ((P.L.pull (eSec P.A)).U fun _ => i₀) (ρ.s fun _ => i₀).val ^ k) *
          (TrivSqZeroExt.inl a' + TrivSqZeroExt.inr b') → a = a' := GlobalTheory.T.section_value_eq_at_first_order_of_tangents

theorem deform_of_series : ∀ (κ : Rule) (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C]
    [CharZero C] (e : C →+* ℂ) (x : KeyIn C) (g : ℕ) (hg : x.P.g = g) (m : ℕ) (ζ : Cˣ)
    (lev : Out.Level x.P (m ^ 2) (unitOn ζ)) (k : C) (X : Type) (n : X → ℕ) (π : C) (B : ℝ)
    (a : (Fin (2 * g) → ZMod (m ^ 2)) → X → C) (b : (Fin (2 * g) → ZMod (m ^ 2)) → Fin g → X → C),
    π ≠ 0 → ‖π‖ < 1 → (∀ i, {α | n α = i}.Finite) → (∀ i α, ‖a i α‖ ≤ B * ‖π‖ ^ n α) →
    (∀ i j α, ‖b i j α‖ ≤ B * ‖π‖ ^ n α) →
    ThJet x hg m (levelPoint lev hg) (fun i => ∑' α, a i α) (fun i j => ∑' α, b i j α) →
    (∃ ε : ℝ, 0 < ε ∧ ∀ u : ℂ, u ≠ 0 → ‖u‖ < ε →
      ((∀ i, Summable fun α => ‖e (a i α) * u ^ n α‖) ∧ ∀ i j, Summable fun α => ‖e (b i j α) * u ^ n α‖) ∧
      ∃ (x₀ : KeyIn ℂ) (hg₀ : x₀.P.g = g) (lev₀ : Out.Level x₀.P (m ^ 2) (unitOn (Units.map e.toMonoidHom ζ))),
        ThJet x₀ hg₀ m (levelPoint lev₀ hg₀) (fun i => ∑' α, e (a i α) * u ^ n α)
          (fun i j => ∑' α, e (b i j α) * u ^ n α) ∧ (κ ℂ x₀ : ℂ) = e k) →
    Deform κ e x hg m ζ lev k := GlobalTheory.T.powerSeriesDeformation_of_boundedLatticeSeries

end GlobalTheory.MBLow.KapFPf

namespace GlobalTheory.MBLow.KapFPf

set_option maxHeartbeats 4000000 in

theorem kapF_of_rule4 : ∀ κ : Rule, Rule4 κ → KapF κ := by
  intro κ hR4
  obtain ⟨hHom, hFun, hTh1, hFamU⟩ := id hR4
  intro V _ _ _ _ hcomp hfin D x G _ _ hSA U w₀ hNW y hy hyv C _ _ _ _ _ _ hCE hiso N ν hInt th ϑ c hOn hExp hFV
  obtain ⟨e⟩ := hiso

  set K := FractionRing V

  obtain ⟨j₀, hj₀⟩ := GlobalTheory.T.transfer_of_rule4' κ hR4 x.P.g 3 Nat.prime_three ⟨1, rfl⟩
  set j := max j₀ 1 with hj
  set m := 3 ^ j with hm
  have hmOdd : Odd m := Odd.pow ⟨1, rfl⟩
  have hm1 : 1 ≤ m := Nat.one_le_pow _ _ (by norm_num)
  have hm2 : 2 ≤ m ^ 2 := by
    have : 3 ≤ m := by
      calc 3 = 3 ^ 1 := by norm_num
        _ ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
    nlinarith

  obtain ⟨vB, r, bX, σ, y', gm₀, gm, hy', hAd, hT⟩ := GlobalTheory.T.exists_adaptedLieBasis_torusExtensionModel V hcomp D x.P G hSA U C hCE N ν hInt
  have hvec := fun j => GlobalTheory.T.existsUnique_genericFibreDualNumberPoint_of_model V hcomp D x.P G hSA U C (y' j)
  choose yA hyA _ using fun j => (hvec j).1
  choose v' hv'o _ using fun j => (hvec j).2.1
  have hyAs : ∀ j, yA j ≫ (snd (TFK (R := V) C) x.P.A).left =
      spMap (dualMap (algebraMap (FractionRing V) C)) ≫ (v' j).left := fun j => (hvec j).2.2 (v' j) (yA j) (hv'o j) (hyA j)
  obtain ⟨-, -, -, hgp, -⟩ := GlobalTheory.T.uniformisation_generic_fibre_cartesian_to_model_bundleIso V _ D x.P G U.toUnifPre
  obtain ⟨hv', u, hu⟩ := GlobalTheory.T.thetaKeyRule_lieBasisChange_unit_factor κ hHom V (FractionRing V) (algebraMap V (FractionRing V)) x G _ hgp y y' v' hy hy' hyv hv'o
  set x' : KeyIn (FractionRing V) := ⟨x.P, x.g_pos, x.rig, x.rig_gen, x.th, x.th_ne, v', hv'⟩ with hx'

  obtain ⟨xC, hgC, io, hPB, hW, hJ⟩ := GlobalTheory.T.exists_keyDatumBaseChange_thetaJets (FractionRing V) C (algebraMap (FractionRing V) C) x'
  have hκC : (κ C xC : C) = algebraMap (FractionRing V) C (κ (FractionRing V) x') := hFun _ _ _ x' xC hPB
  obtain ⟨ζ, ⟨lev⟩⟩ := GlobalTheory.T.exists_symplecticLevel_algClosed_charZero C xC.P (m ^ 2) (by omega)
  obtain ⟨hprim, hadd, hinj, hsurj, hweil⟩ :=
    level_labels (FractionRing V) C (algebraMap (FractionRing V) C) x'.P xC.P io hW x.P.g (m ^ 2) hgC ζ lev hm2
  set pt : (Fin (2 * x.P.g) → ZMod (m ^ 2)) → (TFK (R := V) C ⟶ x.P.A) := fun a => io.symm (levelPoint lev hgC a) with hpt
  obtain ⟨p, Q, hQL, hpq⟩ := GlobalTheory.T.torsionSymplecticLabels_of_levelStructure V hcomp D x.P G hSA U C hCE N ν hInt x.P.g (m ^ 2) (by omega) ζ pt hprim
    hadd hinj hsurj hweil

  choose Θ tt ss ff hfam using fun a => GlobalTheory.T.symmetricThetaTranslates_expand_seriesFamilies V hcomp D x.P G hSA U C hCE N ν hInt w₀ x.rig hNW th ϑ c hExp hFV
    m hmOdd (p a) (Q a) (pt a) (hpq a).1 (hpq a).2
  have hc : c ≠ 0 := c_ne_zero V hcomp D x G hSA U w₀ hNW C hCE N ν th ϑ c hOn hExp hFV
  set s' : (Fin (2 * x.P.g) → ZMod (m ^ 2)) → Fam D.toPre C (m ^ 2) := fun a => c⁻¹ • ss a with hs'
  have hs'V : ∀ a, ν.FamV (s' a) (ff a) := fun a => by
    have := GlobalTheory.WeilValues.famV_smul ν (hfam a).2.2.2.2 c⁻¹
    rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this

  have hch : ∃ i₀, ⊤ ≤ (jFK (R := V) C ≫ eSec x.P.A) ⁻¹ᵁ x.P.L.U i₀ := by
    have h : (jFK (R := V) C ≫ eSec x.P.A) (default : PrimeSpectrum C) ∈ (⨆ i, x.P.L.U i) := by
      rw [x.P.isLB.cover]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 h
    refine ⟨i, fun z _ => ?_⟩
    obtain rfl : z = (default : PrimeSpectrum C) := Subsingleton.elim _ _
    exact hi
  obtain ⟨i₀, hi₀⟩ := hch
  choose cj hcj using fun j => GlobalTheory.T.tangentVector_section_value_eq_expansion_sum V hcomp D x.P G hSA U C hCE N ν hInt w₀ x.rig hNW (y' j) (gm₀ j) (gm j)
    (yA j) (hy'.1 j) (hT j).1 (hT j).2.2 (hyA j) (m ^ 2) i₀ hi₀
  set j₁ : Fin x.P.g := ⟨0, x.g_pos⟩
  set Sf : (Fin (2 * x.P.g) → ZMod (m ^ 2)) → Fin x.P.g → C :=
    fun a j => ∑' α, (jc ν (ss a) (gm j) α).fst / ν.rg ^ (m ^ 2) with hSf
  set Ss : (Fin (2 * x.P.g) → ZMod (m ^ 2)) → Fin x.P.g → C :=
    fun a j => ∑' α, (jc ν (ss a) (gm j) α).snd / ν.rg ^ (m ^ 2) with hSs
  have hind : ∀ a j, Sf a j = Sf a j₁ := fun a j =>
    fst_indep (FractionRing V) C x.P x.rig (m ^ 2) (tt a) i₀ hi₀ (v' j) (v' j₁) (hv'.1 j) (hv'.1 j₁) (yA j) (yA j₁)
      (hyA j).1 (hyAs j) (hyA j₁).1 (hyAs j₁) _ _ _ _ (hcj j (tt a) (ss a) (hfam a).2.2.1).2.2
      (hcj j₁ (tt a) (ss a) (hfam a).2.2.1).2.2
  have hTJ : ThJetT x'.P x'.rig m (spMap (algebraMap (FractionRing V) C)) th pt yA (fun a => Sf a j₁) Ss := by
    refine ⟨Θ, tt, i₀, cj, fun a => ⟨(hfam a).1, (hfam a).2.1⟩, hi₀, fun a j => ?_⟩
    have h := (hcj j (tt a) (ss a) (hfam a).2.2.1).2.2
    have e := hind a j
    simp only [hSf] at e
    rw [e] at h
    exact h
  have hJC := hJ m th _ pt yA (fun a => Sf a j₁) Ss hOn (fun j => ⟨(hyA j).1, hyAs j⟩) hTJ
  have hio : (fun a => io (pt a)) = levelPoint lev hgC := funext fun a => io.apply_symm_apply _
  rw [hio] at hJC
  obtain ⟨th'', hth'', hsc, hJsc⟩ := GlobalTheory.T.thetaKeyRule_scale_section_pow_eight κ hHom C xC c⁻¹ (inv_ne_zero hc)
  have hJ'' := hJsc x.P.g hgC m _ (levelPoint lev hgC) _ _ hJC
  set x'' : KeyIn C := ⟨xC.P, xC.g_pos, xC.rig, xC.rig_gen, th'', hth'', xC.v, xC.basis⟩ with hx''

  have hadm : AdmBase V (IsLocalRing.maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hcomp⟩
  obtain ⟨q, hq⟩ := GlobalTheory.T.degenerationValues_int_of_admissibleBase V _ hadm D C hCE N ν hInt
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  obtain ⟨hrg, hdisc⟩ := GlobalTheory.T.degenerationValues_norms_eq_uniformizer_zpow V ϖ hϖ D C hCE N ν hInt
  have hϖm : ϖ ∈ IsLocalRing.maximalIdeal V := (IsLocalRing.mem_maximalIdeal _).2 hϖ.not_isUnit
  have ht1 : ‖toF V C ϖ‖ < 1 := hCE.2 ϖ hϖm
  have ht0 : toF V C ϖ ≠ 0 := by
    intro h
    have hinj : Function.Injective (toF V C) :=
      (algebraMap (FractionRing V) C).injective.comp (IsFractionRing.injective V (FractionRing V))
    exact hϖ.ne_zero (hinj (h.trans (map_zero _).symm))
  obtain ⟨β, π, hπ0, hπ1, hfinβ, hexp⟩ := GlobalTheory.T.exists_integralForm_parameter_of_discreteNorms C N q (toF V C ϖ) hq ht0 ht1 hdisc m hm1
  choose bd hbd using fun a j => GlobalTheory.T.thetaTranslateTerms_jets_bounded V D C hCE N ν hInt q hq m hmOdd (Q a) (s' a) (ff a) (hs'V a)
    (hfam a).2.2.2.1 (gm₀ j) (gm j) (hT j).2.1 (hT j).2.2
  haveI : NeZero (m ^ 2) := ⟨by omega⟩
  set B : ℝ := ∑ a, ∑ j, |bd a j| with hB
  have hbB : ∀ a j, bd a j ≤ B := fun a j =>
    (le_abs_self _).trans ((Finset.single_le_sum (f := fun j => |bd a j|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ j)).trans (Finset.single_le_sum (f := fun a => ∑ j, |bd a j|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ a)))
  obtain ⟨k₀, hBK, hk₀⟩ := GlobalTheory.T.exists_abelianKeyValue_norm_one κ hR4 V D.toPre C hCE N ν hInt vB hAd.1
  have hAF := GlobalTheory.T.archimedeanExistence_of_complex_isomorphic_field κ hFun (GlobalTheory.T.keyRule_complex_existence_jets_key_value κ hR4)
  obtain ⟨ε, hε, hAε⟩ := hAF V D.toPre D.psi_even D.tau_bimult C e N ν x.P.g r m (m ^ 2) x.g_pos hmOdd dvd_rfl β ζ Q hQL
    s' (fun a => ⟨ff a, hs'V a, (hfam a).2.2.2.1⟩) vB bX σ gm hAd k₀ hBK
  set nn : N.X → ℕ := fun α => (β.be α α / (2 * m ^ 2)).toNat with hnn
  set aa : (Fin (2 * x.P.g) → ZMod (m ^ 2)) → N.X → C :=
    fun a α => (jc ν (s' a) (gm j₁) α).fst / ν.rg ^ (m ^ 2) with haa
  set bb : (Fin (2 * x.P.g) → ZMod (m ^ 2)) → Fin x.P.g → N.X → C :=
    fun a j α => (jc ν (s' a) (gm j) α).snd / ν.rg ^ (m ^ 2) with hbb
  have hSa : ∀ a, c⁻¹ * Sf a j₁ = ∑' α, aa a α := fun a => by
    rw [hSf, ← tsum_mul_left]
    congr 1
    funext α
    simp only [haa, hs', jc_smul, TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_inl]
    ring
  have hSb : ∀ a j, c⁻¹ * Ss a j = ∑' α, bb a j α := fun a j => by
    rw [hSs, ← tsum_mul_left]
    congr 1
    funext α
    simp only [hbb, hs', jc_smul, TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl]
    simp
    ring
  have hJ3 : ThJet x'' hgC m (levelPoint lev hgC) (fun i => ∑' α, aa i α) (fun i j => ∑' α, bb i j α) := by
    have e1 : (fun i => ∑' α, aa i α) = fun i => c⁻¹ * Sf i j₁ := funext fun i => (hSa i).symm
    have e2 : (fun i j => ∑' α, bb i j α) = fun i j => c⁻¹ * Ss i j := funext fun i => funext fun j => (hSb i j).symm
    rw [e1, e2]
    exact hJ''
  have hba : ∀ i α, ‖aa i α‖ ≤ B * ‖π‖ ^ nn α := fun i α => by
    have h := ((hbd i j₁) α).1
    rw [hexp α] at h
    exact h.trans (mul_le_mul_of_nonneg_right (hbB i j₁) (pow_nonneg (norm_nonneg _) _))
  have hbb' : ∀ i j α, ‖bb i j α‖ ≤ B * ‖π‖ ^ nn α := fun i j α => by
    have h := ((hbd i j) α).2
    rw [hexp α] at h
    exact h.trans (mul_le_mul_of_nonneg_right (hbB i j) (pow_nonneg (norm_nonneg _) _))
  have hDef : Deform κ (e : C →+* ℂ) x'' hgC m ζ lev k₀ := by
    refine deform_of_series κ C (e : C →+* ℂ) x'' x.P.g hgC m ζ lev k₀ N.X nn π B aa bb hπ0 hπ1 hfinβ hba hbb' hJ3
      ⟨ε, hε, fun u hu hu' => ?_⟩
    obtain ⟨hsm, x₀, hg₀, lev₀, ϑ₀, hϑ₀, hJ₀, hk⟩ := hAε u hu hu'
    refine ⟨⟨fun i => (hsm i j₁).1, fun i j => (hsm i j).2⟩, x₀, hg₀, lev₀, ?_, hk⟩
    have e3 : ϑ₀ = fun i => ∑' α, (e : C →+* ℂ) (aa i α) * u ^ nn α := funext fun i => hϑ₀ i j₁
    rw [e3] at hJ₀
    exact hJ₀
  have hk := hj₀ j (le_max_left _ _) C (e : C →+* ℂ) x'' hgC ζ lev k₀ hDef
  have h1 : (κ C xC : C) = toF V C u * algebraMap (FractionRing V) C (κ (FractionRing V) x) := by
    rw [hκC, hu, map_mul]
    rfl
  have h2 : c⁻¹ ^ 8 * k₀ = toF V C u * algebraMap (FractionRing V) C (κ (FractionRing V) x) := by
    rw [← hk]
    exact hsc.trans h1
  have h3 := congrArg norm h2
  rw [norm_mul, norm_mul, norm_pow, norm_inv, hk₀, norm_toF_unit hCE u, _root_.mul_one, _root_.one_mul] at h3
  rw [← h3, inv_pow, mul_inv_cancel₀ (pow_ne_zero _ (norm_ne_zero_iff.2 hc))]

end GlobalTheory.MBLow.KapFPf
