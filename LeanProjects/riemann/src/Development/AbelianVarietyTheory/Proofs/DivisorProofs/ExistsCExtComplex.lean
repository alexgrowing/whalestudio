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
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteIsAlgClosedComplexRatVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionNonzeroFibresUnitMultipleThetaSeriesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitOfNormOneFractionRingDvrStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralSectionExpandsIntegrallyGenericFibreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDegenerationDataValuesUltrametricStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HvHolds
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FamiliesValuesCorrespond
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRescaledIsoPreservingRigidificationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionTransportAlongGeneratingIsoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsoCancelPulledBundlesGermsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecMapsSecPullOfPointwiseGermsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsoPreservesRigidificationAtOriginStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UMin.KeySmall

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

end GlobalTheory.UMin.KeySmall

namespace GlobalTheory.UMin.KeySmall

set_option maxHeartbeats 4000000 in

theorem norm_key_eq_one : ∀ κ : Rule, Rule4 κ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V],
    IsAdicComplete (IsLocalRing.maximalIdeal V) V →
    ∀ (D : DegData V (IsLocalRing.maximalIdeal V)) (x : KeyIn (FractionRing V)) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G],
    IsSemiAbelian G → ∀ (U : Unif (IsLocalRing.maximalIdeal V) D x.P G) (w₀ : GlobalTheory.UT.W0 U.toUnifPre),
    GlobalTheory.UT.NormW U.toUnifPre w₀ x.rig → ∀ y : Fin x.P.g → (epsR V ⟶ G), IsLieBasis y →
    (∀ i, IsVecOver (algebraMap V (FractionRing V)) (U.gen.inv.left ≫ pullback.fst G.hom (jK V)) (y i) (x.v i)) →
    ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C]
      [Algebra (FractionRing V) C], CExt V (IsLocalRing.maximalIdeal V) C → Nonempty (C ≃+* ℂ) →
    ∀ (N : NumD C) (ν : NumOf D.toPre C N), ν.IntN → ∀ (th : GlobalTheory.UT.SecA x.P C 1) (ϑ : Fam D.toPre C 1) (c : C),
      IsPolAVSectionInverseImage x.P (TFK (R := V) C) x.th th → U.ExpandsF C 1 w₀ th ϑ → ν.FamV ϑ (c • N.vth) →
      ‖c‖ ^ 8 * ‖algebraMap (FractionRing V) C (κ (FractionRing V) x : FractionRing V)‖ = 1 := by
  intro κ hR4
  obtain ⟨hHom, hFun, hTh1, hFamU⟩ := id hR4
  intro V _ _ _ _ hcomp D x G _ _ hSA U w₀ hNW y hy hyv C _ _ _ _ _ _ hCE hiso N ν hInt th ϑ c hOn hExp hFV
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

end GlobalTheory.UMin.KeySmall

namespace GlobalTheory.UMin.KeySmall

open Cardinal IsLocalRing GlobalTheory.RatNorm in
set_option maxHeartbeats 800000 in

theorem exists_cExt_complex : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], #V ≤ 𝔠 →
    ∃ (C : Type) (_ : NontriviallyNormedField C) (_ : IsUltrametricDist C) (_ : CompleteSpace C) (_ : IsAlgClosed C)
      (_ : CharZero C) (_ : Algebra (FractionRing V) C), CExt V (IsLocalRing.maximalIdeal V) C ∧ Nonempty (C ≃+* ℂ) := by
  intro V _ _ _ _ hcV
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  let K := FractionRing V
  have hϖm : ϖ ∈ maximalIdeal V := hϖ.not_isUnit
  obtain ⟨w, hw, hw1, hwa⟩ := GlobalTheory.exists_absoluteValue_of_isDiscreteValuationRing V K hϖ.ne_zero hϖm
    (r := 1 / 2) (by norm_num) (by norm_num)

  letI : NontriviallyNormedField (WithAbs w) :=
    { (inferInstance : NormedField (WithAbs w)) with
      non_trivial := ⟨(WithAbs.toAbs w (algebraMap V K ϖ))⁻¹, by
        rw [norm_inv]
        change 1 < (w (algebraMap V K ϖ))⁻¹
        rw [hwa]
        norm_num⟩ }
  haveI : IsUltrametricDist (WithAbs w) :=
    IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun x y => hw x.ofAbs y.ofAbs
  let K₁ := UniformSpace.Completion (WithAbs w)
  letI : NontriviallyNormedField K₁ := completionNontriviallyNormedField (WithAbs w)
  haveI : IsUltrametricDist K₁ := IsUltrametricDist.of_normedAlgebra (WithAbs w)
  let K₂ := AlgebraicClosure K₁
  letI : NontriviallyNormedField K₂ := spectralNorm.nontriviallyNormedField K₁ K₂
  letI : NormedAlgebra K₁ K₂ := spectralNorm.normedAlgebra K₁ K₂
  haveI : IsUltrametricDist K₂ := IsUltrametricDist.of_normedAlgebra K₁
  let C := UniformSpace.Completion K₂
  letI : NontriviallyNormedField C := completionNontriviallyNormedField K₂
  haveI : IsUltrametricDist C := IsUltrametricDist.of_normedAlgebra K₂
  haveI : IsAlgClosed C := isAlgClosed_of_denseRange (K := K₂) UniformSpace.Completion.denseRange_coe
  let i : K →+* C := (algebraMap K₂ C).comp ((algebraMap K₁ K₂).comp
    ((algebraMap (WithAbs w) K₁).comp (WithAbs.equiv w).symm.toRingHom))
  have hi : ∀ x : K, ‖i x‖ = w x := by
    intro x
    have h₁ : ∀ y : K₂, ‖algebraMap K₂ C y‖ = ‖y‖ := fun y => UniformSpace.Completion.norm_coe y
    have h₂ : ∀ y : K₁, ‖algebraMap K₁ K₂ y‖ = ‖y‖ := fun y => spectralNorm_extends y
    have h₃ : ∀ y : WithAbs w, ‖algebraMap (WithAbs w) K₁ y‖ = ‖y‖ :=
      fun y => UniformSpace.Completion.norm_coe y
    simp only [i, RingHom.comp_apply, h₁, h₂, h₃]
    rfl
  letI : Algebra K C := i.toAlgebra
  have hiV : Function.Injective (i.comp (algebraMap V K)) :=
    i.injective.comp (IsFractionRing.injective V K)
  haveI : CharZero C := charZero_of_injective_ringHom hiV

  have hc0 : #(WithAbs w) ≤ 𝔠 := by
    rw [Cardinal.mk_congr (WithAbs.equiv w).toEquiv, Cardinal.mk_fractionRing]; exact hcV
  have hc1 : #K₁ ≤ 𝔠 := mk_le_of_dense _ UniformSpace.Completion.denseRange_coe hc0
  have hc2 : #K₂ ≤ 𝔠 :=
    (Algebra.IsAlgebraic.cardinalMk_le_max K₁ K₂).trans (max_le hc1 aleph0_le_continuum)
  have hc3 : #C ≤ 𝔠 := mk_le_of_dense _ UniformSpace.Completion.denseRange_coe hc2
  have hC : #C = 𝔠 := le_antisymm hc3 (continuum_le_cardinal_of_nontriviallyNormedField C)
  refine ⟨C, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    ⟨fun a => ?_, fun a ha => ?_⟩, ?_⟩
  · change ‖i _‖ ≤ 1
    rw [hi]; exact (hw1 _).2 ⟨a, rfl⟩
  · change ‖i _‖ < 1
    rw [hi]
    rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at ha
    obtain ⟨s, rfl⟩ := ha
    rw [map_mul, map_mul, hwa]
    have := (hw1 (algebraMap V K s)).2 ⟨s, rfl⟩
    linarith
  · exact IsAlgClosed.ringEquiv_of_equiv_of_charZero (K := C) (L := ℂ)
      (by rw [hC]; exact Cardinal.aleph0_lt_continuum)
      (Cardinal.eq.1 (by rw [hC, Cardinal.mk_complex]))

open Cardinal GlobalTheory.KeyEven in

theorem key_unit_unif (κ : Rule) (hR : Rule4 κ) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V]
    (hcpl : IsAdicComplete (IsLocalRing.maximalIdeal V) V) (hcV : #V ≤ 𝔠)
    (D : DegData V (IsLocalRing.maximalIdeal V)) (x : KeyIn (FractionRing V)) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G]
    (hG : IsSemiAbelian G) (U : Unif (IsLocalRing.maximalIdeal V) D x.P G) (w₀ : GlobalTheory.UT.W0 U.toUnifPre)
    (hN : GlobalTheory.UT.NormW U.toUnifPre w₀ x.rig) (y : Fin x.P.g → (epsR V ⟶ G)) (hy : IsLieBasis y)
    (hvec : ∀ i, GlobalTheory.IsVecOver (algebraMap V (FractionRing V)) (U.gen.inv.left ≫ pullback.fst G.hom (jK V)) (y i) (x.v i))
    (σ : U.LG.L.Sec) (hNz : NzFib σ)
    (hMaps : GlobalTheory.Cartier.SecMaps w₀ (GlobalTheory.Cartier.secPull x.th U.gen.hom.left)
      (GlobalTheory.Cartier.secPull σ (pullback.fst G.hom (jK V)))) :
    ∃ u : Vˣ, (κ (FractionRing V) x : FractionRing V) = algebraMap V (FractionRing V) u := by
  obtain ⟨C, i1, i2, i3, i4, i5, i6, hC, hCC⟩ := exists_cExt_complex V hcV
  obtain ⟨N, ν, hInt⟩ := GlobalTheory.T.exists_degenerationData_values_ultrametric V hcpl D C hC
  obtain ⟨σ₁, f, th, ϑ, h1, h2, h3, h4, h5⟩ := GlobalTheory.T.integralSection_expands_integrally_genericFibre V hcpl D x.P G hG U w₀ hN.1 x.th σ hMaps C
  have hL : GlobalTheory.UT.LL := GlobalTheory.Ex.hv_holds.1
  have hfam : BrFamSt := GlobalTheory.Ex.brFam hL.1 hL.2.1
  obtain ⟨hv₁, -, -, -, hv₅, -⟩ := hfam V D.toPre D.psi_even D.tau_bimult C N ν 1 le_rfl
  obtain ⟨f', hf', -⟩ := hv₁ ϑ
  obtain ⟨c, rfl⟩ := hv₅ ϑ f' hf'
  have hc : ‖c‖ = 1 := GlobalTheory.T.section_nonzero_fibres_unit_multiple_thetaSeries V hcpl D x.P G hG U σ σ₁ f hNz h1 h2 C hC N ν hInt ϑ c h5 hf'
  have e := norm_key_eq_one κ hR V hcpl D x G hG U w₀ hN y hy hvec C hC hCC N ν hInt th ϑ c h3 h4 hf'
  rw [hc, one_pow, _root_.one_mul] at e
  exact GlobalTheory.T.exists_unit_of_norm_one_fractionRing_dvr V C hC _ e

theorem dualMapR_eq_of_map {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (F : DualNumber R →+* DualNumber R')
    (h1 : ∀ a, F (algebraMap R _ a) = algebraMap R' _ (f a)) (h2 : F DualNumber.eps = DualNumber.eps) :
    F = Chart.dualMapR f := by
  refine RingHom.ext fun a => ?_
  have hx : ∀ (S : Type) [CommRing S] (b : DualNumber S),
      b = algebraMap S (DualNumber S) (TrivSqZeroExt.fst b) + algebraMap S (DualNumber S) (TrivSqZeroExt.snd b) * DualNumber.eps := by
    intro S _ b
    rw [← Algebra.smul_def, ← DualNumber.inr_eq_smul_eps, TrivSqZeroExt.algebraMap_eq_inl,
      TrivSqZeroExt.inl_fst_add_inr_snd_eq]
  have hF : F a = algebraMap R' (DualNumber R') (f (TrivSqZeroExt.fst a)) +
      algebraMap R' (DualNumber R') (f (TrivSqZeroExt.snd a)) * DualNumber.eps := by
    conv_lhs => rw [hx R a]
    rw [map_add, map_mul, h1, h1, h2]
  rw [hF, ← Algebra.smul_def, ← DualNumber.inr_eq_smul_eps, TrivSqZeroExt.algebraMap_eq_inl]
  rfl

open Cardinal GlobalTheory.KeyEven in

theorem key_unit_trait (κ : Rule) (hR : Rule4 κ) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V]
    (hA : IsAdicComplete (IsLocalRing.maximalIdeal V) V) (hF : #V ≤ 𝔠)
    (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (σ : L.L.Sec) (x : KeyIn (FractionRing V))
    (y : Fin x.P.g → (epsR V ⟶ G)) (hSA : IsSemiAbelian G) (hUn : HasUnif G L.L) (hLie : IsLieBasis y) (hNz : NzFib σ)
    (hKey : KeyOn (algebraMap V (FractionRing V)) x G L σ y) :
    ∃ u : Vˣ, (κ (FractionRing V) x : FractionRing V) = algebraMap V (FractionRing V) u := by
  obtain ⟨D, A, U, e, he⟩ := hUn
  obtain ⟨φ, hφe, ψ, F, hPB, hψ, hRig, hTh, hF1, hF2, hv⟩ := hKey
  obtain ⟨θ, hθm, hθφ⟩ := grpPullback_iso (isGrpPullback_pullback G (jK V)) hPB

  obtain ⟨e', he', heR⟩ := GlobalTheory.T.exists_rescaled_iso_preserving_rigidification G U.LG L e he
  obtain ⟨σ', hσ', hnz⟩ := GlobalTheory.T.exists_section_transport_along_generating_iso e' he' U.LG.isLB L.isLB σ
  obtain ⟨w₀, hw₀, hPW⟩ := GlobalTheory.T.exists_iso_cancel_pulled_bundles_germs θ.hom.left φ (pullback.fst G.hom (jK V)) hθφ x.P.L L.L U.LG.L x.P.isLB L.isLB U.LG.isLB ψ e' hψ he'
  let U' : Unif (IsLocalRing.maximalIdeal V) D x.P G :=
    { toUnifPre := { U.toUnifPre with gen := θ, gen_hom := hθm, ext := ⟨w₀, hw₀⟩ }, expand := U.expand }
  have hinv : U'.gen.inv.left ≫ pullback.fst G.hom (jK V) = φ := by
    show θ.inv.left ≫ pullback.fst G.hom (jK V) = φ
    rw [← hθφ, ← Category.assoc, ← Over.comp_left, θ.inv_hom_id, Over.id_left, Category.id_comp]
  have hFd := dualMapR_eq_of_map _ F hF1 hF2
  haveI : IsMonHom θ.hom := hθm
  refine key_unit_unif κ hR V hA hF D x G hSA U' w₀ ⟨hw₀, x.rig_gen, ?_⟩ y hLie (fun i => ?_) σ' ?_ ?_
  · exact GlobalTheory.T.iso_preserves_rigidification_at_origin V G x.P.A θ.hom φ hθφ hφe x.P.L L.L U.LG.L x.P.isLB L.isLB U.LG.isLB x.rig L.rig U.LG.rig ψ e' w₀ hPW hRig heR
  · show (x.v i).left ≫ (U'.gen.inv.left ≫ pullback.fst G.hom (jK V)) = _
    rw [hinv, hv i, hFd]
  · intro s
    obtain ⟨z, hz, hz'⟩ := hNz s
    exact ⟨z, hz, hnz hz'⟩
  · exact GlobalTheory.T.secMaps_secPull_of_pointwise_germs θ.hom.left φ _ hθφ x.P.L L.L U.LG.L L.isLB ψ e' w₀ hPW x.th σ σ' hTh hσ'

end GlobalTheory.UMin.KeySmall
