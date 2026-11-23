import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Formalism.LocalRingCardinality.DataParamsT
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.MeanLogLeOfBounds
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FgIntOfForallIsIntegral
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNumberFieldFrameValueNeZeroOfComplex
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LocalLowerBoundCmPointFramePolynomialEveryPrime
import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.LargeResidueExtensionLemma
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TestValueEqConstMulReadingSecZ
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsEqProdBlockDetPolyPowMul
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsCompleteDVRCompletionIntegralIffStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsCmPointLocalModelOverDvrStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsIntegralEigenbasisOfFrameAtLocalModelStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUnitIntegralGeneratorPrincipalLocalModelStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieLetterIntegralInIntegralEigenbasisStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IntegralGeneratorAssociatedLocalGeneratorCMLineStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmPointEigenbasisChangeDetIntegralAlmostAllPrimeStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointBaseChangeAlgebraMap
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueFrameChangeByMatrices
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelationBaseChangeFieldZpow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClearDenominatorsFramePolynomialAtPrime
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LamT (CMPt)
open GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.CoeffDenomZ

open GlobalTheory.LamT GlobalTheory.CoeffDenom in

theorem exists_clear_coeff_at_prime_any : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (z : CMPt Xo c) (f : ℕ) (La : ℝ), z.Good f La →
    ∀ (e : Formalism.L2.Pj.Ix Dw → ℤ) (k : (E →+* ℂ) → ℕ), ∀ p : IsDedekindDomain.HeightOneSpectrum (𝓞 z.K),
    ∃ x : 𝓞 z.K, x ≠ 0 ∧ ∀ F ∈ GlobalTheory.AllWt.secZ Xo c e, (∀ v, ∀ w ∈ valSet Xo c (algCls Xo c) v, 0 ≤ w F) →
      ∀ G : MvPolynomial (Formalism.L2.LamCM.FrVar Dw.mult) z.K, (∀ (y' : FrPt Xo c z.K) (Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) z.K),
          (∀ b, (Y b).det ≠ 0) → GlobalTheory.Frames.FrChg (fun b => (Y b).transpose) 1 z.y y' →
          (∏ b, (Y b).det ^ k b) * evR Xo c F y' = Formalism.L2.LamCM.evalFr G Y) →
        ∀ μ, p.valuation z.K ((x : z.K) * MvPolynomial.coeff μ G) ≤ 1 := by
  intro E _ _ _ H Dw l Xo c _ z f La hz e k p
  classical
  obtain ⟨T, iK, hT, hiK⟩ := GlobalTheory.T.exists_completeDVR_completion_integral_iff z.K p
  obtain ⟨M⟩ := (GlobalTheory.T.exists_cmPoint_localModel_over_dvr E H Dw l Xo c z T iK).1 fun a => (hiK _).2 (p.valuation_le_one a)
  let io : c.F →+* T.Fr := iK.comp (algebraMap c.F z.K)
  letI := io.toAlgebra
  let φ : z.K →ₐ[c.F] T.Fr := { iK with commutes' := fun _ => rfl }
  obtain ⟨yT, hyT⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c _ _ φ z.y
  have hyx : yT.x = spMap iK ≫ z.x := by rw [hyT.1, hz.2.2.2.1]
  obtain ⟨g, hg, hgL⟩ := (GlobalTheory.T.exists_integralEigenbasis_of_frame_at_localModel E H Dw l Xo c T io M.G.t M.t'.t _ M.m1 M.m2 yT hyx).1
  obtain ⟨s, hsS⟩ := GlobalTheory.T.exists_unit_integral_generator_principal_local_model E H Dw l Xo c T io M.G M.t'.t _ M.m1 M.m2 yT hyx
  obtain ⟨y', hy', -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c T.Fr yT g s hg
  have hL := hgL _ _ hy'
  have hS := hsS _ _ hy'
  choose c0 hc0 using fun (b : E →+* ℂ) (j : Fin (Dw.mult b)) =>
    LocClause.exists_isLocGen p (z.ℓ (z.e ⟨b, j⟩)).I
  let cl : ∀ b : E →+* ℂ, Fin (Dw.mult b) → T.Fr := fun b j => iK (c0 b j)
  have hcl : ∀ b j i, cl b j * (g b)⁻¹ j i ∈ Set.range (algebraMap T.V T.Fr) := fun b j i =>
    GlobalTheory.T.lieLetter_integral_in_integral_eigenbasis E H Dw l Xo c z f La hz p T iK M hiK φ yT y' g s rfl hyT hy' hg hL b j i _ (hc0 b j)
  have hloc := GlobalTheory.FrameCoeffLocZ.coeff_mul_prod_zpow_mem_det E H Dw l Xo c z f La hz e k p T iK hT hiK M φ yT y' g s rfl hyT hy' s.ne_zero hg
    hL hS cl hcl

  let D : ℤ := ∑ b, ((Dw.mult b : ℤ) * (k b : ℤ) + ∑ i : Fin (Dw.mult b), e (some ⟨b, i⟩))
  let S : Finset (Formalism.L2.LamCM.FrVar Dw.mult →₀ ℕ) := (Finsupp.finite_of_degree_le (σ := Formalism.L2.LamCM.FrVar Dw.mult) D.toNat).toFinset
  let τ : T.Fr := ∏ b, (g b).det ^ k b
  let yμ : (Formalism.L2.LamCM.FrVar Dw.mult →₀ ℕ) → T.Fr := fun μ =>
    τ * (∏ v : Formalism.L2.LamCM.FrVar Dw.mult, cl v.1 v.2.2 ^ μ v)⁻¹ * ((s : T.Fr) ^ e none)⁻¹
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors T.V) (S.image yμ)

  obtain ⟨ϖ, hϖp, hϖ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot p.ne_bot
  have hϖv : p.valuation z.K (ϖ : z.K) < 1 := (p.valuation_lt_one_iff_mem ϖ).2 hϖp
  obtain ⟨π, hπ⟩ := (hiK (ϖ : z.K)).2 (p.valuation_le_one ϖ)
  have hϖK : (ϖ : z.K) ≠ 0 := fun h => hϖ0 (RingOfIntegers.coe_eq_zero_iff.1 h)
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [map_zero, eq_comm, map_eq_zero] at hπ
    exact hϖK hπ
  have hπu : ¬ IsUnit π := by
    rintro ⟨u, rfl⟩
    have h1 : iK ((ϖ : z.K)⁻¹) ∈ Set.range (algebraMap T.V T.Fr) := by
      refine ⟨((u⁻¹ : T.Vˣ) : T.V), ?_⟩
      rw [map_inv₀, ← hπ]
      exact map_units_inv (algebraMap T.V T.Fr) u
    have h2 := (hiK _).1 h1
    rw [map_inv₀] at h2
    have h0 : p.valuation z.K (ϖ : z.K) ≠ 0 := (Valuation.ne_zero_iff _).2 hϖK
    have h4 : (1 : _) ≤ p.valuation z.K (ϖ : z.K) :=
      calc (1 : _) = p.valuation z.K (ϖ : z.K) * (p.valuation z.K (ϖ : z.K))⁻¹ := (mul_inv_cancel₀ h0).symm
        _ ≤ p.valuation z.K (ϖ : z.K) * 1 := by gcongr
        _ = p.valuation z.K (ϖ : z.K) := mul_one _
    exact absurd hϖv (not_lt.2 h4)
  obtain ⟨N, t, hNt⟩ := dvd_pow_of_ne_zero_of_not_isUnit (nonZeroDivisors.ne_zero d.2) hπ0 hπu
  refine ⟨ϖ ^ N, pow_ne_zero _ hϖ0, ?_⟩
  intro F hF hv G hG μ
  by_cases hμ : MvPolynomial.coeff μ G = 0
  · simp [hμ]
  have hG1 := hG
  have hdeg := GlobalTheory.FrameHomZ.frPoly_secZ_degree_eq_any E H Dw l Xo c z.K z.y e k F hF G hG1 μ hμ
  have hμS : μ ∈ S := by
    simp only [S, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    omega
  obtain ⟨w, hw⟩ := hloc F hF hv G hG1 μ
  obtain ⟨r, hr⟩ := hd (yμ μ) (Finset.mem_image_of_mem yμ hμS)
  apply (hiK _).1
  have hP : (∏ v : Formalism.L2.LamCM.FrVar Dw.mult, cl v.1 v.2.2 ^ μ v) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun v _ => pow_ne_zero _ ((map_ne_zero iK).2 (hc0 v.1 v.2.2).1)
  have hc : iK (MvPolynomial.coeff μ G) = yμ μ * algebraMap T.V T.Fr w := by
    have hsn : ((s : T.Fr) ^ e none) ≠ 0 := zpow_ne_zero _ s.ne_zero
    have e0 : yμ μ * algebraMap T.V T.Fr w = (τ * algebraMap T.V T.Fr w) *
        ((∏ v : Formalism.L2.LamCM.FrVar Dw.mult, cl v.1 v.2.2 ^ μ v)⁻¹ * ((s : T.Fr) ^ e none)⁻¹) := by
      simp only [yμ]; ring
    rw [e0, ← hw]
    field_simp
  rw [Algebra.smul_def] at hr
  have e1 : (((ϖ ^ N : 𝓞 z.K)) : z.K) = (ϖ : z.K) ^ N := by simp
  refine ⟨t * r * w, ?_⟩
  rw [map_mul iK, e1, map_pow, ← hπ, ← map_pow, hNt, hc]
  simp only [map_mul]
  rw [hr]
  ring

end GlobalTheory.CoeffDenomZ

namespace GlobalTheory.CoeffIntZ

theorem coeff_valuation_le_one_almost_all_any : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (z : CMPt Xo c) (f : ℕ) (La : ℝ), z.Good f La →
    ∀ (e : Formalism.L2.Pj.Ix Dw → ℤ) (k : (E →+* ℂ) → ℕ),
    ∃ S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 z.K)), ∀ p ∉ S,
      ∀ F ∈ GlobalTheory.AllWt.secZ Xo c e, (∀ v, ∀ w ∈ valSet Xo c (algCls Xo c) v, 0 ≤ w F) →
      ∀ G : MvPolynomial (Formalism.L2.LamCM.FrVar Dw.mult) z.K, (∀ (y' : FrPt Xo c z.K) (Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) z.K),
          (∀ b, (Y b).det ≠ 0) → GlobalTheory.Frames.FrChg (fun b => (Y b).transpose) 1 z.y y' →
          (∏ b, (Y b).det ^ k b) * evR Xo c F y' = Formalism.L2.LamCM.evalFr G Y) →
        ∀ μ, p.valuation z.K (MvPolynomial.coeff μ G) ≤ 1 := by
  intro E _ _ _ H Dw l Xo c _ z f La hz e k
  classical
  obtain ⟨S₁, hS₁⟩ := GlobalTheory.T.cmPoint_eigenbasis_change_det_integral_almost_all_primes E H Dw l Xo c z f La hz
  have hfin : (⋃ j, {p : IsDedekindDomain.HeightOneSpectrum (𝓞 z.K) |
      FractionalIdeal.count z.K p (z.ℓ j).I ≠ 0}).Finite :=
    Set.finite_iUnion fun j => Filter.eventually_cofinite.1 (FractionalIdeal.finite_factors (z.ℓ j).I)
  have hfinT := Filter.eventually_cofinite.1 (FractionalIdeal.finite_factors z.Tl.I)
  refine ⟨S₁ ∪ hfin.toFinset ∪ hfinT.toFinset, fun p hp F hF hv G hG μ => ?_⟩
  simp only [Finset.mem_union, not_or, Set.Finite.mem_toFinset, Set.mem_iUnion, Set.mem_setOf_eq, not_exists,
    not_not] at hp
  obtain ⟨⟨hp1, hp2⟩, hp3⟩ := hp
  have hgen : ∀ j, Formalism.L2.LamCM.IsLocGen p (1 : z.K) (z.ℓ j).I := fun j =>
    ⟨one_ne_zero, by rw [FractionalIdeal.spanSingleton_one, FractionalIdeal.count_one, hp2 j]⟩
  obtain ⟨T, iK, hT, hiK⟩ := GlobalTheory.T.exists_completeDVR_completion_integral_iff z.K p
  obtain ⟨M⟩ := (GlobalTheory.T.exists_cmPoint_localModel_over_dvr E H Dw l Xo c z T iK).1 fun a => (hiK _).2 (p.valuation_le_one a)
  let io : c.F →+* T.Fr := iK.comp (algebraMap c.F z.K)
  letI := io.toAlgebra
  let φ : z.K →ₐ[c.F] T.Fr := { iK with commutes' := fun _ => rfl }
  obtain ⟨yT, hyT⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c _ _ φ z.y
  have hyx : yT.x = spMap iK ≫ z.x := by rw [hyT.1, hz.2.2.2.1]
  obtain ⟨g, hg, hgL⟩ := (GlobalTheory.T.exists_integralEigenbasis_of_frame_at_localModel E H Dw l Xo c T io M.G.t M.t'.t _ M.m1 M.m2 yT hyx).1
  obtain ⟨s, hsS⟩ := GlobalTheory.T.exists_unit_integral_generator_principal_local_model E H Dw l Xo c T io M.G M.t'.t _ M.m1 M.m2 yT hyx
  obtain ⟨y', hy', -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c T.Fr yT g s hg
  have hL := hgL _ _ hy'
  have hS := hsS _ _ hy'
  have hinv : ∀ b j i, (g b)⁻¹ j i ∈ Set.range (algebraMap T.V T.Fr) := fun b j i => by
    have := GlobalTheory.T.lieLetter_integral_in_integral_eigenbasis E H Dw l Xo c z f La hz p T iK M hiK φ yT y' g s rfl hyT hy' hg hL b j i 1 (hgen _)
    rwa [map_one, _root_.one_mul] at this
  have hR : ∀ x : T.Fr, x ∈ Set.range (algebraMap T.V T.Fr) ↔ x ∈ (algebraMap T.V T.Fr).range :=
    fun x => (RingHom.mem_range).symm
  have hdetinv : ∀ b, ((g b).det)⁻¹ ∈ (algebraMap T.V T.Fr).range := fun b => by
    choose N hN using hinv b
    have e1 : (g b)⁻¹ = (Matrix.of N).map (algebraMap T.V T.Fr) := by
      ext j i; exact (hN j i).symm
    have e2 : ((g b).det)⁻¹ = ((g b)⁻¹).det := by
      rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
    rw [e2, e1]
    exact ⟨(Matrix.of N).det, by rw [RingHom.map_det]; rfl⟩
  have hall := (hR _).1 (hS₁ p hp1 T iK hT hiK M φ yT y' g s rfl hyT hy' hg hL)
  have hdet : ∀ b, (g b).det ∈ (algebraMap T.V T.Fr).range := fun b => by
    have hne : (∏ b' ∈ Finset.univ.erase b, (g b').det) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun b' _ => (hg b').ne_zero
    have e3 : (g b).det = (∏ b', (g b').det) * ∏ b' ∈ Finset.univ.erase b, ((g b').det)⁻¹ := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ b), Finset.prod_inv_distrib, _root_.mul_assoc,
        mul_inv_cancel₀ hne, _root_.mul_one]
    rw [e3]
    exact Subring.mul_mem _ hall (Subring.prod_mem _ fun b' _ => hdetinv b')
  have hτ : (∏ b, (g b).det ^ k b) ∈ (algebraMap T.V T.Fr).range :=
    Subring.prod_mem _ fun b _ => Subring.pow_mem _ (hdet b) _
  obtain ⟨w, hw⟩ := GlobalTheory.FrameCoeffLocZ.coeff_mul_prod_zpow_mem_det E H Dw l Xo c z f La hz e k p T iK hT hiK M φ yT y' g s rfl
    hyT hy' s.ne_zero hg hL hS (fun _ _ => 1) (fun b j i => by rw [_root_.one_mul]; exact hinv b j i) F hF hv G hG μ
  simp only [one_pow, Finset.prod_const_one, _root_.mul_one] at hw

  have hgenT : Formalism.L2.LamCM.IsLocGen p (1 : z.K) z.Tl.I := by
    refine ⟨one_ne_zero, ?_⟩
    rw [FractionalIdeal.spanSingleton_one, FractionalIdeal.count_one]
    simpa using hp3.symm
  obtain ⟨u, hu⟩ := GlobalTheory.T.integralGenerator_associated_localGenerator_CM_line E H Dw l Xo c z f La hz p T iK M hiK φ yT y' g s rfl hyT hy' hS 1 hgenT
  rw [map_one, _root_.one_mul] at hu
  have hsn : ((s : T.Fr) ^ e none) ≠ 0 := zpow_ne_zero _ s.ne_zero
  have hsinv : ((s : T.Fr) ^ e none)⁻¹ ∈ (algebraMap T.V T.Fr).range := by
    refine ⟨((u ^ (-e none) : T.Vˣ) : T.V), ?_⟩
    have h1 : algebraMap T.V T.Fr ((u ^ (-e none) : T.Vˣ) : T.V) =
        ((Units.map (algebraMap T.V T.Fr : T.V →* T.Fr) (u ^ (-e none)) : T.Frˣ) : T.Fr) := rfl
    rw [h1, map_zpow, Units.val_zpow_eq_zpow_val, hu, zpow_neg]
    rfl
  have hc : iK (MvPolynomial.coeff μ G) = (∏ b, (g b).det ^ k b) * algebraMap T.V T.Fr w * ((s : T.Fr) ^ e none)⁻¹ :=
    (eq_mul_inv_iff_mul_eq₀ hsn).2 hw
  refine (hiK _).1 ((hR _).2 ?_)
  rw [hc]
  exact Subring.mul_mem _ (Subring.mul_mem _ hτ (RingHom.mem_range_self _ _)) hsinv

end GlobalTheory.CoeffIntZ
