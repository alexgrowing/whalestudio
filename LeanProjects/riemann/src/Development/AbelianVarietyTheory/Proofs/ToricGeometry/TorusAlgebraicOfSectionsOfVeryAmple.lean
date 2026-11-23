import Mathlib
import ReciprocityTheory.ThetaQuasiPeriods.ThetaQuasiPeriodStatement
import ReciprocityTheory.ThetaQuasiPeriods.Transl
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.MemThetaDomainIffIsSiegelAddTranspose
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsMulDotProductLeOfIsCompactThetaDomain
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.DifferentiableOnThetaProdOfNormal
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ClassicalThetaLevelAndLinearIndependent
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.FourierCoeffUnitCubeTranslateOfEntirePeriodic
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.EntirePeriodicEqZeroOfFourierCoeffEqZero
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.CardLePowOfLinearIndependent
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.MemSpanThetaOfLevel
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.RiemannThetaLevelOneNeZero
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsApplySubSmulNeZeroAndApplyAddNeZero
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.MulVecOfRealVecAddMemSpanPeriodLattice
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.MemPeriodLatticeOfThetaTranslateEqUnitMul
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.LevelThreeSeparatesPoints
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.LevelThreeSeparatesTangentVectors
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ThetaConeIdealIsPrimeAndRingKrullDimLe
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsPrimitiveElementDiscriminantMultiple
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsConnectedAndDenseComplHypersurface
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsMvPolynomialOfPolyBoundOffHypersurface
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsConnectedUnramifiedCoverOfIrreducible
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsIsConnectedPrincipalOpen
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.PrincipalOpenDenseComplexPoints
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsConnectedBasicOpenComplexPointsOfDense
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsNhdsSubsetRange
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IntegralAndRationalOfPolynomialGrowth
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsIntegralAndRationalTheta
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.FiniteOfIsIntegralOfBirationalOfPresentation
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsIsHomogeneousOfMemSpanPow
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsIsHomogeneousEvalOfMulMemSpan
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsUniquePointOfRingHom
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsProjectiveModelPolarisedTorusThetaStatement
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.EqZeroOfForallAlgHomComplex
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.EvalDivOfIsHomogeneous
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.HolFamilyOfIsPullback
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsUniqueHomOfLocallyRegular
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsReducedTensorObjComplex
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.AdditionLevelTwoMul
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.LocallyOfFiniteTypeTensor
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.RingKrullDimOfEtaleMvPolynomial
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsTestFunctionsSubsetOfMemNhds
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsEtaleCoordsVanishing
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.FderivEqMulOfMemSpan
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsMemThetaLevelCharApplyNeZero
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsUnitOfComplexPoints
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.RelAmpleThetaBundleProjectiveModelStatement
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.FderivEqZeroOfAffine
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsIsGenTranslDiffComp
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TranslateTrivialEqOneOfFiniteTypePointsStatement
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.KrullDimLEAndIsLocalRingQuotientPow
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TranslationFixingBundleArtinPointEqOneStatement
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.MemPeriodLatticeOfExpThetaLinForm
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.AppellHumbertNormalFormOfLinearExponent
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ReFormPosOfThetaNeZero
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsThetaSeriesApplyNeZeroOfLargeFormStatement
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsComplementaryThetaOfLinearMap
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsTopLePreimageOfISupEqTop
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.PolarisedTorusAlgebraicOfParts
import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real

namespace GlobalTheory

theorem polarisedTorus_algebraic :
    (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ), τ.IsSymm → (τ.map Complex.im).PosDef → (∀ i, a i = 0 ∨ a i = 1 / 2) → (∀ i, b i = 0 ∨ b i = 1 / 2) → ∃ (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L g) (th : P.L.Sec), P.g = g ∧ (∀ z, z ∈ u.Λ ↔ ∃ m n : Fin g → ℤ, z = (fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ))) ∧ u.IsFn th (thetaChar τ a b) ∧ ∀ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ l ∈ u.Λ, F l ∈ u.Λ) → ∃ f : P.A ⟶ P.A, IsMonHom f ∧ ∀ z, u.ex (F z) = u.ex z ≫ f) := by
  have f0 := @GlobalTheory.siegelSubDomain_and_domainOpen
  have f1 := @GlobalTheory.thetaMTest_and_thetaSummable
  have f2 := @GlobalTheory.thetaHolo_of_domainOpen_of_mTest f0.2 f1.1
  have f3 := @GlobalTheory.classicalTheta_level_and_linearIndependent f0.1 f2 f1.1
  have f4 := @GlobalTheory.fourierCoeff_unitCube_translate_of_entire_periodic
  have f5 := @GlobalTheory.entire_periodic_eq_zero_of_fourierCoeff_eq_zero f4
  have f6 := @GlobalTheory.ClassicalTheta.card_le_pow_of_linearIndependent f4 f5
  have f7 := @GlobalTheory.ThetaSpan.mem_span_theta_of_level f6 f3
  have f8 := @GlobalTheory.riemannTheta_level_one_ne_zero f3
  have f9 := @GlobalTheory.exists_level_apply_ne_zero_of_two_le f8
  have f10 := @GlobalTheory.periodLattice_isLattice_of_mem_siegelH
  have f11 := @GlobalTheory.mem_periodLattice_of_theta_translate_eq_unit_mul f8 f10
  have f12 := @GlobalTheory.ThetaSeparation.level_three_separates_points f8 f11
  have f13 := @GlobalTheory.ThetaTangent.level_three_separates_tangent_vectors f8 f11 f10
  have f14 := @GlobalTheory.thetaConeIdeal_isPrime_and_ringKrullDim_le f3 f6
  have f15 := @GlobalTheory.noetherNormalization_primitive
  have f16 := @GlobalTheory.isConnected_and_dense_compl_hypersurface
  have f17 := @GlobalTheory.exists_mvPolynomial_of_poly_bound_off_hypersurface
  have f18 := @GlobalTheory.isConnected_unramified_cover_of_irreducible f16 f17
  have f19 := @GlobalTheory.exists_isConnected_principalOpen f15 f18
  have f20 := @GlobalTheory.principalOpen_dense_complexPoints f15 f16
  have f21 := @GlobalTheory.isConnected_basicOpen_complexPoints_of_dense f19 f20
  have f22 := @GlobalTheory.thetaCone_eq_zeroLocus f3 f7 f9 f13 f10 f14 f15 f21 f20
  have f23 := @GlobalTheory.FiniteCoverGrowth.integral_and_rational_of_polynomial_growth f16 f17
  have f24 := @GlobalTheory.ThetaRational.isIntegral_and_rational_theta f3 f7 f9 f12 f13 f10 f14 f22 f15 f23
  have f25 := @GlobalTheory.finite_of_isIntegral_of_birational_of_presentation f15
  have f26 := @GlobalTheory.theta_ring_generated_in_degree_one f3 f7 f24 f25
  have f27 := @GlobalTheory.theta_projectiveNormality_even f3 f7 f26
  have f28 := @GlobalTheory.existsUnique_point_of_ringHom
  have f29 := @GlobalTheory.T.exists_projectiveModel_polarisedTorus_theta f28 f3 f7 f9 f12 f14 f22
  have f30 := @GlobalTheory.valAt'_rules
  have f31 := @GlobalTheory.eq_of_valAt'_eq f30 f28
  have f32 := @GlobalTheory.theta_quotient_regular f31
  have f33 := @GlobalTheory.holFamily_lift f30
  have f34 := @GlobalTheory.existsUnique_hom_of_locally_regular f28 f31
  have f35 := @GlobalTheory.isReduced_tensorObj_complex
  have f36 := @GlobalTheory.ThetaAddition.addition_level_two_mul f3 f7
  have f37 := @GlobalTheory.thetaModel_groupLaw f33 f31 f34 f35 f36 f3 f7 f9 f10
  have f38 := @GlobalTheory.SmoothDim.ringKrullDim_affineOpen
  have f39 := @GlobalTheory.exists_holomorphic_section_of_etale
  have f40 := @GlobalTheory.HolChart.exists_holomorphic_chart f30 f28 f39
  have f41 := @GlobalTheory.ProjModelDim.isAbelianScheme_and_dim f38 f40 f3 f7 f13
  have f42 := @GlobalTheory.exists_thetaBundle_holUnif f31 f0.1 f2 f8 f10
  have f43 := @GlobalTheory.ThetaBundleSym.rigidified_sym_section f31 f0.1 f2
  have f44 := @GlobalTheory.T.relAmple_thetaBundle_projectiveModel f31 f3
  have f45 := @GlobalTheory.exists_coord_adapted f40
  have f46 := @GlobalTheory.kTriv_of_global
  have f47 := @GlobalTheory.T.translate_trivial_eq_one_of_finiteType_points
  have f48 := @GlobalTheory.translDiff_triv_of_artin_local
  have f49 := @GlobalTheory.TangentOrigin.tangent_bijection_of_values f30
  have f50 := @GlobalTheory.T.translation_fixing_bundle_artin_point_eq_one f33 f49
  have f51 := @GlobalTheory.thetaBundle_kTriv f10 f13 f3 f7 f45 f46 f47 f48 f50
  have f52 := @GlobalTheory.appellHumbert_normal_form_of_linear_exponent
  have f53 := @GlobalTheory.ThetaPositivity.re_form_pos_of_theta_ne_zero
  have f54 := @GlobalTheory.T.exists_thetaSeries_apply_ne_zero_of_large_form
  have f55 := @GlobalTheory.exists_complementary_theta_of_linear_map f10 f8 f52 f53 f54
  have f56 := @GlobalTheory.exists_isMonHom_of_map_periodLattice f31 f34 f35 f55 f3
  exact @GlobalTheory.polarisedTorus_algebraic_of_parts f27 f29 f32 f37 f41 f42 f43 f44 f51 f56

theorem torusAlgebraic_of_sections_of_veryAmple :
    (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∀ N : ℕ, 3 ≤ N → ∀ (X
        : Over (Sp ℂ)) (ex : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ X)) (D : (Fin g → Fin
        N) → X.left.Opens), (IsIntegral X.left ∧ IsProper X.hom ∧ Function.Surjective ex ∧
        (∀ z z', ex z = ex z' ↔ z - z' ∈ periodLattice τ) ∧ (∀ (U : (X).left.Opens) (f : Γ((X).left,
        U)), IsOpen {w | w ∈ (Set.univ : Set (Fin g → ℂ)) ∧ ⊤ ≤ (ex
        w).left ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun w => valAt' (ex w).left U f) {w | w ∈ (Set.univ
        : Set (Fin g → ℂ)) ∧ ⊤ ≤ (ex w).left ⁻¹ᵁ U}) ∧ (∀ c, IsAffineOpen (D
        c) ∧ ringKrullDim Γ(X.left, D c) ≤ g ∧ (∀ z, ⊤ ≤ (ex z).left ⁻¹ᵁ D c ↔ theta (fun i => ((c i
        : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ) ≠ 0) ∧ ∃ r : (Fin g → Fin N) → Γ(X.left, D
        c), (∀ c' z, theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) •
        τ) ≠ 0 → valAt' (ex z).left (D c) (r c') = theta (fun i => ((c' i : ℕ) : ℝ) / N) 0 ((N : ℂ)
        • z) ((N : ℂ) • τ) / theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) •
        τ)) ∧ ∀ f : Γ(X.left, D c), ∃ F : MvPolynomial (Fin g → Fin
        N) ℂ, f = MvPolynomial.eval₂ (RingHom.comp (X.hom.appLE ⊤ _ le_top).hom (Scheme.ΓSpecIso
        (CommRingCat.of ℂ)).inv.hom) r F) ∧ (⨆ c, D c = ⊤)) → (∀ (d : ℕ) (p q : (Fin g →
        ℂ) → ℂ), (Differentiable ℂ p ∧ ∀ (n n' : Fin g → ℤ) z, p (z + τ *ᵥ ofIntVec n + ofIntVec
        n') = eC (-((N * d : ℕ) : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ
        z)) * p z) → (Differentiable ℂ q ∧ ∀ (n n' : Fin g → ℤ) z, q (z + τ *ᵥ ofIntVec n + ofIntVec
        n') = eC (-((N * d : ℕ) : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ
        z)) * q z) → ∃ (U : X.left.Opens) (φ : Γ(X.left, U)), ∀ z, (⊤ ≤ (ex z).left ⁻¹ᵁ U ↔ q z ≠
        0) ∧ (q z ≠ 0 → valAt' (ex z).left U φ = p z / q z)) → Even N → ∀ [GrpObj X], (∀ z w, ex (z
        +
        w) = ex z * ex w) → ∀ a b : Fin g → ℝ, (∀ i, a i = 0 ∨ a i = 1 / 2) → (∀ i, b i = 0 ∨ b i = 1 / 2) → ∀ (L
        : LB X.left) (u : HolUnif X L g), L.IsLB → (u.ex = ex ∧ (∀ z, z ∈ u.Λ ↔ z ∈ periodLattice τ)
        ∧ (∀ (n n' : Fin g → ℤ) i z, ⊤ ≤ (ex
        z).left ⁻¹ᵁ L.U i → u.fr i z = autFactor a b τ n n' z * u.fr i (z + τ *ᵥ ofIntVec n +
        ofIntVec n')) ∧ (∀ i, ∃ h F : (Fin g → ℂ) → ℂ, (Differentiable ℂ h ∧ ∀ (n n'
        : Fin g → ℤ) z, h (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ
        ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * h z) ∧ Differentiable ℂ F ∧ (∀ (n n'
        : Fin g → ℤ) z, F (z + τ *ᵥ ofIntVec n + ofIntVec n') = autFactor a b τ n n' z * eC (-(N
        : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * F z) ∧ ∀ z, (⊤ ≤ (ex
        z).left ⁻¹ᵁ L.U i ↔ h z ≠ 0 ∧ F z ≠
        0) ∧ u.fr i z = h z / F z)) → IsAbelianScheme X → SmoothOfRelativeDimension g X.hom → (∀ n : ℕ, (∀ s, ∃! θ, θ ∈ thetaLevelChar a b n τ ∧ u.IsFnPow n s θ) ∧ ∀ θ ∈ thetaLevelChar a b n τ, ∃! s, u.IsFnPow n s θ)) → (∀ (g
        : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∀ N : ℕ, 3 ≤ N → ∀ (X : Over (Sp
        ℂ)) (ex : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ X)) (D : (Fin g → Fin
        N) → X.left.Opens), (IsIntegral X.left ∧ IsProper X.hom ∧ Function.Surjective ex ∧
        (∀ z z', ex z = ex z' ↔ z - z' ∈ periodLattice τ) ∧ (∀ (U : (X).left.Opens) (f : Γ((X).left,
        U)), IsOpen {w | w ∈ (Set.univ : Set (Fin g → ℂ)) ∧ ⊤ ≤ (ex
        w).left ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun w => valAt' (ex w).left U f) {w | w ∈ (Set.univ
        : Set (Fin g → ℂ)) ∧ ⊤ ≤ (ex w).left ⁻¹ᵁ U}) ∧ (∀ c, IsAffineOpen (D
        c) ∧ ringKrullDim Γ(X.left, D c) ≤ g ∧ (∀ z, ⊤ ≤ (ex z).left ⁻¹ᵁ D c ↔ theta (fun i => ((c i
        : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ) ≠ 0) ∧ ∃ r : (Fin g → Fin N) → Γ(X.left, D
        c), (∀ c' z, theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) •
        τ) ≠ 0 → valAt' (ex z).left (D c) (r c') = theta (fun i => ((c' i : ℕ) : ℝ) / N) 0 ((N : ℂ)
        • z) ((N : ℂ) • τ) / theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) •
        τ)) ∧ ∀ f : Γ(X.left, D c), ∃ F : MvPolynomial (Fin g → Fin
        N) ℂ, f = MvPolynomial.eval₂ (RingHom.comp (X.hom.appLE ⊤ _ le_top).hom (Scheme.ΓSpecIso
        (CommRingCat.of ℂ)).inv.hom) r F) ∧ (⨆ c, D c = ⊤)) → (∀ (d : ℕ) (p q : (Fin g →
        ℂ) → ℂ), (Differentiable ℂ p ∧ ∀ (n n' : Fin g → ℤ) z, p (z + τ *ᵥ ofIntVec n + ofIntVec
        n') = eC (-((N * d : ℕ) : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ
        z)) * p z) → (Differentiable ℂ q ∧ ∀ (n n' : Fin g → ℤ) z, q (z + τ *ᵥ ofIntVec n + ofIntVec
        n') = eC (-((N * d : ℕ) : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ
        z)) * q z) → ∃ (U : X.left.Opens) (φ : Γ(X.left, U)), ∀ z, (⊤ ≤ (ex z).left ⁻¹ᵁ U ↔ q z ≠
        0) ∧ (q z ≠ 0 → valAt' (ex z).left U φ = p z / q z)) → Even N → ∀ [GrpObj X], (∀ z w, ex (z
        +
        w) = ex z * ex w) → ∀ a b : Fin g → ℝ, (∀ i, a i = 0 ∨ a i = 1 / 2) → (∀ i, b i = 0 ∨ b i = 1 / 2) → ∀ (L
        : LB X.left) (u : HolUnif X L g), L.IsLB → (u.ex = ex ∧ (∀ z, z ∈ u.Λ ↔ z ∈ periodLattice τ)
        ∧ (∀ (n n' : Fin g → ℤ) i z, ⊤ ≤ (ex
        z).left ⁻¹ᵁ L.U i → u.fr i z = autFactor a b τ n n' z * u.fr i (z + τ *ᵥ ofIntVec n +
        ofIntVec n')) ∧ (∀ i, ∃ h F : (Fin g → ℂ) → ℂ, (Differentiable ℂ h ∧ ∀ (n n'
        : Fin g → ℤ) z, h (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ
        ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * h z) ∧ Differentiable ℂ F ∧ (∀ (n n'
        : Fin g → ℤ) z, F (z + τ *ᵥ ofIntVec n + ofIntVec n') = autFactor a b τ n n' z * eC (-(N
        : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * F z) ∧ ∀ z, (⊤ ≤ (ex
        z).left ⁻¹ᵁ L.U i ↔ h z ≠ 0 ∧ F z ≠
        0) ∧ u.fr i z = h z / F z)) → IsAbelianScheme X → SmoothOfRelativeDimension g X.hom → (∀ n : ℕ, (∀ s, ∃! θ, θ ∈ thetaLevelChar a b n τ ∧ u.IsFnPow n s θ) ∧ ∀ θ ∈ thetaLevelChar a b n τ, ∃! s, u.IsFnPow n s θ) → ∀ M : ℕ, 3 ≤ M → Out.VeryAmpleAt X L M) → TorusAlgebraic := by
  intro hsec hva g τ a₀ b₀ hs hp ha₀ hb₀
  have f0 := @GlobalTheory.siegelSubDomain_and_domainOpen
  have f1 := @GlobalTheory.thetaMTest_and_thetaSummable
  have f2 := @GlobalTheory.thetaHolo_of_domainOpen_of_mTest f0.2 f1.1
  have f3 := @GlobalTheory.classicalTheta_level_and_linearIndependent f0.1 f2 f1.1
  have f4 := @GlobalTheory.fourierCoeff_unitCube_translate_of_entire_periodic
  have f5 := @GlobalTheory.entire_periodic_eq_zero_of_fourierCoeff_eq_zero f4
  have f6 := @GlobalTheory.ClassicalTheta.card_le_pow_of_linearIndependent f4 f5
  have f7 := @GlobalTheory.ThetaSpan.mem_span_theta_of_level f6 f3
  have f8 := @GlobalTheory.riemannTheta_level_one_ne_zero f3
  have f9 := @GlobalTheory.exists_level_apply_ne_zero_of_two_le f8
  have f10 := @GlobalTheory.periodLattice_isLattice_of_mem_siegelH
  have f11 := @GlobalTheory.mem_periodLattice_of_theta_translate_eq_unit_mul f8 f10
  have f12 := @GlobalTheory.ThetaSeparation.level_three_separates_points f8 f11
  have f13 := @GlobalTheory.ThetaTangent.level_three_separates_tangent_vectors f8 f11 f10
  have f14 := @GlobalTheory.thetaConeIdeal_isPrime_and_ringKrullDim_le f3 f6
  have f15 := @GlobalTheory.noetherNormalization_primitive
  have f16 := @GlobalTheory.isConnected_and_dense_compl_hypersurface
  have f17 := @GlobalTheory.exists_mvPolynomial_of_poly_bound_off_hypersurface
  have f18 := @GlobalTheory.isConnected_unramified_cover_of_irreducible f16 f17
  have f19 := @GlobalTheory.exists_isConnected_principalOpen f15 f18
  have f20 := @GlobalTheory.principalOpen_dense_complexPoints f15 f16
  have f21 := @GlobalTheory.isConnected_basicOpen_complexPoints_of_dense f19 f20
  have f22 := @GlobalTheory.thetaCone_eq_zeroLocus f3 f7 f9 f13 f10 f14 f15 f21 f20
  have f23 := @GlobalTheory.FiniteCoverGrowth.integral_and_rational_of_polynomial_growth f16 f17
  have f24 := @GlobalTheory.ThetaRational.isIntegral_and_rational_theta f3 f7 f9 f12 f13 f10 f14 f22 f15 f23
  have f25 := @GlobalTheory.finite_of_isIntegral_of_birational_of_presentation f15
  have f26 := @GlobalTheory.theta_ring_generated_in_degree_one f3 f7 f24 f25
  have f27 := @GlobalTheory.theta_projectiveNormality_even f3 f7 f26
  have f28 := @GlobalTheory.existsUnique_point_of_ringHom
  have f29 := @GlobalTheory.T.exists_projectiveModel_polarisedTorus_theta f28 f3 f7 f9 f12 f14 f22
  have f30 := @GlobalTheory.valAt'_rules
  have f31 := @GlobalTheory.eq_of_valAt'_eq f30 f28
  have f32 := @GlobalTheory.theta_quotient_regular f31
  have f33 := @GlobalTheory.holFamily_lift f30
  have f34 := @GlobalTheory.existsUnique_hom_of_locally_regular f28 f31
  have f35 := @GlobalTheory.isReduced_tensorObj_complex
  have f36 := @GlobalTheory.ThetaAddition.addition_level_two_mul f3 f7
  have f37 := @GlobalTheory.thetaModel_groupLaw f33 f31 f34 f35 f36 f3 f7 f9 f10
  have f38 := @GlobalTheory.SmoothDim.ringKrullDim_affineOpen
  have f39 := @GlobalTheory.exists_holomorphic_section_of_etale
  have f40 := @GlobalTheory.HolChart.exists_holomorphic_chart f30 f28 f39
  have f41 := @GlobalTheory.ProjModelDim.isAbelianScheme_and_dim f38 f40 f3 f7 f13
  have f42 := @GlobalTheory.exists_thetaBundle_holUnif f31 f0.1 f2 f8 f10
  have f43 := @GlobalTheory.ThetaBundleSym.rigidified_sym_section f31 f0.1 f2
  have f44 := @GlobalTheory.T.relAmple_thetaBundle_projectiveModel f31 f3
  have f45 := @GlobalTheory.exists_coord_adapted f40
  have f46 := @GlobalTheory.kTriv_of_global
  have f47 := @GlobalTheory.T.translate_trivial_eq_one_of_finiteType_points
  have f48 := @GlobalTheory.translDiff_triv_of_artin_local
  have f49 := @GlobalTheory.TangentOrigin.tangent_bijection_of_values f30
  have f50 := @GlobalTheory.T.translation_fixing_bundle_artin_point_eq_one f33 f49
  have f51 := @GlobalTheory.thetaBundle_kTriv f10 f13 f3 f7 f45 f46 f47 f48 f50
  have f52 := @GlobalTheory.appellHumbert_normal_form_of_linear_exponent
  have f53 := @GlobalTheory.ThetaPositivity.re_form_pos_of_theta_ne_zero
  have f54 := @GlobalTheory.T.exists_thetaSeries_apply_ne_zero_of_large_form
  have f55 := @GlobalTheory.exists_complementary_theta_of_linear_map f10 f8 f52 f53 f54
  have f56 := @GlobalTheory.exists_isMonHom_of_map_periodLattice f31 f34 f35 f55 f3
  have hτ : τ ∈ SiegelH (Fin g) := ⟨hs, hp⟩
  obtain ⟨a, ha, rfl⟩ := exists_ofRealVec_of_half a₀ ha₀
  obtain ⟨b, hb, rfl⟩ := exists_ofRealVec_of_half b₀ hb₀
  have ea : (fun i => (ofRealVec a i).re) = a := funext fun i => Complex.ofReal_re _
  have eb : (fun i => (ofRealVec b i).re) = b := funext fun i => Complex.ofReal_re _
  rw [ea, eb]
  obtain ⟨N, hN, hE, hgen⟩ := f27 g τ hτ
  obtain ⟨X, ex, D, hX⟩ := f29 g τ hτ N hN
  have hq := f32 g τ hτ N hN hgen X ex D hX
  obtain ⟨inst, hc, hadd⟩ := f37 g τ hτ N hN X ex D hX hq
  obtain ⟨hab, hsm⟩ := f41 g τ hτ N hN X ex D hX hq hc
  obtain ⟨L, u, hL, hu⟩ := f42 g τ hτ N hN X ex D hX hq hE hadd a b ha hb
  obtain ⟨hr, hsy, th, hth⟩ := f43 g τ hτ N hN X ex D hX hq hE hadd a b ha hb L u hL hu
  have ham := f44 g τ hτ N hN X ex D hX hq hE hadd a b ha hb L u hL hu
  have hk := f51 g τ hτ N hN X ex D hX hq hE hadd a b ha hb L u hL hu hab hsm
  have hend := f56 g τ hτ N hN X ex D hX hq hadd
  have hs' := hsec g τ hτ N hN X ex D hX hq hE hadd a b ha hb L u hL hu hab hsm
  have hv' := hva g τ hτ N hN X ex D hX hq hE hadd a b ha hb L u hL hu hab hsm hs'
  obtain ⟨hex, hΛ, -⟩ := hu
  subst hex
  have htan : (∀ v, IsTangent v → ∃! w, u.IsDiff w v) ∧ ∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v := by
    refine f49 X L g u (f45 X L g u hsm fun w hw => ?_)
    obtain ⟨-, -, -, -, -, hD, hcov⟩ := hX
    have hN1 : 1 ≤ N := by omega
    have hmem : (u.ex 0).left (default : PrimeSpectrum ℂ) ∈ ⨆ c, D c := by rw [hcov]; trivial
    obtain ⟨c, hc⟩ := TopologicalSpace.Opens.mem_iSup.1 hmem
    have hc' := (top_le_preimage_iff_mem _ _).2 hc
    obtain ⟨-, -, hDc, r, hr, -⟩ := hD c
    exact f13 g τ hτ N hN 0 w _ fun f hf => fderiv_eq_mul_of_ratio _
      (fun c => ((f3 g τ hτ N hN1).1 c).1) c 0 w ((hDc 0).1 hc')
      (fun c' z => valAt' (u.ex z).left (D c) (r c')) hr (fun c' => hw _ _ hc') f (f7 g τ hτ N hN1 f hf)
  refine ⟨{ A := X, isAb := hab, g := g, smoothDim := hsm, L := L, isLB := hL, rigid := hr, sym := hsy,
            ample := ham, ktriv := hk }, u, th, rfl, fun z => (hΛ z).trans (TorusAlg.mem_periodLattice_iff z),
    htan, ?_, hs', hv', fun F hF => ?_⟩
  · rw [thetaChar_ofRealVec_eq_theta]
    exact hth
  · exact hend F fun l hl => (hΛ _).1 (hF l ((hΛ _).2 hl))

end GlobalTheory
