import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PerfectoidXiNonZeroDivisorStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SharpSurjectiveKerSpanStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UntiltAdicCompleteStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SharpMapCongruencePropertiesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompatibleRootsLiftToTiltStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TiltSequenceDeterminedBySharpStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CrystallineFiltrationMultiplicativeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CrystallineGradedPiecesDescriptionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CrystallineFiltrationSaturatedStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFiltrationGeneratedByDividedXiStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuotientMapsSurjectiveWithKernelsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PrimePowAnnihilatorReductionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExpansionSurjectiveAdditiveLinearStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExpansionEqZeroIffCoeffsMemStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FunctorialityOfPeriodRingMapsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiltrationDividedPowerStructuresStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsDividedPowersOnReductionsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsThetaKernelEqFiltrationOneStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralRingAdicCompletePrimeRegularStatement
import GroundTheory.PAdicHodge.TiltAlgClosed
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PeriodRingComparisonOfBaseStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorLiftKernelModPrimeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorLiftSurjectiveKernelLevelStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsPrimeRootValuationQuotientStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUniqueIdempotentLiftTiltStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsUnitOfIsUnitSharpStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemFixedIffIdempotentSum
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdempotentSumInjective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdempotentsOfPrimePowerRootOfUnityStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousFunctionsPerfectAdicRingStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistFrobeniusFiltrationCompatStatement
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GaloisTwistIdentitySection
set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

theorem CrystallineSemistableComparison.RL.u_tf : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l), (l : A.U) ∈ nonZeroDivisors A.U ∧ A.xi ∈ nonZeroDivisors A.W ∧ ∀ (n : ℕ) (x : A.W), A.xi * x ∈ Ideal.span {(l : A.W) ^ n} → x ∈ Ideal.span {(l : A.W) ^ n} := GlobalTheory.T.perfectoid_xi_nonZeroDivisor

theorem CrystallineSemistableComparison.RL.u_mod : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l), Function.Surjective A.aToU1 ∧ RingHom.ker A.aToU1 = Ideal.span {A.pi} := GlobalTheory.T.sharp_surjective_ker_span

theorem CrystallineSemistableComparison.RL.u_complete : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l), IsAdicComplete (Ideal.span {(l : A.U)}) A.U := GlobalTheory.T.untilt_adic_complete

theorem CrystallineSemistableComparison.RL.sharp_cong : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l), (∀ (a b : A.A) (n : ℕ), a - b ∈ Ideal.span {A.pi} → A.sharp (a ^ l ^ n) - A.sharp (b ^ l ^ n) ∈ Ideal.span {(l : A.U) ^ (n + 1)}) ∧ (∀ a b : A.A, A.sharp a - A.sharp b ∈ Ideal.span {(l : A.U)} ↔ a - b ∈ Ideal.span {A.pi}) ∧ ∀ e : A.A, IsIdempotentElem e → A.sharp (1 - e) = 1 - A.sharp e := GlobalTheory.T.sharp_map_congruence_properties

theorem CrystallineSemistableComparison.RL.tilt_ex : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (u : ℕ → A.U), (∀ i, u (i + 1) ^ l = u i) → ∃ a : ℕ → A.A, (∀ i, a (i + 1) ^ l = a i) ∧ ∀ i, A.sharp (a i) = u i := GlobalTheory.T.compatible_roots_lift_to_tilt

theorem CrystallineSemistableComparison.RL.tilt_inj : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (a b : ℕ → A.A), (∀ i, a (i + 1) ^ l = a i) → (∀ i, b (i + 1) ^ l = b i) → (∀ i, A.sharp (a i) = A.sharp (b i)) → a = b := GlobalTheory.T.tilt_sequence_determined_by_sharp

theorem CrystallineSemistableComparison.RL.filtration_multiplicative : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l), A.Fil0 0 = ⊤ ∧ (∀ i j, A.dxi0 i * A.dxi0 j = ((i + j).choose i : A.Acr0) * A.dxi0 (i + j)) ∧ (∀ k, (k.factorial : A.Acr0) * A.dxi0 k = algebraMap A.W A.Acr0 A.xi ^ k) ∧ (∀ r s, A.Fil0 r * A.Fil0 s ≤ A.Fil0 (r + s)) ∧ (∀ n r, A.Fil n r = (A.Fil0 r).map (A.mkAcr n)) ∧ (∀ n, A.PFil n = A.PFil0.map (A.mkAcr n)) ∧ (∀ n, A.Fil n 0 = ⊤) ∧ ∀ n r s, A.Fil n r * A.Fil n s ≤ A.Fil n (r + s) := GlobalTheory.T.crystalline_filtration_multiplicative

theorem CrystallineSemistableComparison.RL.gr : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (n r : ℕ), (∀ z ∈ A.Fil n r, ∃ w : A.W, z - A.toAcr n w * A.dxi n r ∈ A.Fil n (r + 1)) ∧ ∀ w : A.W, A.toAcr n w * A.dxi n r ∈ A.Fil n (r + 1) ↔ A.th w ∈ Ideal.span {(l : A.U) ^ n} := GlobalTheory.T.graded_filtration_generated_by_dividedXi

theorem CrystallineSemistableComparison.RL.uToQ : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (n : ℕ), Function.Surjective (A.uToQ n) ∧ RingHom.ker (A.uToQ n) = Ideal.span {(l : A.U) ^ n} ∧ Function.Surjective (A.uToPQ n) ∧ (n ≠ 0 → RingHom.ker (A.uToPQ n) = Ideal.span {(l : A.U)}) := GlobalTheory.T.quotient_maps_surjective_with_kernels

theorem CrystallineSemistableComparison.RL.expand_nat : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (B : PAlg l) (f : A ⟶ B), (∀ a, mapAcr f 1 (A.aTo1 a) = B.aTo1 (Hom.f f a)) ∧ (∀ c : ℕ →₀ A.A, mapAcr f 1 (A.expand c) = B.expand (c.mapRange (Hom.f f) (map_zero _))) ∧ (∀ a, mapU f (A.sharp a) = B.sharp (Hom.f f a)) ∧ (∀ a, mapUn f 1 (A.aToU1 a) = B.aToU1 (Hom.f f a)) ∧ (∀ n x, Ideal.Quotient.mk (B.Fil n 1) (mapAcr f n (A.toAcr n x)) = B.uToQ n (mapU f (A.th x))) ∧ ∀ x : Ainf l, algebraMap (Ainf l) (A.Acr 1) x = A.aTo1 (A.s (x.coeff 0)) := GlobalTheory.T.functoriality_of_period_ring_maps

theorem CrystallineSemistableComparison.RL.pdi : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l), R.PdI (A.Fil0 1) ∧ R.PdI A.PFil0 ∧ ∀ x ∈ A.Fil0 1, ∀ (k : ℕ) (y : A.Acr0), (k.factorial : A.Acr0) * y = x ^ k → y ∈ A.Fil0 k := GlobalTheory.T.filtration_divided_power_structures

theorem CrystallineSemistableComparison.RL.pd_ex : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (n : ℕ), (∃ δ : DividedPowers (A.Fil n 1), R.IsPd (A.mkAcr n) (A.Fil0 1) δ) ∧ ∃ δ : DividedPowers (A.PFil n), R.IsPd (A.mkAcr n) A.PFil0 δ := GlobalTheory.T.exists_divided_powers_on_reductions

theorem CrystallineSemistableComparison.RL.theta_ex : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (n : ℕ), ∃ θ : A.Acr n →+* A.Un n, (∀ x : A.W, θ (A.toAcr n x) = Ideal.Quotient.mk _ (A.th x)) ∧ RingHom.ker θ = A.Fil n 1 := GlobalTheory.T.exists_theta_kernel_eq_filtration_one

theorem CrystallineSemistableComparison.RL.base_ex : ∀ {l : ℕ} [Fact l.Prime], IsAdicComplete (Ideal.span {pFlat l}) (Ob l) ∧ pFlat l ∈ nonZeroDivisors (Ob l) := GlobalTheory.T.integral_ring_adic_complete_prime_regular

theorem CrystallineSemistableComparison.RL.base_acr : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l), IsBase l A → (Function.Bijective A.cris0 ∧ Function.Bijective A.oC) ∧ ∀ n, Function.Surjective (A.cris n) ∧ RingHom.ker (A.cris n) = Ideal.span {(l : Acris l) ^ n} := GlobalTheory.T.period_ring_comparison_of_base

theorem CrystallineSemistableComparison.RL.tens : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (n : ℕ), Function.Surjective (Algebra.TensorProduct.lift (IsScalarTower.toAlgHom (Ainf l) (Acris l) (A.Acr n)) (IsScalarTower.toAlgHom (Ainf l) A.W (A.Acr n)) (fun _ _ => Commute.all _ _)) ∧ ∀ z : TensorProduct (Ainf l) (Acris l) A.W, Algebra.TensorProduct.lift (IsScalarTower.toAlgHom (Ainf l) (Acris l) (A.Acr n)) (IsScalarTower.toAlgHom (Ainf l) A.W (A.Acr n)) (fun _ _ => Commute.all _ _) z = 0 ↔ z ∈ Ideal.span {(l : TensorProduct (Ainf l) (Acris l) A.W) ^ n} := GlobalTheory.T.tensor_lift_surjective_kernel_level

theorem CrystallineSemistableComparison.RL.untilt_valuation_mod_square : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l), A.IsTest → ∃ ϖ : A.U, ϖ ^ l = (l : A.U) ∧ R.Val0 (A.U ⧸ Ideal.span {ϖ ^ 2}) ∧ R.Aic (A.U ⧸ Ideal.span {ϖ ^ 2}) := GlobalTheory.T.exists_prime_root_valuation_quotient

theorem CrystallineSemistableComparison.RL.idem_au : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (e : A.U), IsIdempotentElem e → ∃! e₀ : A.A, IsIdempotentElem e₀ ∧ A.sharp e₀ = e := GlobalTheory.T.existsUnique_idempotent_lift_tilt

theorem CrystallineSemistableComparison.RL.unit_lift : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (a : A.A), IsUnit (A.sharp a) → IsUnit a := GlobalTheory.T.isUnit_of_isUnit_sharp'

theorem CrystallineSemistableComparison.RL.mu_lc : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l), R.Val (l : A.U) → ∀ (n : ℕ) (ζ : OC l), IsPrimitiveRoot ζ (l ^ n) → ∀ z : A.U, z ^ l ^ n = 1 → ∃ e : ZMod (l ^ n) → A.A, (haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩; CompleteOrthogonalIdempotents e) ∧ ∀ c, A.sharp (e c) * (z - A.oC ζ ^ c.val) = 0 := GlobalTheory.T.idempotents_of_prime_power_root_of_unity

theorem CrystallineSemistableComparison.RL.cont_ex : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (Γ : Type) [TopologicalSpace Γ], PerfectRing (A.contR Γ) l ∧ IsAdicComplete (Ideal.span {A.contC Γ A.pi}) (A.contR Γ) ∧ A.contC Γ A.pi ∈ nonZeroDivisors (A.contR Γ) ∧ ∀ (k : ℕ) (f : A.contR Γ), f ∈ Ideal.span {A.contC Γ A.pi ^ k} ↔ ∀ γ, f.1 γ ∈ Ideal.span {A.pi ^ k} := GlobalTheory.T.continuous_functions_perfect_adic_ring

theorem CrystallineSemistableComparison.RL.tw_fil : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (σ : Gal(PadicAlgCl l/K)), (∀ x ∈ (tw σ A).Fil0 1, (pdOk_twId σ A).acr0 x ∈ A.Fil0 1) ∧ (∀ x ∈ A.PFil0, A.pdOk_frob.acr0 x ∈ Ideal.span {(l : A.Acr0)}) ∧ (∀ n r, ∀ x ∈ (tw σ A).Fil n r, twAcr σ A n x ∈ A.Fil n r) ∧ (∀ n, Function.Bijective (twAcr σ A n)) ∧ ∀ n x, twAcr σ A n ((tw σ A).phi n x) = A.phi n (twAcr σ A n x) := GlobalTheory.T.twist_frobenius_filtration_compat
