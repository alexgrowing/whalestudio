import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRingHomPowPrimePow
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PfFacts
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WpPf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PerfectTensorProduct
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsPQ
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PqLift
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PerfectTensorGeneratedLift
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PqBaseChangePolynomial
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitTZpow
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EqCOfToLaurentEqInvert
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulEqZeroOfCPowMemSpan
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsConstOfRhoEq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LaurentEqToLaurentSubInvert
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmulSmulMemRange
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProdLeftEqRTensor
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFgTmulEqZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneTmulMemRangeIff
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CovOfAlgHom
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GoodBaseChange
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CancelLTensor
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrobeniusPowerSolutionLift
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PerfectFrobeniusRootSolution
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRetraction
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsKill
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DirectedSystemTrR
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SolvAtStage
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AicValOfIsColim
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorsQuot
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompletionComplete
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsComplNonZeroDivisor
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PfOfIsCompl
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsComplExistsUnique
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValThree
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ComplVal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsEvalEqProdOfNatDegreeEq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulProdCongr
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HenselPolynomialRefinement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemPowSmulTopIff
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsIsWP
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BijectiveAlgebraMapZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AltAlt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WpHomotopy
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeftCommLTensorNatural
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorPunitEqZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmulEqZeroOfLTensorSubtypeEqZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmulMemRangeLTensorOfLTensorEqZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TmulEqZeroOfMemSpan
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CofaceRel
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.IsCompl
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial
namespace CrystallineSemistableComparison.D.Leaf

theorem frob : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A], (p : A) = 0 → ∀ k : ℕ, ∃ F : A →+* A, ∀ x, F x = x ^ p ^ k := GlobalTheory.CompanionTheory.Frobenius.exists_ringHom_pow_prime_pow

theorem pf_facts : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A], Pf p A → (∃ F : A ≃+* A, ∀ x, F x = x ^ p) ∧ (∀ (x : A) (n : ℕ), x ^ n = 0 → x = 0) ∧ (∀ (k : ℕ) (x : A), ∃ y, y ^ p ^ k = x) ∧ (∀ (k : ℕ) (x y : A), x ^ p ^ k = y ^ p ^ k → x = y) ∧ ∀ r : ℕ → A, IsRt p r → (∀ k, ∃ c, r k = c * r (k + 1) * r (k + 1)) ∧ (∀ k, r k ^ p ^ k = r 0) ∧ ∀ (N : ℕ) (x : A), r 0 ^ N * x = 0 → ∀ k, r k * x = 0 := GlobalTheory.CompanionTheory.PerfectRing.pf_facts

theorem wp_pf : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A](B : Type) [CommRing B] [Algebra A B] (K : Type) [CommRing K] [Algebra A K] (n : ℕ) (ι : Fin n → (B →ₐ[A] K)), IsWP ι → Pf p A → Pf p B → Pf p K := GlobalTheory.CompanionTheory.PerfectRing.wp_pf

theorem tensor_pf : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A](B : Type) [CommRing B] [Algebra A B] (K : Type) [CommRing K] [Algebra A K], Pf p A → Pf p B → Pf p K → Pf p (B ⊗[A] K) := GlobalTheory.CompanionTheory.PerfectRing.pf_tensor

theorem pq_ex : ∀ (p : ℕ) [Fact p.Prime] (S : Type) [CommRing S] (I : Ideal S), (p : S) = 0 → ∃ (T : Type) (_ : CommRing T) (i : S →+* T), PQ p i I := GlobalTheory.CompanionTheory.PerfClos.exists_PQ

theorem pq_lift : ∀ (p : ℕ) [Fact p.Prime] (S : Type) [CommRing S] (T : Type) [CommRing T] (T₁ : Type) [CommRing T₁] (i : S →+* T) (I : Ideal S) (φ : S →+* T₁), PQ p i I → Pf p T₁ → (∀ x ∈ I, φ x = 0) → ∃! ψ : T →+* T₁, ψ.comp i = φ := GlobalTheory.CompanionTheory.PerfectRing.pq_lift

theorem pq_bc : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A](S : Type) [CommRing S] [Algebra A S] (B : Type) [CommRing B] [Algebra A B] (K : Type) [CommRing K] [Algebra A K](S₁ : Type) [CommRing S₁] (i : S →ₐ[A] B) (I : Ideal S) (κ : K →+* S₁) (j : S →+* S₁) (i₁ : S₁ →+* B ⊗[A] K), Pf p A → Pf p K → PQ p (i : S →+* B) I → κ.comp (algebraMap A K) = j.comp (algebraMap A S) → Subring.closure (Set.range κ ∪ Set.range j) = ⊤ → (∀ a, i₁ (κ a) = (1 : B) ⊗ₜ[A] a) → (∀ s, i₁ (j s) = i s ⊗ₜ[A] (1 : K)) → PQ p i₁ (I.map j) := GlobalTheory.CompanionTheory.PerfectRing.pq_baseChange

theorem bc_poly : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A](B : Type) [CommRing B] [Algebra A B] (K : Type) [CommRing K] [Algebra A K] (i : Polynomial A →ₐ[A] B) (h : Polynomial A), Pf p A → Pf p K → PQ p (i : Polynomial A →+* B) (Ideal.span {h}) → ∃ i₁ : Polynomial K →+* B ⊗[A] K, PQ p i₁ (Ideal.span {h.map (algebraMap A K)}) ∧ (∀ a, i₁ (Polynomial.C a) = (1 : B) ⊗ₜ[A] a) ∧ i₁ Polynomial.X = i Polynomial.X ⊗ₜ[A] (1 : K) := GlobalTheory.CompanionTheory.Perfection.pq_baseChange_polynomial

theorem bc_laur : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A](B : Type) [CommRing B] [Algebra A B] (K : Type) [CommRing K] [Algebra A K] (i : A[T;T⁻¹] →ₐ[A] B) (f g : A), Pf p A → Pf p K → PQ p (i : A[T;T⁻¹] →+* B) (Ideal.span {LaurentPolynomial.C f - LaurentPolynomial.T 1 * LaurentPolynomial.C g}) → ∃ i₁ : K[T;T⁻¹] →+* B ⊗[A] K, PQ p i₁ (Ideal.span {LaurentPolynomial.C (algebraMap A K f) - LaurentPolynomial.T 1 * LaurentPolynomial.C (algebraMap A K g)}) ∧ (∀ a, i₁ (LaurentPolynomial.C a) = (1 : B) ⊗ₜ[A] a) ∧ ∀ n : ℤ, i₁ (LaurentPolynomial.T n) = i (LaurentPolynomial.T n) ⊗ₜ[A] (1 : K) := GlobalTheory.CompanionTheory.PerfBC.bc_laur

theorem laur_split : ∀ (K : Type) [CommRing K] (f g : K) (α β : Polynomial K), Polynomial.toLaurent α - LaurentPolynomial.invert (Polynomial.toLaurent β) ∈ Ideal.span {(LaurentPolynomial.C f - LaurentPolynomial.T 1 * LaurentPolynomial.C g : K[T;T⁻¹])} → ∃ c : K, α - Polynomial.C c ∈ Ideal.span {Polynomial.C f - Polynomial.X * Polynomial.C g} ∧ β - Polynomial.C c ∈ Ideal.span {Polynomial.C g - Polynomial.X * Polynomial.C f} := GlobalTheory.CompanionTheory.LaurSplit.exists_const_of_mem_span

theorem b_inj : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [CommRing K] (K₁ : Type) [CommRing K₁] (K₂ : Type) [CommRing K₂] (f g : K) (i₁ : Polynomial K →+* K₁) (i₂ : Polynomial K →+* K₂) (r : ℕ → K) (N : ℕ), Pf p K → IsRt p r → r 0 ^ N ∈ Ideal.span {f, g} → PQ p i₁ (Ideal.span {Polynomial.C f - Polynomial.X * Polynomial.C g}) → PQ p i₂ (Ideal.span {Polynomial.C g - Polynomial.X * Polynomial.C f}) → ∀ a : K, i₁ (Polynomial.C a) = 0 → i₂ (Polynomial.C a) = 0 → ∀ k, r k * a = 0 := GlobalTheory.CompanionTheory.PerfectRing.b_inj

theorem b_mid : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [CommRing K] (K₁ : Type) [CommRing K₁] (K₂ : Type) [CommRing K₂] (K₃ : Type) [CommRing K₃] (f g : K) (i₁ : Polynomial K →+* K₁) (i₂ : Polynomial K →+* K₂) (i₃ : K[T;T⁻¹] →+* K₃) (ρ₁ : K₁ →+* K₃) (ρ₂ : K₂ →+* K₃), Pf p K → PQ p i₁ (Ideal.span {Polynomial.C f - Polynomial.X * Polynomial.C g}) → PQ p i₂ (Ideal.span {Polynomial.C g - Polynomial.X * Polynomial.C f}) → PQ p i₃ (Ideal.span {LaurentPolynomial.C f - LaurentPolynomial.T 1 * LaurentPolynomial.C g}) → (∀ α, ρ₁ (i₁ α) = i₃ (Polynomial.toLaurent α)) → (∀ β, ρ₂ (i₂ β) = i₃ (LaurentPolynomial.invert (Polynomial.toLaurent β))) → ∀ (b₁ : K₁) (b₂ : K₂), ρ₁ b₁ = ρ₂ b₂ → ∃ a : K, i₁ (Polynomial.C a) = b₁ ∧ i₂ (Polynomial.C a) = b₂ := GlobalTheory.CompanionTheory.BMid.exists_const_of_rho_eq

theorem b_surj : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [CommRing K] (K₁ : Type) [CommRing K₁] (K₂ : Type) [CommRing K₂] (K₃ : Type) [CommRing K₃] (f g : K) (i₁ : Polynomial K →+* K₁) (i₂ : Polynomial K →+* K₂) (i₃ : K[T;T⁻¹] →+* K₃) (ρ₁ : K₁ →+* K₃) (ρ₂ : K₂ →+* K₃), Pf p K → PQ p i₁ (Ideal.span {Polynomial.C f - Polynomial.X * Polynomial.C g}) → PQ p i₂ (Ideal.span {Polynomial.C g - Polynomial.X * Polynomial.C f}) → PQ p i₃ (Ideal.span {LaurentPolynomial.C f - LaurentPolynomial.T 1 * LaurentPolynomial.C g}) → (∀ α, ρ₁ (i₁ α) = i₃ (Polynomial.toLaurent α)) → (∀ β, ρ₂ (i₂ β) = i₃ (LaurentPolynomial.invert (Polynomial.toLaurent β))) → ∀ y : K₃, ∃ (b₁ : K₁) (b₂ : K₂), y = ρ₁ b₁ - ρ₂ b₂ := GlobalTheory.CompanionTheory.PerfectRing.b_surj

theorem mv_cov : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A](B : Type) [CommRing B] [Algebra A B] (D : Type) [CommRing D] [Algebra A D] (r : ℕ → A) (ρ : B →ₗ[A] D), IsRt p r → Pf p D → Function.Surjective ρ → ρ 1 = 0 → (∀ (K : Type) [CommRing K] [Algebra A K], Pf p K → (∀ a : K, ((1 : B) ⊗ₜ[A] a) = 0 → ∀ k, r k • a = 0) ∧ ∀ w : B ⊗[A] K, ρ.rTensor K w = 0 → ∃ a : K, w = (1 : B) ⊗ₜ[A] a) → Cov p r B := GlobalTheory.CompanionTheory.SnakeCov.mv_cov

theorem mv_prod : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A](B₁ : Type) [CommRing B₁] [Algebra A B₁] (B₂ : Type) [CommRing B₂] [Algebra A B₂] (D : Type) [CommRing D] [Algebra A D] (r : ℕ → A) (ρ₁ : B₁ →ₐ[A] D) (ρ₂ : B₂ →ₐ[A] D), IsRt p r → Pf p D → (∀ y, ∃ b₁ b₂, y = ρ₁ b₁ - ρ₂ b₂) → (∀ (K : Type) [CommRing K] [Algebra A K], Pf p K → (∀ a : K, ((1 : B₁) ⊗ₜ[A] a) = 0 → ((1 : B₂) ⊗ₜ[A] a) = 0 → ∀ k, r k • a = 0) ∧ ∀ (w₁ : B₁ ⊗[A] K) (w₂ : B₂ ⊗[A] K), Algebra.TensorProduct.map ρ₁ (AlgHom.id A K) w₁ = Algebra.TensorProduct.map ρ₂ (AlgHom.id A K) w₂ → ∃ a : K, w₁ = (1 : B₁) ⊗ₜ[A] a ∧ w₂ = (1 : B₂) ⊗ₜ[A] a) → Cov p r (B₁ × B₂) := GlobalTheory.CompanionTheory.SnakeCov.mv_prod

theorem eq_crit : ∀ (A : Type) [CommRing A](B : Type) [CommRing B] [Algebra A B] (Q : Type) [AddCommGroup Q] [Module A Q] (z : Q), ((1 : B) ⊗ₜ[A] z) = 0 → ∃ (m n : ℕ) (a : Fin m → Fin n → A) (c : Fin m → A), Solv B a c ∧ ∀ (B₁ : Type) [CommRing B₁] [Algebra A B₁], Solv B₁ a c → ((1 : B₁) ⊗ₜ[A] z) = 0 := fun A _ B _ _ Q _ _ z h => GlobalTheory.CompanionTheory.EqCrit.exists_system B z h

theorem cov_cmp : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A](B : Type) [CommRing B] [Algebra A B] (r : ℕ → A), (∀ (m n : ℕ) (a : Fin m → Fin n → A) (c : Fin m → A), Solv B a c → ∃ (B₁ : Type) (_ : CommRing B₁) (_ : Algebra A B₁), Cov p r B₁ ∧ Solv B₁ a c) → Cov p r B := GlobalTheory.CompanionTheory.CovCmp.cov_of_solv

theorem cov_mono : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] (r : ℕ → A), Cov p r A ∧ ∀ (B : Type) [CommRing B] [Algebra A B] (B₁ : Type) [CommRing B₁] [Algebra A B₁] (φ : B →ₐ[A] B₁), Cov p r B₁ → Cov p r B := GlobalTheory.CompanionTheory.CovMono.cov_mono

theorem good_bc : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A](B : Type) [CommRing B] [Algebra A B] (r : ℕ → A) (K₁ K₀ : Type) [AddCommGroup K₁] [Module A K₁] [AddCommGroup K₀] [Module A K₀] (d : K₁ →ₗ[A] K₀), Good p r d → Good p (fun k => algebraMap A B (r k)) (d.baseChange B) := GlobalTheory.CompanionTheory.GoodBaseChange.good_baseChange

theorem cov_comp : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A](B : Type) [CommRing B] [Algebra A B](B₁ : Type) [CommRing B₁] [Algebra A B₁] [Algebra B B₁] [IsScalarTower A B B₁] (r : ℕ → A), Pf p A → Pf p B → IsRt p r → Cov p r B → Cov p (fun k => algebraMap A B (r k)) B₁ → Cov p r B₁ := GlobalTheory.CompanionTheory.CovComp.cov_comp

theorem solv_pow : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A](S : Type) [CommRing S] [Algebra A S] (B : Type) [CommRing B] [Algebra A B] (i : S →ₐ[A] B) (I : Ideal S) (m n : ℕ) (a : Fin m → Fin n → A) (c : Fin m → A), (p : A) = 0 → PQ p (i : S →+* B) I → Solv B a c → ∃ (k : ℕ) (s : Fin n → S), ∀ t, ∑ j, a t j ^ p ^ k • s j - algebraMap A S (c t ^ p ^ k) ∈ I := GlobalTheory.CompanionTheory.PerfectQuotient.solv_pow

theorem solv_root : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A](B : Type) [CommRing B] [Algebra A B] (m n k : ℕ) (a : Fin m → Fin n → A) (c : Fin m → A), Pf p B → Solv B (fun t j => a t j ^ p ^ k) (fun t => c t ^ p ^ k) → Solv B a c := GlobalTheory.CompanionTheory.PerfectRing.solv_of_solv_pow

theorem cov_root : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] (r : ℕ → A) (P : Polynomial A), Pf p A → P.Monic → 0 < P.natDegree → ∃ (B : Type) (_ : CommRing B) (_ : Algebra A B), Pf p B ∧ Cov p r B ∧ ∃ x : B, Polynomial.aeval x P = 0 := GlobalTheory.CompanionTheory.CovRoot.cov_root

theorem big_step : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] (r : ℕ → A) (𝓔 : Set (Set (MvPolynomial (Fin 3) A))), Pf p A → (∀ J : Set (Set (MvPolynomial (Fin 3) A)), J.Finite → J ⊆ 𝓔 → ∃ (B : Type) (_ : CommRing B) (_ : Algebra A B), Pf p B ∧ Cov p r B ∧ ∀ E ∈ J, Pt (algebraMap A B) E) → ∃ (B : Type) (_ : CommRing B) (_ : Algebra A B), Pf p B ∧ Cov p r B ∧ (∀ E ∈ 𝓔, Pt (algebraMap A B) E) ∧ ∀ (T : Type) [CommRing T] (x : A →+* T), Pf p T → (∀ E ∈ 𝓔, Pt x E) → ∃ y : B →+* T, y.comp (algebraMap A B) = x := GlobalTheory.CompanionTheory.BigStep.big_step

theorem colim_ex : ∀ (A : Type) [CommRing A](G : ℕ → Type) [∀ n, CommRing (G n)] [∀ n, Algebra A (G n)] (f : ∀ n, G n →ₐ[A] G (n + 1)), ∃ (L : Type) (_ : CommRing L) (_ : Algebra A L), ∃ ι : ∀ n, G n →ₐ[A] L, IsColim f ι := GlobalTheory.CompanionTheory.ColimEx.exists_isColim

theorem colim_pf : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A](G : ℕ → Type) [∀ n, CommRing (G n)] [∀ n, Algebra A (G n)] (f : ∀ n, G n →ₐ[A] G (n + 1))(L : Type) [CommRing L] [Algebra A L] (ι : ∀ n, G n →ₐ[A] L), IsColim f ι → ((∀ n, Pf p (G n)) → Pf p L) ∧ ∀ (m n : ℕ) (a : Fin m → Fin n → A) (c : Fin m → A), Solv L a c → ∃ N, Solv (G N) a c := GlobalTheory.CompanionTheory.colim_pf

theorem colim_test : ∀ (A : Type) [CommRing A] (π : A) (G : ℕ → Type) [∀ n, CommRing (G n)] [∀ n, Algebra A (G n)] (f : ∀ n, G n →ₐ[A] G (n + 1))(L : Type) [CommRing L] [Algebra A L] (ι : ∀ n, G n →ₐ[A] L), IsColim f ι → (∀ n, AICm (f n : G n →+* G (n + 1))) → (∀ n, VALm (algebraMap A (G n) π) (f n : G n →+* G (n + 1))) → AIC L ∧ VAL (algebraMap A L π) := GlobalTheory.CompanionTheory.Colim.aic_val_of_isColim

theorem tors_quot : ∀ (p : ℕ) [Fact p.Prime] (B : Type) [CommRing B] (π : B), Pf p B → ∃ (B₁ : Type) (_ : CommRing B₁) (q : B →+* B₁), Function.Surjective q ∧ Pf p B₁ ∧ q π ∈ nonZeroDivisors B₁ ∧ (∀ x, q x = 0 ↔ π * x = 0) ∧ (AIC B → AIC B₁) ∧ (VAL π → VAL (q π)) := GlobalTheory.CompanionTheory.PerfectRing.tors_quot

theorem compl_ex : ∀ (B : Type) [CommRing B] (π : B), ∃ (T : Type) (_ : CommRing T) (g : B →+* T), IsCompl π g := GlobalTheory.CompanionTheory.AdicCompl.exists_isCompl

theorem compl_reg : ∀ (B : Type) [CommRing B] (T : Type) [CommRing T] (π : B) (g : B →+* T), IsCompl π g → π ∈ nonZeroDivisors B → g π ∈ nonZeroDivisors T := GlobalTheory.CompanionTheory.ComplReg.isCompl_nonZeroDivisor

theorem compl_pf : ∀ (p : ℕ) [Fact p.Prime] (B : Type) [CommRing B] (T : Type) [CommRing T] (π : B) (g : B →+* T), IsCompl π g → Pf p B → Pf p T := GlobalTheory.CompanionTheory.PerfectRing.pf_of_isCompl

theorem compl_univ : ∀ (B : Type) [CommRing B] (T : Type) [CommRing T] (π : B) (g : B →+* T), IsCompl π g → ∀ (T₁ : Type) [CommRing T₁] (x : B →+* T₁), IsAdicComplete (Ideal.span {x π}) T₁ → ∃! ψ : T →+* T₁, ψ.comp g = x := GlobalTheory.CompanionTheory.PfCompl.isCompl_existsUnique

theorem val_three : ∀ (B : Type) [CommRing B] (π : B), VAL π → ∀ (f g : B) (M : ℕ), ∃ e₁ e₂ e : B, IsIdempotentElem e₁ ∧ IsIdempotentElem e₂ ∧ IsIdempotentElem e ∧ e₁ * f ∈ Ideal.span {π ^ M} ∧ (1 - e₁) * π ^ M ∈ Ideal.span {f} ∧ e₂ * g ∈ Ideal.span {π ^ M} ∧ (1 - e₂) * π ^ M ∈ Ideal.span {g} ∧ (1 - e₁) * (1 - e₂) * e * f ∈ Ideal.span {g} ∧ (1 - e₁) * (1 - e₂) * (1 - e) * g ∈ Ideal.span {f} := GlobalTheory.CompanionTheory.ValThree.val_three

theorem compl_val : ∀ (B : Type) [CommRing B] (T : Type) [CommRing T] (π : B) (g : B →+* T), IsCompl π g → VAL π → VAL (g π) := GlobalTheory.CompanionTheory.ComplVal.compl_val

theorem aic_split : ∀ (B : Type) [CommRing B], AIC B → ∀ P : Polynomial B, P.Monic → ∃ b : Fin P.natDegree → B, ∀ a : B, P.eval a = ∏ j, (a - b j) := GlobalTheory.CompanionTheory.AicSplit.exists_eval_eq_prod

theorem root_near : ∀ (B : Type) [CommRing B] (π : B), π ∈ nonZeroDivisors B → VAL π → ∀ (d M : ℕ) (b : Fin d → B) (a : B), 0 < d → ∏ j, (a - b j) ∈ Ideal.span {π ^ (d * M)} → ∃ a₁ : B, a₁ - a ∈ Ideal.span {π ^ M} ∧ ∏ j, (a₁ - b j) = 0 := GlobalTheory.CompanionTheory.RootNear.root_near

theorem aic_step : ∀ (B : Type) [CommRing B] (T : Type) [CommRing T] (π : B) (g : B →+* T), IsCompl π g → π ∈ nonZeroDivisors B → AIC B → VAL π → ∀ P : Polynomial T, P.Monic → 0 < P.natDegree → ∀ (M : ℕ) (a : B), P.eval (g a) ∈ Ideal.span {g π ^ (P.natDegree * M)} → ∃ a₁ : B, a₁ - a ∈ Ideal.span {π ^ M} ∧ P.eval (g a₁) ∈ Ideal.span {g π ^ (P.natDegree * (M + 1))} := GlobalTheory.CompanionTheory.AicStep.aic_step

theorem compl_aic : ∀ (B : Type) [CommRing B] (T : Type) [CommRing T] (π : B) (g : B →+* T), IsCompl π g → π ∈ nonZeroDivisors B → AIC B → VAL π → AIC T := GlobalTheory.CompanionTheory.Completion.aic_of_isCompl

theorem wp_ex : ∀ (A : Type) [CommRing A](B : Type) [CommRing B] [Algebra A B] (n : ℕ), ∃ (K : Type) (_ : CommRing K) (_ : Algebra A K) (ι : Fin n → (B →ₐ[A] K)), IsWP ι := GlobalTheory.CompanionTheory.AlgCoproduct.exists_isWP

theorem wp_cof : ∀ (A : Type) [CommRing A](B : Type) [CommRing B] [Algebra A B] (K : ℕ → Type) [∀ n, CommRing (K n)] [∀ n, Algebra A (K n)] (ι : ∀ n, Fin n → (B →ₐ[A] K n)), (∀ n, IsWP (ι n)) → Function.Bijective (algebraMap A (K 0)) ∧ Function.Bijective (ι 1 0) ∧ ∃ δ : ∀ n, Fin (n + 1) → (K n →ₐ[A] K (n + 1)), ∀ n k i, (δ n k).comp (ι n i) = ι (n + 1) (k.succAbove i) := GlobalTheory.CompanionTheory.Coproduct.coproduct_low_and_coface

theorem wp_dd : ∀ (A : Type) [CommRing A](B : Type) [CommRing B] [Algebra A B] (K : ℕ → Type) [∀ n, CommRing (K n)] [∀ n, Algebra A (K n)] (ι : ∀ n, Fin n → (B →ₐ[A] K n)) (δ : ∀ n, Fin (n + 1) → (K n →ₐ[A] K (n + 1))), (∀ n, IsWP (ι n)) → (∀ n k i, (δ n k).comp (ι n i) = ι (n + 1) (k.succAbove i)) → ∀ n z, alt (δ (n + 1)) (alt (δ n) z) = 0 := GlobalTheory.CompanionTheory.WpCoface.alt_alt

theorem wp_htpy : ∀ (A : Type) [CommRing A](B : Type) [CommRing B] [Algebra A B] (K : ℕ → Type) [∀ n, CommRing (K n)] [∀ n, Algebra A (K n)] (ι : ∀ n, Fin n → (B →ₐ[A] K n)) (δ : ∀ n, Fin (n + 1) → (K n →ₐ[A] K (n + 1))), (∀ n, IsWP (ι n)) → (∀ n k i, (δ n k).comp (ι n i) = ι (n + 1) (k.succAbove i)) → ∃ H : ∀ n, K (n + 1) →ₗ[A] B ⊗[A] K n, (∀ z, H 0 (alt (δ 0) z) = (1 : B) ⊗ₜ[A] z) ∧ ∀ n z, (alt (δ n)).lTensor B (H n z) + H (n + 1) (alt (δ (n + 1)) z) = (1 : B) ⊗ₜ[A] z := GlobalTheory.CompanionTheory.WpHomotopy.wp_homotopy

theorem ami_bc : ∀ (A : Type) [CommRing A](B : Type) [CommRing B] [Algebra A B] (C : Type) [AddCommGroup C] [Module A C] (K : ℕ → Type) [∀ n, AddCommGroup (K n)] [∀ n, Module A (K n)] (d : ∀ n, K n →ₗ[A] K (n + 1)) (H : ∀ n, K (n + 1) →ₗ[A] B ⊗[A] K n), ((∀ z, H 0 (d 0 z) = (1 : B) ⊗ₜ[A] z) ∧ ∀ n z, (d n).lTensor B (H n z) + H (n + 1) (d (n + 1) z) = (1 : B) ⊗ₜ[A] z) → ∃ H₁ : ∀ n, C ⊗[A] K (n + 1) →ₗ[A] B ⊗[A] (C ⊗[A] K n), (∀ z, H₁ 0 ((d 0).lTensor C z) = (1 : B) ⊗ₜ[A] z) ∧ ∀ n z, ((d n).lTensor C).lTensor B (H₁ n z) + H₁ (n + 1) ((d (n + 1)).lTensor C z) = (1 : B) ⊗ₜ[A] z := GlobalTheory.CompanionTheory.Dblock.AmiBc.contraction_lTensor

theorem ami_exact : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A](B : Type) [CommRing B] [Algebra A B] (r : ℕ → A), Pf p A → Cov p r B → ∀ (K : ℕ → Type) [∀ n, CommRing (K n)] [∀ n, Algebra A (K n)] (d : ∀ n, K n →ₗ[A] K (n + 1)) (H : ∀ n, K (n + 1) →ₗ[A] B ⊗[A] K n), (∀ n, Pf p (K n)) → (∀ n z, d (n + 1) (d n z) = 0) → ((∀ z, H 0 (d 0 z) = (1 : B) ⊗ₜ[A] z) ∧ ∀ n z, (d n).lTensor B (H n z) + H (n + 1) (d (n + 1) z) = (1 : B) ⊗ₜ[A] z) → (∀ z, d 0 z = 0 → ∀ k, r k • z = 0) ∧ ∀ n z, d (n + 1) z = 0 → ∀ k, r k • z ∈ LinearMap.range (d n) := GlobalTheory.CompanionTheory.Dblock.AmiExact.exact_of_contraction

theorem tens_inj : ∀ (R : Type) [CommRing R] [IsDomain R] [ValuationRing R] (r : ℕ → R) (N : Type) [AddCommGroup N] [Module R N] (K : Type) [AddCommGroup K] [Module R K] (I : Submodule R K), (∀ (a : R) (x : K), a ≠ 0 → a • x ∈ I → ∀ k, r k • x ∈ I) → ∀ w : N ⊗[R] I, I.subtype.lTensor N w = 0 → ∀ k, r k • w = 0 := GlobalTheory.CompanionTheory.Dblock.smul_eq_zero_of_lTensor_subtype_eq_zero

theorem tens_exact : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [IsDomain R] [ValuationRing R] (r : ℕ → R) (N : Type) [AddCommGroup N] [Module R N] (K₀ : Type) [AddCommGroup K₀] [Module R K₀] (K₁ : Type) [AddCommGroup K₁] [Module R K₁] (K₂ : Type) [AddCommGroup K₂] [Module R K₂] (K₃ : Type) [AddCommGroup K₃] [Module R K₃] (d₀ : K₀ →ₗ[R] K₁) (d₁ : K₁ →ₗ[R] K₂) (d₂ : K₂ →ₗ[R] K₃), IsRt p r → (∀ z, d₂ (d₁ z) = 0) → (∀ z, d₁ z = 0 → ∀ k, r k • z ∈ LinearMap.range d₀) → (∀ z, d₂ z = 0 → ∀ k, r k • z ∈ LinearMap.range d₁) → (∀ (a : R) (x : K₃), a ≠ 0 → a • x = 0 → ∀ k, r k • x = 0) → ∀ w : N ⊗[R] K₁, d₁.lTensor N w = 0 → ∀ k, r k • w ∈ LinearMap.range (d₀.lTensor N) := GlobalTheory.CompanionTheory.Dblock.smul_mem_range_lTensor_of_lTensor_eq_zero

theorem tens_compl : ∀ (R : Type) [CommRing R] (r : ℕ → R) (M : ℕ) (N : Type) [AddCommGroup N] [Module R N](B : Type) [CommRing B] [Algebra R B] (T : Type) [CommRing T] [Algebra R T] (g : B →ₐ[R] T), (∀ x : N, r 0 ^ M • x = 0) → (∀ y : T, ∃ x, y - g x ∈ Ideal.span {algebraMap R T (r 0) ^ M}) → (∀ x : B, g x ∈ Ideal.span {algebraMap R T (r 0) ^ M} → ∀ k, r k • x ∈ Ideal.span {algebraMap R B (r 0) ^ M}) → Function.Surjective (g.toLinearMap.lTensor N) ∧ ∀ w : N ⊗[R] B, g.toLinearMap.lTensor N w = 0 → ∀ k, r k • w = 0 := GlobalTheory.CompanionTheory.TensCompl.main

theorem wp_rel : ∀ (A : Type) [CommRing A](B : Type) [CommRing B] [Algebra A B] (K : ℕ → Type) [∀ n, CommRing (K n)] [∀ n, Algebra A (K n)] (ι : ∀ n, Fin n → (B →ₐ[A] K n)) (δ : ∀ n, Fin (n + 1) → (K n →ₐ[A] K (n + 1))), (∀ n, IsWP (ι n)) → (∀ n k i, (δ n k).comp (ι n i) = ι (n + 1) (k.succAbove i)) → ∀ (n : ℕ) (k : Fin (n + 2)) (i : Fin (n + 1)), (δ (n + 1) (k.succAbove i)).comp (δ n (i.predAbove k)) = (δ (n + 1) k).comp (δ n i) := GlobalTheory.CompanionTheory.WpCoface.coface_rel

end CrystallineSemistableComparison.D.Leaf
