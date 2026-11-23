import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.FacDefs
import Development.AutomorphicArithmetic.WhittakerHecke.HeightOneSpectrumRatCorrespondPrimes
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

theorem UpperTheory.exists_multiplicative_of_prime_power_values :
    ∀ M : H.P ℚ → ℕ → ℂ, (∀ v, M v 0 = 1) → ∃ μ : ℕ → ℂ, μ 1 = 1 ∧
          (∀ m n : ℕ, 0 < m → 0 < n → m.Coprime n → μ (m * n) = μ m * μ n) ∧
          ∀ (v : H.P ℚ) (k : ℕ), μ (normV v ^ k) = M v k := by
  intro M hM
  obtain ⟨hp, -, hinj, -⟩ := UpperTheory.heightOneSpectrum_rat_correspond_primes
  let f : ℕ → ℕ → ℂ := fun p k =>
    if h : ∃ v : H.P ℚ, normV v = p then M h.choose k else 1
  have hf : ∀ (v : H.P ℚ) (k : ℕ), f (normV v) k = M v k := by
    intro v k
    have h : ∃ w : H.P ℚ, normV w = normV v := ⟨v, rfl⟩
    have h2 : h.choose = v := hinj _ _ h.choose_spec
    simp only [f]
    rw [dif_pos h, h2]
  refine ⟨fun n => n.factorization.prod f, by simp, ?_, ?_⟩
  · intro m n hm hn hmn
    show (m * n).factorization.prod f = m.factorization.prod f * n.factorization.prod f
    rw [Nat.factorization_mul hm.ne' hn.ne']
    exact Finsupp.prod_add_index_of_disjoint
      (by simpa using hmn.disjoint_primeFactors) f
  · intro v k
    show (normV v ^ k).factorization.prod f = M v k
    rw [(hp v).factorization_pow, Finsupp.prod_single_index (by rw [hf, hM]), hf]
