import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductOfVectorMultiplicationsMemFiltrationLattiStatement
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

namespace GlobalTheory.HSShort.CoeffInt

theorem word_col {K A : Type} [Field K] [AddCommGroup A] [Module K A] {N n t : ℕ}
    (mul : (Fin N → K) →ₗ[K] Module.End K A) (w : Matrix (Fin N) (Fin n) K) (g : Fin t → Fin n) :
    word mul (fun i => w.col (g i)) =
      ∑ e : Fin t → Fin N, (∏ i, w (e i) (g i)) • word mul (fun i => Pi.single (e i) 1) := by
  let Φ := (MultilinearMap.mkPiAlgebraFin K t (Module.End K A)).compLinearMap (fun _ => mul)
  have hΦ : ∀ u : Fin t → Fin N → K, word mul u = Φ u := by
    intro u; simp [Φ, word, MultilinearMap.mkPiAlgebraFin_apply]
  have hcol : ∀ i, w.col (g i) = ∑ j, w j (g i) • (Pi.single j 1 : Fin N → K) := by
    intro i; funext k; simp [Matrix.col, Finset.sum_apply, Pi.single_apply]
  rw [hΦ]
  simp_rw [hcol]
  rw [MultilinearMap.map_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [MultilinearMap.map_smul_univ, hΦ]

theorem linSubst_coordP {K A : Type} [Field K] [AddCommGroup A] [Module K A] {N n B t : ℕ}
    (mul : (Fin N → K) →ₗ[K] Module.End K A) (w : Matrix (Fin N) (Fin n) K) (c : A →ₗ[K] K)
    (β : Fin t → Fin B) (x : A) :
    linSubst w (coordP mul c β x) =
      ∑ g : Fin t → Fin n, C (c (word mul (fun i => w.col (g i)) x)) *
        ∏ i, (X (β i, g i) : MvPolynomial (Fin B × Fin n) K) := by
  rw [show (∑ g : Fin t → Fin n, C (c (word mul (fun i => w.col (g i)) x)) *
        ∏ i, (X (β i, g i) : MvPolynomial (Fin B × Fin n) K)) =
      ∑ g : Fin t → Fin n, ∑ e : Fin t → Fin N, C (c (word mul (fun i => Pi.single (e i) 1) x)) *
        ((∏ i, C (w (e i) (g i))) * ∏ i, (X (β i, g i) : MvPolynomial (Fin B × Fin n) K)) from ?_]
  · simp only [linSubst, coordP, map_sum, map_mul, aeval_C, map_prod, aeval_X, algebraMap_eq]
    simp_rw [Fintype.prod_sum, Finset.mul_sum, ← Finset.prod_mul_distrib]
    exact Finset.sum_comm
  · refine Finset.sum_congr rfl fun g _ => ?_
    rw [word_col, LinearMap.sum_apply, map_sum, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [LinearMap.smul_apply, map_smul, smul_eq_mul, ← map_prod, map_mul]
    ring

theorem prod_X_monomial {σ K : Type} [Field K] {t : ℕ} (f : Fin t → σ) :
    ∃ s, (∏ i, (X (f i) : MvPolynomial σ K)) = monomial s 1 := by
  refine Finset.prod_induction _ (fun q => ∃ s, q = monomial s 1) ?_ ?_ ?_
  · rintro _ _ ⟨s, rfl⟩ ⟨s', rfl⟩; exact ⟨s + s', by rw [monomial_mul, one_mul]⟩
  · exact ⟨0, by simp⟩
  · intro i _; exact ⟨_, rfl⟩

end GlobalTheory.HSShort.CoeffInt

open GlobalTheory.HSShort.CoeffInt in

theorem GlobalTheory.HSShort.colCoeff_mem : ∀ (F A : Type) [Field F] [NumberField F] [AddCommGroup A] [Module F A] [Module (𝓞 F) A] [IsScalarTower (𝓞 F) F A] (S : Sys F A), S.Hyp → ∀ (d : ℕ) (b : Module.Basis (Fin d) F (S.V S.T)) (c : Fin d → A →ₗ[F] F), S.IsCo b c → ∀ κ : S.Col, κ.x ∈ S.M κ.j → ∀ m, ∑ i, coeff m (linSubst S.w (coordP S.mul (c i) κ.β (κ.x : A))) • b i ∈ S.M S.T := by
  intro F A _ _ _ _ _ _ S hS d b c hco κ hx m
  obtain ⟨-, hM⟩ := GlobalTheory.T.productOfVectorMultiplications_mem_filtration_lattice F A S hS κ.j κ.t (le_of_eq κ.add)
  have tr : ∀ j', j' = S.T → ∀ y' ∈ S.M j', ∃ y ∈ S.M S.T, (y : A) = (y' : A) := by
    rintro j' rfl y' hy'; exact ⟨y', hy', rfl⟩
  have key : ∀ g : Fin κ.t → Fin S.n, ∃ y ∈ S.M S.T,
      (y : A) = word S.mul (fun i => S.w.col (g i)) (κ.x : A) := by
    intro g
    obtain ⟨y, hy, hyeq⟩ := hM g κ.x hx
    obtain ⟨z, hz, hzeq⟩ := tr _ κ.add y hy
    exact ⟨z, hz, hzeq.trans hyeq⟩
  choose Y hY hYeq using key
  choose s hs using fun g : Fin κ.t → Fin S.n =>
    prod_X_monomial (K := F) (fun i => (κ.β i, g i))
  have hcoef : ∀ i, coeff m (linSubst S.w (coordP S.mul (c i) κ.β (κ.x : A))) =
      ∑ g, b.repr (Y g) i * (if s g = m then 1 else 0) := by
    intro i
    rw [linSubst_coordP, coeff_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [coeff_C_mul, hs g, coeff_monomial, ← hYeq g, hco]
  simp_rw [hcoef, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Submodule.sum_mem _ fun g _ => ?_
  have hsum : ∑ i, (b.repr (Y g) i * (if s g = m then (1 : F) else 0)) • b i =
      (if s g = m then (1 : F) else 0) • Y g := by
    conv_rhs => rw [← b.sum_repr (Y g), Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul, mul_comm]
  rw [hsum]
  split_ifs
  · rw [one_smul]; exact hY g
  · rw [zero_smul]; exact zero_mem _
