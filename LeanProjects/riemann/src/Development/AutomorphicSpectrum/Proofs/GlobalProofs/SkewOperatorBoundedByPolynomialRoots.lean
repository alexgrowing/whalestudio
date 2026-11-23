import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IoInjective
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SkewOfCommute
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory Matrix
open scoped TensorProduct Topology InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.SkewSpec

theorem aeval_intertwine {A B : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
    (f : A →ₗ[ℂ] B) (SA : Module.End ℂ A) (SB : Module.End ℂ B)
    (h : ∀ v, f (SA v) = SB (f v)) (p : Polynomial ℂ) (v : A) :
    f (Polynomial.aeval SA p v) = Polynomial.aeval SB p (f v) := by
  induction p using Polynomial.induction_on generalizing v with
  | C a => simp [Polynomial.aeval_C, Module.algebraMap_end_apply]
  | add p q hp hq => simp [hp, hq]
  | monomial n a ih =>
    have hp : Polynomial.C a * Polynomial.X ^ (n + 1) =
        (Polynomial.C a * Polynomial.X ^ n) * (Polynomial.X : Polynomial ℂ) := by ring
    rw [hp, map_mul (Polynomial.aeval SA), map_mul (Polynomial.aeval SB), Polynomial.aeval_X, Polynomial.aeval_X,
      Module.End.mul_apply, Module.End.mul_apply, ih, h]

theorem functional_aeval {A : Type} [AddCommGroup A] [Module ℂ A]
    (φ : A → ℂ) (hadd : ∀ a b, φ (a + b) = φ a + φ b) (hsmul : ∀ (c : ℂ) a, φ (c • a) = c * φ a)
    (S : Module.End ℂ A) (c : ℂ)
    (h : ∀ v, φ (S v) = c * φ v) (p : Polynomial ℂ) (v : A) :
    φ (Polynomial.aeval S p v) = p.eval c * φ v := by
  induction p using Polynomial.induction_on generalizing v with
  | C a => simp [Polynomial.aeval_C, Module.algebraMap_end_apply, hsmul]
  | add p q hp hq => simp [hp, hq, hadd, add_mul]
  | monomial n a ih =>
    rw [pow_succ, ← mul_assoc, map_mul, Polynomial.aeval_X, Module.End.mul_apply, ih, h]
    simp only [Polynomial.eval_mul, Polynomial.eval_X]
    ring

theorem fd_bound {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (S : Module.End ℂ E) (hS : ∀ x y, ⟪S x, y⟫_ℂ = -⟪x, S y⟫_ℂ) (m : Polynomial ℂ) (hm : m ≠ 0)
    (κ : ℝ) (hκ : 0 ≤ κ) (hr : ∀ r ∈ m.roots, ‖r‖ ≤ κ) (u : E)
    (hu : Polynomial.aeval S m u = 0) : ‖S u‖ ≤ κ * ‖u‖ := by
  have hA : (Complex.I • S : E →ₗ[ℂ] E).IsSymmetric := by
    intro x y
    simp [inner_smul_left, inner_smul_right, hS]
  let b := hA.eigenvectorBasis (n := Module.finrank ℂ E) rfl
  let μ := hA.eigenvalues (n := Module.finrank ℂ E) rfl
  have hb : ∀ i, S (b i) = (-Complex.I * (μ i : ℂ)) • b i := by
    intro i
    have h1 := hA.apply_eigenvectorBasis (n := Module.finrank ℂ E) rfl i
    have h2 : Complex.I • S (b i) = ((μ i : ℝ) : ℂ) • b i := by simpa using h1
    have h3 := congrArg (fun w => (-Complex.I) • w) h2
    simp only [smul_smul] at h3
    simpa using h3
  have hφ : ∀ i v, ⟪b i, S v⟫_ℂ = (-Complex.I * (μ i : ℂ)) * ⟪b i, v⟫_ℂ := by
    intro i v
    have h1 := hS (b i) v
    rw [hb, inner_smul_left] at h1
    simp at h1
    linear_combination h1
  have hc : ∀ i, ⟪b i, u⟫_ℂ = 0 ∨ ‖(μ i : ℂ)‖ ≤ κ := by
    intro i
    have h1 := functional_aeval (fun v => ⟪b i, v⟫_ℂ) (fun a c => inner_add_right _ _ _)
      (fun c a => inner_smul_right _ _ _) S _ (hφ i) m u
    simp only [hu, inner_zero_right] at h1
    rcases mul_eq_zero.mp h1.symm with h2 | h2
    · right
      have h3 := hr _ ((Polynomial.mem_roots hm).mpr h2)
      simpa using h3
    · exact Or.inl h2
  have hsq : ‖S u‖ ^ 2 ≤ (κ * ‖u‖) ^ 2 := by
    rw [mul_pow, ← b.sum_sq_norm_inner_right (S u), ← b.sum_sq_norm_inner_right u, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [hφ, norm_mul, mul_pow]
    rcases hc i with h | h
    · simp [h]
    · have h4 : ‖-Complex.I * (μ i : ℂ)‖ ≤ κ := by simpa using h
      gcongr
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq

theorem norm_le_of_aeval_eq_zero (M H : Type) [AddCommGroup M] [Module ℂ M] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (ι : M →ₗ[ℂ] H) (hι : Function.Injective ι) (T : Module.End ℂ M)
    (hT : ∀ x y, ⟪ι (T x), ι y⟫_ℂ = -⟪ι x, ι (T y)⟫_ℂ) (m : Polynomial ℂ) (hm : m ≠ 0) (κ : ℝ)
    (hκ : 0 ≤ κ) (hr : ∀ r ∈ m.roots, ‖r‖ ≤ κ) (x : M) (hx : Polynomial.aeval T m x = 0) :
    ‖ι (T x)‖ ≤ κ * ‖ι x‖ := by
  classical
  let L : Polynomial ℂ →ₗ[ℂ] M :=
    { toFun := fun p => Polynomial.aeval T p x
      map_add' := fun p q => by simp
      map_smul' := fun c p => by simp }
  have hL : ∀ p, L p = Polynomial.aeval T p x := fun _ => rfl
  let N : Submodule ℂ M := LinearMap.range L
  have hNeq : N = (Polynomial.degreeLT ℂ m.natDegree).map L := by
    apply le_antisymm
    · rintro _ ⟨p, rfl⟩
      refine ⟨p % m, ?_, ?_⟩
      · have h1 := Polynomial.degree_mod_lt p hm
        rw [Polynomial.degree_eq_natDegree hm] at h1
        exact Polynomial.mem_degreeLT.mpr h1
      · have h2 : L (m * (p / m)) = 0 := by
          rw [hL, mul_comm, map_mul, Module.End.mul_apply, hx, map_zero]
        have h3 := congrArg L (EuclideanDomain.div_add_mod p m)
        rw [map_add, h2, zero_add] at h3
        exact h3
    · exact LinearMap.map_le_range
  haveI : Module.Finite ℂ (Polynomial.degreeLT ℂ m.natDegree) :=
    Module.Finite.equiv (Polynomial.degreeLTEquiv ℂ m.natDegree).symm
  haveI hfin : Module.Finite ℂ N := by
    rw [hNeq]
    exact Module.Finite.map _ _
  have hN : ∀ v ∈ N, T v ∈ N := by
    rintro _ ⟨p, rfl⟩
    refine ⟨Polynomial.X * p, ?_⟩
    rw [hL, hL, map_mul, Polynomial.aeval_X, Module.End.mul_apply]
  have hxN : x ∈ N := ⟨1, by simp [hL]⟩
  let R : Module.End ℂ N := T.restrict hN
  let e := Submodule.equivMapOfInjective ι hι N
  let S : Module.End ℂ (N.map ι) := e.toLinearMap ∘ₗ R ∘ₗ e.symm.toLinearMap
  have hSe : ∀ v, S (e v) = e (R v) := fun v => by simp [S]
  have heι : ∀ v : N, ((e v : N.map ι) : H) = ι v := fun v => rfl
  have hRc : ∀ v : N, ((R v : N) : M) = T v := fun v => rfl
  have hS : ∀ a b, ⟪S a, b⟫_ℂ = -⟪a, S b⟫_ℂ := by
    intro a b
    obtain ⟨a', rfl⟩ := e.surjective a
    obtain ⟨b', rfl⟩ := e.surjective b
    rw [hSe, hSe, Submodule.coe_inner, Submodule.coe_inner, heι, heι, heι, heι, hRc, hRc]
    exact hT _ _
  let x' : N := ⟨x, hxN⟩
  have h1 : ((Polynomial.aeval R m x' : N) : M) = 0 := by
    have := aeval_intertwine N.subtype R T (fun v => rfl) m x'
    simpa [x', hx] using this
  have h2 : Polynomial.aeval R m x' = 0 := Subtype.ext h1
  have h3 : Polynomial.aeval S m (e x') = 0 := by
    have := aeval_intertwine e.toLinearMap R S (fun v => (hSe v).symm) m x'
    rw [h2] at this
    simpa using this.symm
  have h4 := fd_bound S hS m hm κ hκ hr (e x') h3
  rw [hSe, Submodule.coe_norm, Submodule.coe_norm, heι, heι, hRc] at h4
  exact h4

end GlobalTheory.CompanionTheory.SkewSpec
