import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Formalism.HarderNarasimhan.ShiftInvariance
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory

theorem isIntegral_of_left_eigenvector_of_lattice {E K : Type} [Field E] [NumberField E] [Field K]
    [Algebra E K] [Algebra (𝓞 E) K] [IsScalarTower (𝓞 E) E K] {n : ℕ}
    (Λ : Submodule (𝓞 E) (Fin n → E)) (B : Matrix (Fin n) (Fin n) E) (c : E) (w : K)
    (v : Fin n → K) (hfg : Λ.FG) (hsp : Submodule.span E (Λ : Set (Fin n → E)) = ⊤)
    (hc : c ≠ 0) (hB : ∀ y ∈ Λ, ∃ z ∈ Λ, B *ᵥ y = c • z) (hv : v ≠ 0)
    (hw : v ᵥ* (B.map (algebraMap E K)) = (algebraMap E K c * w) • v) :
    IsIntegral (𝓞 E) w := by
  let φ : (Fin n → E) →ₗ[E] K :=
    { toFun := fun y => v ⬝ᵥ (fun i => algebraMap E K (y i))
      map_add' := by
        intro x y
        simp [dotProduct, mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro a x
        simp [dotProduct, Finset.mul_sum, Algebra.smul_def, mul_left_comm] }
  have hφ : ∀ y, φ (B *ᵥ y) = (algebraMap E K c * w) * φ y := by
    intro y
    have h1 : (fun i => algebraMap E K ((B *ᵥ y) i))
        = (B.map (algebraMap E K)) *ᵥ (fun i => algebraMap E K (y i)) := by
      ext i
      simp [Matrix.mulVec, dotProduct, map_sum]
    show v ⬝ᵥ (fun i => algebraMap E K ((B *ᵥ y) i)) = _ * (v ⬝ᵥ (fun i => algebraMap E K (y i)))
    rw [h1, Matrix.dotProduct_mulVec, hw, smul_dotProduct, smul_eq_mul]
  have hcK : algebraMap E K c ≠ 0 := by simpa using hc
  let N : Submodule (𝓞 E) K := Λ.map (φ.restrictScalars (𝓞 E))
  refine isIntegral_of_smul_mem_submodule N ?_ (hfg.map _) w ?_
  · intro hN
    apply hv
    have h0 : ∀ y ∈ Λ, φ y = 0 := by
      intro y hy
      have : φ y ∈ N := ⟨y, hy, rfl⟩
      rw [hN] at this
      simpa using this
    have hk : (⊤ : Submodule E (Fin n → E)) ≤ LinearMap.ker φ := by
      rw [← hsp, Submodule.span_le]
      intro y hy
      exact h0 y hy
    ext i
    have := hk (Submodule.mem_top (x := Pi.single i (1 : E)))
    have h2 : v ⬝ᵥ (fun j => algebraMap E K ((Pi.single i (1 : E) : Fin n → E) j)) = 0 := this
    simpa [dotProduct, Pi.single_apply, apply_ite] using h2
  · rintro _ ⟨y, hy, rfl⟩
    obtain ⟨z, hz, hyz⟩ := hB y hy
    refine ⟨z, hz, ?_⟩
    have h := hφ y
    rw [hyz, map_smul, Algebra.smul_def, mul_assoc] at h
    have h' := mul_left_cancel₀ hcK h
    simpa using h'

theorem trace_mem_of_nilpotent_mod_radical (E : Type) [Field E] [NumberField E] (n m g : ℕ)
    (Λ : Submodule (𝓞 E) (Fin n → E)) (A : Matrix (Fin n) (Fin n) E) (hfg : Λ.FG)
    (hsp : Submodule.span E (Λ : Set (Fin n → E)) = ⊤)
    (hrad : (Ideal.span {(g : 𝓞 E)}).IsRadical) (hg : 1 ≤ g)
    (hA : ∀ y ∈ Λ, A *ᵥ y ∈ Λ) (hm : ∀ y ∈ Λ, ∃ z ∈ Λ, (A ^ m) *ᵥ y = (g : E) • z) :
    ∃ t : 𝓞 E, A.trace = (g : E) * (t : E) := by
  let K := AlgebraicClosure E
  let f : E →+* K := algebraMap E K
  let R := integralClosure (𝓞 E) K
  have hgE : (g : E) ≠ 0 := by exact_mod_cast (by omega : g ≠ 0)
  have hgK : (g : K) ≠ 0 := by
    have : f (g : E) ≠ 0 := by simpa only [map_ne_zero] using hgE
    simpa using this
  have hroot : ∀ z ∈ (A.map f).charpoly.roots,
      ∃ r : R, r ∈ (Ideal.span {(g : R)}).radical ∧ (r : K) = z := by
    intro z hz
    have h0 : (Matrix.scalar (Fin n) z - A.map f).det = 0 := by
      rw [← Matrix.eval_charpoly]
      exact (Polynomial.mem_roots'.1 hz).2
    obtain ⟨v, hv, hvz⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h0
    have h1 : v ᵥ* (A.map f) = z • v := by
      rw [Matrix.vecMul_sub, sub_eq_zero] at hvz
      rw [← hvz]
      ext i
      simp [Matrix.vecMul_diagonal, mul_comm]
    have hk : ∀ k : ℕ, v ᵥ* ((A ^ k).map f) = z ^ k • v := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ, Matrix.map_mul, ← Matrix.vecMul_vecMul, ih, Matrix.smul_vecMul, h1,
          smul_smul, pow_succ]
    have hi1 : IsIntegral (𝓞 E) z :=
      isIntegral_of_left_eigenvector_of_lattice Λ A 1 z v hfg hsp one_ne_zero
        (fun y hy => ⟨_, hA y hy, by simp⟩) hv (by simpa using h1)
    have hi2 : IsIntegral (𝓞 E) (z ^ m / (g : K)) :=
      isIntegral_of_left_eigenvector_of_lattice Λ (A ^ m) (g : E) _ v hfg hsp hgE hm hv (by
        rw [map_natCast, mul_div_cancel₀ _ hgK]
        exact hk m)
    refine ⟨⟨z, hi1⟩, ⟨m, Ideal.mem_span_singleton'.2 ⟨⟨_, hi2⟩, ?_⟩⟩, rfl⟩
    apply Subtype.ext
    show z ^ m / (g : K) * ((g : R) : K) = z ^ m
    have : ((g : R) : K) = (g : K) := by simp
    rw [this, div_mul_cancel₀ _ hgK]
  have hsum : ∃ r : R, r ∈ (Ideal.span {(g : R)}).radical ∧
      (r : K) = (A.map f).charpoly.roots.sum := by
    refine Multiset.sum_induction (fun x : K => ∃ r : R,
      r ∈ (Ideal.span {(g : R)}).radical ∧ (r : K) = x) _ ?_ ⟨0, Ideal.zero_mem _, rfl⟩ hroot
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a + b, Ideal.add_mem _ ha hb, rfl⟩
  rw [← Matrix.trace_eq_sum_roots_charpoly, ← AddMonoidHom.map_trace f A] at hsum
  obtain ⟨r, ⟨N, hN⟩, hr⟩ := hsum
  obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.1 hN
  have hdown : ∀ x : E, IsIntegral (𝓞 E) (f x) → ∃ t : 𝓞 E, (t : E) = x := by
    intro x hx
    exact IsIntegrallyClosed.isIntegral_iff.1
      ((isIntegral_algebraMap_iff (algebraMap E K).injective).1 hx)
  obtain ⟨t₀, ht₀⟩ := hdown A.trace (hr ▸ r.2)
  have hsK : (s : K) * (g : K) = f A.trace ^ N := by
    have := congrArg (fun x : R => (x : K)) hs
    simpa [hr] using this
  obtain ⟨u, hu⟩ := hdown (A.trace ^ N / (g : E)) (by
    rw [map_div₀, map_pow, map_natCast, ← hsK, mul_div_cancel_right₀ _ hgK]
    exact s.2)
  have hmem : t₀ ∈ Ideal.span {(g : 𝓞 E)} := by
    apply hrad
    refine ⟨N, Ideal.mem_span_singleton'.2 ⟨u, ?_⟩⟩
    apply RingOfIntegers.coe_injective
    have h : (u : E) * (g : E) = (t₀ : E) ^ N := by
      rw [hu, ht₀, div_mul_cancel₀ _ hgE]
    simpa using h
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 hmem
  refine ⟨t, ?_⟩
  rw [← ht₀, ← ht]
  simp [mul_comm]

end GlobalTheory
