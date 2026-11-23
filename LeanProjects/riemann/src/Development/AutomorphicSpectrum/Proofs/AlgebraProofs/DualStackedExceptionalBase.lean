import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualStackedExcChart
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DualStackedGraphBihomogeneous
set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.Ar.Giv

open GroundTheory.Heights₂.Heights ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial NumberField Matrix

noncomputable section

section Scale

variable {T : Type} [Fintype T]

def blockVal {R : Type} (P Q : T → R) : (Σ κ, stackedBlocks T κ) → R
  | ⟨.inl _, t⟩ => P t
  | ⟨.inr _, t⟩ => Q t

def blockEval {R : Type} [CommRing R] (P Q : T → R) : MRing (stackedBlocks T) →+* R :=
  eval₂Hom (Int.castRingHom R) (blockVal P Q)

theorem blockEval_first {R : Type} [CommRing R] (P Q : T → R) (t : T) :
    blockEval P Q (graphFirst t) = P t := by
  simp [blockEval, graphFirst, blockVal]

theorem blockEval_second {R : Type} [CommRing R] (P Q : T → R) (t : T) :
    blockEval P Q (graphSecond t) = Q t := by
  simp [blockEval, graphSecond, blockVal]

theorem ringHom_block_ext {R : Type} [CommRing R] {f g : MRing (stackedBlocks T) →+* R}
    (h1 : ∀ t, f (graphFirst t) = g (graphFirst t)) (h2 : ∀ t, f (graphSecond t) = g (graphSecond t)) :
    f = g := by
  apply MvPolynomial.ringHom_ext
  · intro n
    simp
  · rintro ⟨(u | u), t⟩ <;> obtain ⟨⟩ := u
    · exact h1 t
    · exact h2 t

theorem blockEval_scale {R : Type} [CommRing R] (P Q : T → R) (l μ : R) {d e : ℕ}
    {f : MRing (stackedBlocks T)} (hf : IsMultiHomog f (bidegree d e)) :
    blockEval (fun t => l * P t) (fun t => μ * Q t) f = l ^ d * μ ^ e * blockEval P Q f := by
  classical
  simp only [blockEval, coe_eval₂Hom]
  rw [eval₂_eq', eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have h1 : ∑ t : T, m ⟨Sum.inl (), t⟩ = d := hf m hm (Sum.inl ())
  have h2 : ∑ t : T, m ⟨Sum.inr (), t⟩ = e := hf m hm (Sum.inr ())
  have key : ∏ s, blockVal (fun t => l * P t) (fun t => μ * Q t) s ^ m s =
      l ^ d * μ ^ e * ∏ s, blockVal P Q s ^ m s := by
    rw [Fintype.prod_sigma, Fintype.prod_sigma, Fintype.prod_sum_type, Fintype.prod_sum_type]
    simp only [Fintype.prod_unique]
    change (∏ t : T, (l * P t) ^ m ⟨Sum.inl (), t⟩) * (∏ t : T, (μ * Q t) ^ m ⟨Sum.inr (), t⟩) =
      l ^ d * μ ^ e * ((∏ t : T, P t ^ m ⟨Sum.inl (), t⟩) * ∏ t : T, Q t ^ m ⟨Sum.inr (), t⟩)
    simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, h1, h2]
    ring
  rw [key]
  ring

end Scale

section ThetaShiftProofs

variable {K : Type} [Field K] {i m : ℕ}

theorem arc_form (p : K) (y₀ : Fin i → K) (g : Fin m → Fin i → K) (φ : Fin i → K) :
    eval₂Hom (C : K →+* MvPolynomial (Fin (m + 1)) K)
        (fun j => C p * (C (y₀ j) * X 0 + ∑ l, C (g l j) * X l.succ)) (∑ j, C (φ j) * X j) =
      C p * (C (φ ⬝ᵥ y₀) * X 0 + ∑ l, C (φ ⬝ᵥ g l) * X l.succ) := by
  have hj : ∀ j, eval₂Hom (C : K →+* MvPolynomial (Fin (m + 1)) K)
      (fun j => C p * (C (y₀ j) * X 0 + ∑ l, C (g l j) * X l.succ)) (C (φ j) * X j) =
      C p * (C (φ j * y₀ j) * X 0 + ∑ l, C (φ j * g l j) * X l.succ) := by
    intro j
    rw [map_mul, eval₂Hom_C, eval₂Hom_X']
    simp only [C_mul, mul_assoc, ← Finset.mul_sum]
    ring
  rw [map_sum, Finset.sum_congr rfl fun j _ => hj j, ← Finset.mul_sum, Finset.sum_add_distrib,
    ← Finset.sum_mul, Finset.sum_comm]
  simp only [dotProduct, map_sum, Finset.sum_mul]

end ThetaShiftProofs

section Lead

variable {K : Type} [Field K] [NumberField K] {i : ℕ} {F F' : HermLattice K i} {T : Type} [Fintype T]

theorem lead_of_coords {b : Module.Basis T ℤ (dualLattice F)} {b' : Module.Basis T ℤ (dualLattice F')}
    {k : Type} [Field k] {ρ : 𝓞 K →+* k} {π : 𝓞 K} {y₀ : Fin i → K} {m : ℕ} {g : Fin m → Fin i → K}
    {α : T → k} {M : T → Fin (m + 1) → k} (hco : IsExcCoords F F' b b' ρ π y₀ g α M) {d e : ℕ}
    {f : MRing (stackedBlocks T)} (hf : IsMultiHomog f (bidegree d e))
    (h0 : stackedFormEval b b' f = 0) : linPointMap α M f = 0 := by
  obtain ⟨-, hπ, -, hg, hα, hM0, hMj, ⟨t₀, ht₀⟩, -, -, -, -⟩ := hco
  choose cα hcα hcαρ using hα
  choose c0 hc0 hc0ρ using hM0
  choose c1 hc1 hc1ρ using hMj
  have hh : ∀ t l, ∃ c : 𝓞 K, algebraMap (𝓞 K) K c = (b' t : Fin i → K) ⬝ᵥ g l :=
    fun t l => (b' t).2 _ (hg l)
  choose h hh using hh
  have hinj : Function.Injective (algebraMap (𝓞 K) K) := IsFractionRing.injective (𝓞 K) K
  have hπ0 : algebraMap (𝓞 K) K π ≠ 0 := by
    intro hp
    apply ht₀
    have hc : cα t₀ = 0 := hinj (by rw [hcα, hp, map_zero, zero_smul, dotProduct_zero])
    rw [← hcαρ t₀, hc, map_zero]

  let A : T → MvPolynomial (Fin (m + 1)) (𝓞 K) :=
    fun t => C (cα t) * X 0 + ∑ l, C (π * h t l) * X l.succ
  let L : T → MvPolynomial (Fin (m + 1)) (𝓞 K) :=
    fun t => C (c0 t) * X 0 + ∑ l, C (c1 t l) * X l.succ
  let ι : MvPolynomial (Fin (m + 1)) (𝓞 K) →+* MvPolynomial (Fin (m + 1)) K :=
    map (algebraMap (𝓞 K) K)
  have hι : Function.Injective ι := map_injective _ hinj
  let p : K := algebraMap (𝓞 K) K π
  let Φ : MvPolynomial (Fin i) K →+* MvPolynomial (Fin (m + 1)) K :=
    eval₂Hom C (fun j => C p * (C (y₀ j) * X 0 + ∑ l, C (g l j) * X l.succ))
  have hΦ : Φ.comp (stackedFormEval b b') =
      blockEval (fun t => 1 * ι (A t)) (fun t => C p * ι (L t)) := by
    apply ringHom_block_ext
    · intro t
      rw [RingHom.comp_apply, DualStackedExcLeadExample.stackedFormEval_first, blockEval_first]
      refine (arc_form p y₀ g _).trans ?_
      simp only [A, ι, map_add, map_mul, map_C, map_X, map_sum, one_mul]
      rw [hcα, dotProduct_smul, smul_eq_mul, C_mul, mul_add, Finset.mul_sum, mul_assoc]
      congr 1
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [hh]
      exact (mul_assoc _ _ _).symm
    · intro t
      rw [RingHom.comp_apply, DualStackedExcLeadExample.stackedFormEval_second, blockEval_second]
      refine (arc_form p y₀ g _).trans ?_
      simp only [L, ι, map_add, map_mul, map_C, map_X, map_sum, hc0, hc1]
  have hι2 : blockEval (fun t => ι (A t)) (fun t => ι (L t)) = ι.comp (blockEval A L) := by
    apply ringHom_block_ext
    · intro t
      simp only [RingHom.comp_apply, blockEval_first]
    · intro t
      simp only [RingHom.comp_apply, blockEval_second]
  have e1 : (C p) ^ e * ι (blockEval A L f) = 0 := by
    have h1 := congrArg (fun r => r f) hΦ
    simp only [RingHom.comp_apply, h0, map_zero] at h1
    rw [blockEval_scale _ _ _ _ hf, hι2, one_pow, one_mul, RingHom.comp_apply] at h1
    exact h1.symm
  have e2 : blockEval A L f = 0 := by
    have hCp : (C p : MvPolynomial (Fin (m + 1)) K) ≠ 0 := by
      rw [Ne, C_eq_zero]
      exact hπ0
    exact hι (by rw [map_zero]; exact (mul_eq_zero.mp e1).resolve_left (pow_ne_zero _ hCp))

  let ψ : MvPolynomial (Fin (m + 1)) (𝓞 K) →+* MvPolynomial (Option (Fin (m + 1))) k :=
    eval₂Hom (C.comp ρ) (fun j => X (some j))
  let ℓ : T → MvPolynomial (Option (Fin (m + 1))) k := fun t => ∑ j, C (M t j) * X (some j)
  have hψ : ψ.comp (blockEval A L) =
      blockEval (fun t => X (some 0) * C (α t)) (fun t => 1 * ℓ t) := by
    apply ringHom_block_ext
    · intro t
      rw [RingHom.comp_apply, blockEval_first, blockEval_first]
      simp only [A, ψ, map_add, map_mul, eval₂Hom_C, eval₂Hom_X', map_sum, RingHom.comp_apply, hcαρ,
        hπ, map_zero, zero_mul, Finset.sum_const_zero, add_zero]
      ring
    · intro t
      rw [RingHom.comp_apply, blockEval_second, blockEval_second]
      simp only [L, ψ, ℓ, map_add, map_mul, eval₂Hom_C, eval₂Hom_X', map_sum, RingHom.comp_apply, hc0ρ,
        hc1ρ, one_mul, Fin.sum_univ_succ]
  have hlin : (linPointMap α M : MRing (stackedBlocks T) →+* _) =
      blockEval (fun t => X none * C (α t)) (fun t => 1 * ℓ t) := by
    apply ringHom_block_ext
    · intro t
      rw [LinPrimeExample.linPointMap_first, blockEval_first, mul_comm]
    · intro t
      rw [LinPrimeExample.linPointMap_second, blockEval_second, one_mul]
  have e3 : blockEval (fun t => C (α t)) ℓ f = 0 := by
    have h1 := congrArg (fun r => r f) hψ
    simp only [RingHom.comp_apply, e2, map_zero] at h1
    rw [blockEval_scale _ _ _ _ hf, one_pow, mul_one] at h1
    exact (mul_eq_zero.mp h1.symm).resolve_left (pow_ne_zero _ (X_ne_zero _))
  rw [hlin, blockEval_scale _ _ _ _ hf, e3, mul_zero]

theorem centre_mem_of_coords {b : Module.Basis T ℤ (dualLattice F)} {b' : Module.Basis T ℤ (dualLattice F')}
    {a : T → ℤ} (hab : ∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) {k : Type} [Field k]
    {ρ : 𝓞 K →+* k} {π : 𝓞 K} {y₀ : Fin i → K} {m : ℕ} {g : Fin m → Fin i → K}
    {α : T → k} {M : T → Fin (m + 1) → k} (hco : IsExcCoords F F' b b' ρ π y₀ g α M) (t : T) :
    C (a t) * graphFirst t ∈ linPrime α M := by
  obtain ⟨-, hπ, -, -, hα, hM0, -⟩ := hco
  obtain ⟨c, hc, hcρ⟩ := hα t
  obtain ⟨c', hc', -⟩ := hM0 t
  have hinj : Function.Injective (algebraMap (𝓞 K) K) := IsFractionRing.injective (𝓞 K) K
  have h : ((a t : ℤ) : 𝓞 K) * c = π * c' := by
    apply hinj
    rw [map_mul, map_mul, map_intCast, hc, hc', hab t, dotProduct_smul, smul_dotProduct, smul_eq_mul,
      zsmul_eq_mul]
    ring
  have h0 : ((a t : ℤ) : k) * α t = 0 := by
    rw [← hcρ, ← map_intCast ρ, ← map_mul, h, map_mul, hπ, zero_mul]
  have h1 : linPointMap α M (C (a t)) = C ((a t : k)) := by simp [linPointMap]
  rw [linPrime, RingHom.mem_ker, map_mul, h1, LinPrimeExample.linPointMap_first, ← mul_assoc, ← C_mul, h0, C_0,
    zero_mul]

end Lead

theorem exc_base : DualStackedExcBase.Statement := by
  intro K _ _ i F F' T _ _ b b' a hi hlt hcov hab k _ ρ π y₀ m g α M hco
  refine sup_le ?_ ?_
  · intro f hf
    obtain ⟨s, G, rfl, hG⟩ := graph_bihomog K i F F' T b b' a hab f hf
    rw [linPrime, RingHom.mem_ker, map_sum]
    exact Finset.sum_eq_zero fun p hp => lead_of_coords hco (hG p hp).1 (hG p hp).2
  · rw [Ideal.span_le, Set.range_subset_iff]
    exact centre_mem_of_coords hab hco

end

end GlobalTheory.CompanionTheory.Ar.Giv
