import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.AdeleApproximation.AdeleIntA

namespace ReciprocityTheory.ChartRestriction.G.SA

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Topology WithZero Filter

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K]

theorem small_mem_nhds (v : HeightOneSpectrum R) {s : Set (v.adicCompletion K)}
    (hs : s ∈ 𝓝 (0 : v.adicCompletion K)) :
    ∃ n : ℕ, ∀ x, Valued.v x ≤ exp (-(n : ℤ)) → x ∈ s := by
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.1 hs
  have hg := MonoidWithZeroHom.ValueGroup₀.embedding_unit_ne_zero γ
  refine ⟨(log (MonoidWithZeroHom.ValueGroup₀.embedding γ.1)).natAbs + 1, fun x hx => hγ ?_⟩
  show Valued.v.restrict x < γ.1
  rw [Valuation.restrict_lt_iff_lt_embedding]
  refine lt_of_le_of_lt hx ?_
  calc exp (-(((log (MonoidWithZeroHom.ValueGroup₀.embedding γ.1)).natAbs + 1 : ℕ) : ℤ))
      < exp (log (MonoidWithZeroHom.ValueGroup₀.embedding γ.1)) := exp_lt_exp.2 (by omega)
    _ = _ := exp_log hg

theorem nhds_zero_int {N : Set (FiniteAdeleRing R K)} (hN : N ∈ 𝓝 (0 : FiniteAdeleRing R K)) :
    ∃ r : R, r ≠ 0 ∧ ∀ y : FiniteAdeleRing R K,
      (∀ v, Valued.v (y v) ≤ v.intValuation r) → y ∈ N := by
  have hBopen : ∀ v : HeightOneSpectrum R,
      IsOpen ((v.adicCompletionIntegers K : ValuationSubring _) : Set (v.adicCompletion K)) :=
    fun v => Valued.isOpen_valuationSubring _
  let mk : (∀ v : HeightOneSpectrum R, v.adicCompletionIntegers K) → FiniteAdeleRing R K :=
    fun y => ⟨fun v => (y v : v.adicCompletion K), Eventually.of_forall fun v => (y v).2⟩
  have hmk : Continuous mk := by
    exact (RestrictedProduct.isEmbedding_structureMap (R := fun v : HeightOneSpectrum R => v.adicCompletion K)
      (A := fun v => ((v.adicCompletionIntegers K : ValuationSubring _) : Set (v.adicCompletion K)))
      (𝓕 := cofinite)).continuous
  have hmk0 : mk 0 = 0 := rfl
  have hpre : mk ⁻¹' N ∈ 𝓝 (0 : ∀ v : HeightOneSpectrum R, v.adicCompletionIntegers K) :=
    hmk.continuousAt.preimage_mem_nhds (by rw [hmk0]; exact hN)
  rw [nhds_pi, mem_pi] at hpre
  obtain ⟨T, hT, t, ht, hsub⟩ := hpre
  have hloc : ∀ v, ∃ n : ℕ, ∀ x : v.adicCompletionIntegers K,
      Valued.v (x : v.adicCompletion K) ≤ exp (-(n : ℤ)) → x ∈ t v := by
    intro v
    obtain ⟨u, hu, hut⟩ := (mem_nhds_subtype _ _ _).1 (ht v)
    have hu0 : u ∈ 𝓝 (0 : v.adicCompletion K) := by simpa using hu
    obtain ⟨n, hn⟩ := small_mem_nhds v hu0
    exact ⟨n, fun x hx => hut (hn _ hx)⟩
  choose n hn using hloc
  let I : Ideal R := ∏ v ∈ hT.toFinset, v.asIdeal ^ (n v)
  have hI : I ≠ ⊥ := by
    rw [← Ideal.zero_eq_bot]
    exact Finset.prod_ne_zero_iff.2 fun v _ => pow_ne_zero _ (by rw [Ideal.zero_eq_bot]; exact v.ne_bot)
  obtain ⟨r, hrI, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  refine ⟨r, hr0, fun y hy => ?_⟩
  have hyint : ∀ v, y v ∈ v.adicCompletionIntegers K := fun v => by
    rw [mem_adicCompletionIntegers]
    exact (hy v).trans (v.intValuation_le_one r)
  have hy' : y = mk (fun v => ⟨y v, hyint v⟩) := by ext v; rfl
  rw [hy']
  apply hsub
  intro v hv
  apply hn v
  refine (hy v).trans ?_
  rw [intValuation_le_pow_iff_mem]
  exact Ideal.le_of_dvd (Finset.dvd_prod_of_mem _ (hT.mem_toFinset.2 hv)) hrI

theorem denseRange_finiteAdele : DenseRange (algebraMap K (FiniteAdeleRing R K)) := by
  intro b
  rw [mem_closure_iff_nhds]
  intro N hN
  have h0 : (fun y => b + y) ⁻¹' N ∈ 𝓝 (0 : FiniteAdeleRing R K) := by
    have ht := (continuous_add_left b).tendsto (0 : FiniteAdeleRing R K)
    rw [add_zero] at ht
    exact ht hN
  obtain ⟨r, hr, hrN⟩ := nhds_zero_int h0
  obtain ⟨u, hu⟩ := ReciprocityTheory.ChartRestriction.G.Lib.AdeleIntA.exists_approx_adele b
  obtain ⟨a, ha⟩ := ReciprocityTheory.ChartRestriction.G.Lib.AdeleIntA.exists_approx (b - algebraMap K _ u) hu r hr
  refine ⟨algebraMap K (FiniteAdeleRing R K) (u + algebraMap R K a), ?_, ⟨_, rfl⟩⟩
  have hx : algebraMap K (FiniteAdeleRing R K) (u + algebraMap R K a) - b =
      -((b - algebraMap K (FiniteAdeleRing R K) u) -
        algebraMap K (FiniteAdeleRing R K) (algebraMap R K a)) := by
    rw [map_add]; ring
  have hmem := hrN (algebraMap K (FiniteAdeleRing R K) (u + algebraMap R K a) - b) (by
    rw [hx]
    intro v
    have hv : (-((b - algebraMap K (FiniteAdeleRing R K) u) -
        algebraMap K (FiniteAdeleRing R K) (algebraMap R K a))) v =
        -((b - algebraMap K (FiniteAdeleRing R K) u) v - algebraMap K _ (algebraMap R K a)) := by
      first
      | rfl
      | simp
    rw [hv, Valuation.map_neg]
    exact ha v)
  simpa using hmem

end ReciprocityTheory.ChartRestriction.G.SA
