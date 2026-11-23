import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WittExtensionTotallyDefiniteHermitianStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsMaximalIntegralHermitianLatticeOrthonormalStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MaximalHermitianLatticeBadPrimesIffGramDetStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemHcompl
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsOrthogonalBasisDotProductApplyEq
import Formalism.HermitianLattices.HermitianLatticesProofs.LocDual

open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

namespace GlobalTheory.Mass.SameBad

section Val

variable {K : Type} [Field K] [NumberField K] [StarRing K]

def NormUnit (P : Ideal (𝓞 K)) (x : K) : Prop :=
  ∃ c : K, c ≠ 0 ∧ star c * c * x ∈ locR (K := K) P ∧ (star c * c * x)⁻¹ ∈ locR (K := K) P

theorem mem_locR_iff (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (hc : conjIdeal (K := K) v.asIdeal = v.asIdeal) (a : K) :
    a ∈ locR (K := K) v.asIdeal ↔ v.valuation K a ≤ 1 := by
  have mR : a ∈ locR (K := K) v.asIdeal ↔ ∃ s, s ∉ v.asIdeal ∧ ∃ r : 𝓞 K,
      algebraMap (𝓞 K) K r = algebraMap (𝓞 K) K s * a :=
    exists_congr fun s => and_congr (LocWitt.mem_hcompl v.isMaximal hc s)
      (by rw [Submodule.mem_one, Algebra.smul_def])
  rw [mR]
  constructor
  · rintro ⟨s, hs, r, e⟩
    have h1 : v.valuation K (algebraMap (𝓞 K) K s) = 1 :=
      (v.valuation_eq_one_iff_notMem (K := K)).2 hs
    have h2 : v.valuation K (algebraMap (𝓞 K) K r) ≤ 1 := v.valuation_le_one (K := K) r
    rwa [e, map_mul, h1, one_mul] at h2
  · intro ha
    obtain ⟨n, d, e⟩ := v.exists_primeCompl_mul_eq_of_integer a ha
    exact ⟨d, d.2, n, by rw [← e, mul_comm]⟩

theorem star_mem_locR {P : Ideal (𝓞 K)} (hP : P.IsMaximal) (hc : conjIdeal (K := K) P = P) {a : K}
    (ha : a ∈ locR (K := K) P) : star a ∈ locR (K := K) P := by
  have mR : ∀ a : K, a ∈ locR (K := K) P ↔ ∃ s, s ∉ P ∧ ∃ r : 𝓞 K,
      algebraMap (𝓞 K) K r = algebraMap (𝓞 K) K s * a := fun a =>
    exists_congr fun s => and_congr (LocWitt.mem_hcompl hP hc s)
      (by rw [Submodule.mem_one, Algebra.smul_def])
  obtain ⟨s, hs, r, e⟩ := (mR a).1 ha
  obtain ⟨s', es⟩ := LocWitt.star_int s
  obtain ⟨r', er⟩ := LocWitt.star_int r
  refine (mR _).2 ⟨s', fun a => hs ?_, r', by rw [er, es, e, star_mul']⟩
  rw [← hc]
  exact Ideal.subset_span ⟨s', a, by rw [es, star_star]⟩

theorem valuation_star (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (hc : conjIdeal (K := K) v.asIdeal = v.asIdeal) (a : K) :
    v.valuation K (star a) = v.valuation K a := by
  have le1 : ∀ a : K, v.valuation K a ≤ 1 → v.valuation K (star a) ≤ 1 := fun a ha =>
    (mem_locR_iff v hc _).1 (star_mem_locR v.isMaximal hc ((mem_locR_iff v hc _).2 ha))
  have mono : ∀ a b : K, b ≠ 0 → v.valuation K a ≤ v.valuation K b →
      v.valuation K (star a) ≤ v.valuation K (star b) := by
    intro a b hb hab
    have hb' : v.valuation K b ≠ 0 := by simpa using hb
    have hb'' : v.valuation K (star b) ≠ 0 := by simpa using hb
    have := le1 (a / b) (by rw [map_div₀]; exact div_le_one_of_le₀ hab zero_le')
    rw [star_div₀, map_div₀] at this
    exact (div_le_one₀ (zero_lt_iff.2 hb'')).1 this
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer K
  have π0 : π ≠ 0 := by
    rintro rfl
    rw [map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  have s0 : v.valuation K (star π) ≠ 0 := by simpa using π0
  obtain ⟨n, hn⟩ : ∃ n : ℤ, v.valuation K (star π) = WithZero.exp n :=
    ⟨_, (WithZero.exp_log s0).symm⟩
  have gen : ∀ (a : K) (m : ℤ), v.valuation K a = WithZero.exp m →
      v.valuation K (star a) = WithZero.exp (-m * n) := by
    intro a m hm
    have a0 : a ≠ 0 := by
      rintro rfl
      rw [map_zero] at hm
      exact WithZero.exp_ne_zero hm.symm
    have e1 : v.valuation K (π ^ (-m)) = v.valuation K a := by
      rw [map_zpow₀, hπ, ← WithZero.exp_zsmul, hm]; simp
    have e2 : v.valuation K (star (π ^ (-m))) = WithZero.exp (-m * n) := by
      rw [star_zpow₀, map_zpow₀, hn, ← WithZero.exp_zsmul]; simp
    rw [← e2]
    exact le_antisymm (mono _ _ (zpow_ne_zero _ π0) e1.ge) (mono _ _ a0 e1.le)
  have h1 := gen _ _ hn
  rw [star_star, hπ, WithZero.exp_inj] at h1
  have h2 : n ≤ 0 := by
    have := le1 π (by rw [hπ, ← WithZero.exp_zero, WithZero.exp_le_exp]; norm_num)
    rwa [hn, ← WithZero.exp_zero, WithZero.exp_le_exp] at this
  have h3 : n = -1 := by nlinarith
  rcases eq_or_ne a 0 with rfl | a0
  · simp
  · have : v.valuation K a ≠ 0 := by simpa using a0
    have h4 := gen a _ (WithZero.exp_log this).symm
    rw [h4, h3]; simp [WithZero.exp_log this]

theorem normUnit_iff (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (hc : conjIdeal (K := K) v.asIdeal = v.asIdeal) {x : K} {m : ℤ}
    (hx : v.valuation K x = WithZero.exp m) : NormUnit v.asIdeal x ↔ Even m := by
  have key : ∀ (c : K) (k : ℤ), v.valuation K c = WithZero.exp k →
      v.valuation K (star c * c * x) = WithZero.exp (k + k + m) := by
    intro c k hk
    rw [map_mul, map_mul, valuation_star v hc, hk, hx, WithZero.exp_add, WithZero.exp_add]
  constructor
  · rintro ⟨c, c0, h1, h2⟩
    have : v.valuation K c ≠ 0 := by simpa using c0
    have e := key c _ (WithZero.exp_log this).symm
    rw [mem_locR_iff v hc] at h1 h2
    rw [map_inv₀, e, ← WithZero.exp_neg, ← WithZero.exp_zero, WithZero.exp_le_exp] at h2
    rw [e, ← WithZero.exp_zero, WithZero.exp_le_exp] at h1
    exact ⟨-(WithZero.log (v.valuation K c)), by omega⟩
  · rintro ⟨k, rfl⟩
    obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer K
    have π0 : π ≠ 0 := by
      rintro rfl
      rw [map_zero] at hπ
      exact WithZero.exp_ne_zero hπ.symm
    have e1 : v.valuation K (π ^ k) = WithZero.exp (-k) := by
      rw [map_zpow₀, hπ, ← WithZero.exp_zsmul]; simp
    have e := key _ _ e1
    have e0 : -k + -k + (k + k) = 0 := by ring
    rw [e0, WithZero.exp_zero] at e
    refine ⟨π ^ k, zpow_ne_zero _ π0, ?_, ?_⟩
    · rw [mem_locR_iff v hc, e]
    · rw [mem_locR_iff v hc, map_inv₀, e, inv_one]

theorem normUnit_mul {P : Ideal (𝓞 K)} (hP : P.IsMaximal) (hc : conjIdeal (K := K) P = P) {x y : K}
    (hx : x ≠ 0) (hy : y ≠ 0) (h : NormUnit P x ↔ NormUnit P y) : NormUnit P (x * y) := by
  let v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) :=
    ⟨P, hP.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField K)⟩
  have hx' : v.valuation K x ≠ 0 := by simpa using hx
  have hy' : v.valuation K y ≠ 0 := by simpa using hy
  have e1 := normUnit_iff v hc (WithZero.exp_log hx').symm
  have e2 := normUnit_iff v hc (WithZero.exp_log hy').symm
  have e3 := normUnit_iff v hc (x := x * y)
    (m := WithZero.log (v.valuation K x) + WithZero.log (v.valuation K y))
    (by rw [map_mul, WithZero.exp_add, WithZero.exp_log hx', WithZero.exp_log hy'])
  exact e3.2 (Int.even_add.2 (e1.symm.trans (h.trans e2)))

end Val

section Ext

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]

theorem nondeg_of_PD (h : V →ₗ⋆[K] V →ₗ[K] K) (hp : PD h) : h.Nondegenerate := by
  obtain ⟨τ⟩ : Nonempty (K →+* ℂ) := inferInstance
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · by_contra h0
    have := hp τ x h0
    rw [hx x] at this
    simp at this
  · by_contra h0
    have := hp τ x h0
    rw [hx x] at this
    simp at this

def ext (h : V →ₗ⋆[K] V →ₗ[K] K) (β : K) : (V × K) →ₗ⋆[K] (V × K) →ₗ[K] K :=
  LinearMap.mk₂'ₛₗ (starRingEnd K) (RingHom.id K) (fun x y => h x.1 y.1 + β * (star x.2 * y.2))
    (fun x x' y => by simp only [Prod.fst_add, Prod.snd_add, map_add, LinearMap.add_apply, star_add]; ring)
    (fun c x y => by
      simp only [Prod.smul_fst, Prod.smul_snd, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, star_mul',
        starRingEnd_apply]; ring)
    (fun x y y' => by simp only [Prod.fst_add, Prod.snd_add, map_add]; ring)
    (fun c x y => by
      simp only [Prod.smul_fst, Prod.smul_snd, map_smul, smul_eq_mul, RingHom.id_apply]; ring)

omit [NumberField K] in
theorem ext_apply (h : V →ₗ⋆[K] V →ₗ[K] K) (β : K) (x y : V × K) :
    ext h β x y = h x.1 y.1 + β * (star x.2 * y.2) := rfl

omit [NumberField K] in
theorem ext_symm {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) {β : K} (hβ : star β = β) :
    (ext h β).IsSymm := ⟨fun x y => by
  have := hs.eq x.1 y.1
  rw [starRingEnd_apply] at this
  simp only [ext_apply, starRingEnd_apply, star_add, star_mul', star_star, hβ, this]
  ring⟩

theorem ext_PD (hK : IsCMUnram K) {h : V →ₗ⋆[K] V →ₗ[K] K} (hp : PD h) {β : K}
    (hβ : ∀ τ : K →+* ℂ, 0 < (τ β).re) : PD (ext h β) := by
  intro τ x hx
  have e : (τ (β * (star x.2 * x.2))).re = (τ β).re * Complex.normSq (τ x.2) := by
    rw [map_mul, map_mul, hK.2.1, ← Complex.normSq_eq_conj_mul_self, Complex.re_mul_ofReal]
  rw [ext_apply, map_add, Complex.add_re, e]
  have n1 := Complex.normSq_nonneg (τ x.2)
  have b := hβ τ
  by_cases h1 : x.1 = 0
  · have h2 : x.2 ≠ 0 := fun h2 => hx (Prod.ext h1 h2)
    have : 0 < Complex.normSq (τ x.2) := Complex.normSq_pos.2 (by simpa using h2)
    simp only [h1, map_zero, Complex.zero_re, zero_add]
    positivity
  · have := hp τ _ h1
    positivity

theorem exists_basis [FiniteDimensional K V] (hK : IsCMUnram K) {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hs : h.IsSymm) (hp : PD h) : ∃ b : Module.Basis (Fin (Module.finrank K V)) K V,
      star (Matrix.of fun i l => h (b i) (b l)).det = (Matrix.of fun i l => h (b i) (b l)).det ∧
      ∀ τ : K →+* ℂ, 0 < (τ (Matrix.of fun i l => h (b i) (b l)).det).re := by
  obtain ⟨b, hb⟩ := GlobalTheory.HermDiag.exists_orthogonal_basis_fin (c := starRingEnd K) two_ne_zero _
    h.flip (fun x y => hs.eq y x) rfl
  have e : (Matrix.of fun i l => h (b i) (b l)) = Matrix.diagonal fun i => h (b i) (b i) := by
    ext i l
    by_cases hil : i = l
    · subst hil; simp
    · rw [Matrix.diagonal_apply_ne _ hil]; exact hb l i (Ne.symm hil)
  refine ⟨b, ?_⟩
  rw [e, Matrix.det_diagonal]
  refine Finset.prod_induction _ (fun d : K => star d = d ∧ ∀ τ : K →+* ℂ, 0 < (τ d).re) ?_ ?_ ?_
  · rintro x y ⟨x1, x2⟩ ⟨y1, y2⟩
    refine ⟨by rw [star_mul', x1, y1], fun τ => ?_⟩
    have : (τ x).im = 0 := Complex.conj_eq_iff_im.1 (by rw [← hK.2.1, x1])
    rw [map_mul, Complex.mul_re, this, zero_mul, sub_zero]
    exact mul_pos (x2 τ) (y2 τ)
  · simp
  · intro i _
    exact ⟨hs.eq _ _, fun τ => hp τ _ (b.ne_zero i)⟩

theorem exists_intLat [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K) : ∃ M : Submodule (𝓞 K) V, IsIntLat h M := by
  let b := Module.finBasis K V
  obtain ⟨N, hN⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (𝓞 K))
    (fun p : Fin (Module.finrank K V) × Fin (Module.finrank K V) => h (b p.1) (b p.2))
  have N0 : algebraMap (𝓞 K) K N ≠ 0 := by
    simpa using nonZeroDivisors.ne_zero N.2
  let b' := b.unitsSMul fun _ => Units.mk0 _ N0
  have hb' : ∀ i, b' i = algebraMap (𝓞 K) K N • b i := fun i => by
    simp [b', Module.Basis.unitsSMul_apply, Units.smul_def]
  refine ⟨Submodule.span (𝓞 K) (Set.range b'), ⟨Submodule.fg_span (Set.finite_range _), ?_⟩, ?_⟩
  · rw [Submodule.span_span_of_tower, b'.span_eq]
  · intro x hx y hy
    induction hx using Submodule.span_induction with
    | zero => simp
    | add x x' _ _ h1 h2 => rw [map_add, LinearMap.add_apply]; exact Submodule.add_mem _ h1 h2
    | smul a x _ h1 =>
      obtain ⟨t, ht⟩ := LocWitt.star_int a
      rw [← algebraMap_smul K a x, map_smulₛₗ, LinearMap.smul_apply, starRingEnd_apply, ← ht,
        algebraMap_smul]
      exact Submodule.smul_mem _ _ h1
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      induction hy using Submodule.span_induction with
      | zero => simp
      | add y y' _ _ h1 h2 => rw [map_add]; exact Submodule.add_mem _ h1 h2
      | smul a y _ h1 =>
        rw [← algebraMap_smul K a y, map_smul, algebraMap_smul]
        exact Submodule.smul_mem _ _ h1
      | mem y hy =>
        obtain ⟨j, rfl⟩ := hy
        obtain ⟨t, ht⟩ := LocWitt.star_int (K := K) N
        obtain ⟨r, hr⟩ := hN (i, j)
        rw [hb', hb', h.map_smulₛₗ, LinearMap.smul_apply, map_smul, starRingEnd_apply, ← ht,
          algebraMap_smul, algebraMap_smul]
        refine Submodule.smul_mem _ _ ?_
        exact Submodule.mem_one.2 ⟨r, hr⟩

omit [NumberField K] in

theorem exists_basis_ext {n : ℕ} (h : V →ₗ⋆[K] V →ₗ[K] K) (β : K) (b : Module.Basis (Fin n) K V) :
    ∃ (j : ℕ) (c : Module.Basis (Fin j) K (V × K)), (Matrix.of fun i l => ext h β (c i) (c l)).det =
      (Matrix.of fun i l => h (b i) (b l)).det * β := by
  let c := b.prod (Module.Basis.singleton Unit K)
  let e := Fintype.equivFin (Fin n ⊕ Unit)
  refine ⟨_, c.reindex e, ?_⟩
  have e1 : (Matrix.of fun i l => ext h β (c.reindex e i) (c.reindex e l)) =
      (Matrix.fromBlocks (Matrix.of fun i l => h (b i) (b l)) 0 0
        (Matrix.of fun _ _ : Unit => β)).submatrix e.symm e.symm := by
    ext i l
    simp only [Module.Basis.reindex_apply, Matrix.of_apply, Matrix.submatrix_apply]
    generalize e.symm i = i'
    generalize e.symm l = l'
    rcases i' with i' | i' <;> rcases l' with l' | l' <;>
      simp [c, ext_apply, Module.Basis.prod_apply]
  rw [e1, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]
  simp

theorem exists_unimodular [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (hK : IsCMUnram K) {h : V →ₗ⋆[K] V →ₗ[K] K} {β : K} (hs : (ext h β).IsSymm) (hp : PD (ext h β))
    {n : ℕ} (b : Module.Basis (Fin n) K V)
    (hP : ∀ P : Ideal (𝓞 K), P.IsMaximal → conjIdeal (K := K) P = P →
      NormUnit P ((Matrix.of fun i l => h (b i) (b l)).det * β)) :
    ∃ L : Submodule (𝓞 K) (V × K), Submodule.IsLattice K L ∧ IsUnimodular (ext h β) L := by
  have nd := nondeg_of_PD _ hp
  obtain ⟨M, hM⟩ := exists_intLat (ext h β)
  obtain ⟨L, hL, -⟩ := (GlobalTheory.T.exists_maximal_integralHermitianLattice_orthonormal_maximal K (V × K) (ext h β) hK hs nd).1 M hM
  obtain ⟨j, c, hc⟩ := exists_basis_ext h β b
  refine ⟨L, hL.1.1, (locDual (𝓞 K) K (V × K) (ext h β) hs
    (fun r => LocWitt.star_int r) L hL.1.1.fg).2.2 fun P hm => ?_⟩
  by_contra hu
  have := (GlobalTheory.T.maximalHermitianLattice_badPrimes_iff_gramDet K (V × K) (ext h β) hK hs nd L hL j c P hm).1 ⟨hm, hu⟩
  rw [hc] at this
  exact this.2 (hP P hm this.1)

theorem iso_of_ortho {W : Type} [AddCommGroup W] [Module K W] [Module (𝓞 K) V] [Module (𝓞 K) W]
    {h : V →ₗ⋆[K] V →ₗ[K] K} {k : W →ₗ⋆[K] W →ₗ[K] K} {n : ℕ} {I : Submodule (𝓞 K) V}
    {J : Submodule (𝓞 K) W} (hI : IsOrthoLattice h I n) (hJ : IsOrthoLattice k J n) :
    ∃ e : V ≃ₗ[K] W, ∀ x y, k (e x) (e y) = h x y := by
  obtain ⟨a, a1, a2, -, a3⟩ := hI
  obtain ⟨b, b1, b2, -, b3⟩ := hJ
  let A := Module.Basis.mk a1 a2.ge
  let B := Module.Basis.mk b1 b2.ge
  let e := A.equiv B (Equiv.refl _)
  have he : ∀ i, e (A i) = B i := fun i => by simp [e]
  refine ⟨e, fun x y => ?_⟩
  rw [← A.sum_repr x, ← A.sum_repr y]
  simp only [map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply, he]
  simp [A, B, a3, b3]

theorem cancel {W : Type} [AddCommGroup W] [Module K W] [FiniteDimensional K V] [FiniteDimensional K W]
    [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (hK : IsCMUnram K)
    {h : V →ₗ⋆[K] V →ₗ[K] K} {k : W →ₗ⋆[K] W →ₗ[K] K} (hh : PD h) {β : K} (β0 : β ≠ 0)
    (hs : (ext k β).IsSymm) (hp : PD (ext k β)) (hd : Module.finrank K V = Module.finrank K W)
    (φ : (V × K) ≃ₗ[K] (W × K)) (hφ : ∀ x y, ext k β (φ x) (φ y) = ext h β x y) :
    ∃ e : V ≃ₗ[K] W, ∀ x y, k (e x) (e y) = h x y := by
  have u0 : ((0, 1) : W × K) ≠ 0 := by simp
  have w0 : φ (0, 1) ≠ 0 := by simp
  let e1 := LinearEquiv.toSpanNonzeroSingleton K _ _ w0
  let e2 := LinearEquiv.toSpanNonzeroSingleton K _ _ u0
  obtain ⟨g, hg, hg1⟩ := (GlobalTheory.T.witt_extension_totally_definite_hermitian K (W × K) (ext k β) hK hs hp).1 _ _ (e1.symm.trans e2) (by
    intro x y
    obtain ⟨s, rfl⟩ := e1.surjective x
    obtain ⟨t, rfl⟩ := e1.surjective y
    simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
    simp only [e1, e2, LinearEquiv.toSpanNonzeroSingleton_apply, map_smulₛₗ, LinearMap.smul_apply, hφ]
    simp [ext_apply])
  have hg2 : g (φ (0, 1)) = (0, 1) := by
    have := hg1 (e1 1)
    simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply] at this
    simpa [e1, e2] using this
  have iso : ∀ x y, ext k β (g (φ x)) (g (φ y)) = ext h β x y := fun x y => (hg _ _).trans (hφ x y)
  have z : ∀ x : V, (g (φ (x, 0))).2 = 0 := fun x => by
    have := iso (0, 1) (x, 0)
    rw [hg2] at this
    simpa [ext_apply, β0] using this
  let f : V →ₗ[K] W := LinearMap.fst K W K ∘ₗ (φ.trans g).toLinearMap ∘ₗ LinearMap.inl K V K
  have hf : ∀ x y, k (f x) (f y) = h x y := fun x y => by
    have := iso (x, 0) (y, 0)
    rw [ext_apply, ext_apply, z y] at this
    simpa [f] using this
  have inj : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    refine (nondeg_of_PD h hh).1 x fun y => ?_
    rw [← hf, hx]; simp
  exact ⟨LinearMap.linearEquivOfInjective f inj hd, hf⟩

end Ext

theorem main : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → PD h → (∀ (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (k : W →ₗ⋆[K] W →ₗ[K] K), k.IsSymm → PD k → (∃ L : Submodule (𝓞 K) W, Submodule.IsLattice K L ∧ IsUnimodular k L) → ∃ I : Submodule (𝓞 K) W, IsOrthoLattice k I (Module.finrank K W)) → ∀ (V' : Type) [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V'] (h' : V' →ₗ⋆[K] V' →ₗ[K] K), h'.IsSymm → PD h' → Module.finrank K V = Module.finrank K V' → ∀ (M : Submodule (𝓞 K) V) (M' : Submodule (𝓞 K) V'), IsMaxLat h M → IsMaxLat h' M' → badP h M = badP h' M' → ∃ e : V ≃ₗ[K] V', ∀ x y, h' (e x) (e y) = h x y := by
  intro K V _ _ _ _ _ _ _ _ h hK hs hp lan V' _ _ _ _ _ h' hs' hp' hd M M' hM hM' hbad
  obtain ⟨b, d1, d2⟩ := exists_basis hK hs hp
  obtain ⟨b', -, d2'⟩ := exists_basis hK hs' hp'
  obtain ⟨τ⟩ : Nonempty (K →+* ℂ) := inferInstance
  have p1 := fun P => GlobalTheory.T.maximalHermitianLattice_badPrimes_iff_gramDet K V h hK hs (nondeg_of_PD h hp) M hM _ b P
  have p2 := fun P => GlobalTheory.T.maximalHermitianLattice_badPrimes_iff_gramDet K V' h' hK hs' (nondeg_of_PD h' hp') M' hM' _ b' P
  generalize hβ : (Matrix.of fun i l => h (b i) (b l)).det = β at d1 d2 p1
  generalize hβ' : (Matrix.of fun i l => h' (b' i) (b' l)).det = β' at d2' p2
  have β0 : β ≠ 0 := by
    intro h0
    simpa [h0] using d2 τ
  have β0' : β' ≠ 0 := by
    intro h0
    simpa [h0] using d2' τ
  have s1 := ext_symm hs d1
  have s2 := ext_symm hs' d1
  have q1 := ext_PD hK hp d2
  have q2 := ext_PD hK hp' d2
  obtain ⟨I, hI⟩ := lan _ _ s1 q1 (exists_unimodular hK s1 q1 b fun P hP hc => by
    rw [hβ]; exact normUnit_mul hP hc β0 β0 Iff.rfl)
  obtain ⟨J, hJ⟩ := lan _ _ s2 q2 (exists_unimodular hK s2 q2 b' fun P hP hc => by
    rw [hβ']
    refine normUnit_mul hP hc β0' β0 (not_iff_not.1 ?_)
    have a1 := p1 P hP
    have a2 := p2 P hP
    rw [hbad] at a1
    simp only [hc, true_and] at a1 a2
    exact a2.symm.trans a1)
  rw [Module.finrank_prod] at hI hJ
  rw [← hd] at hJ
  obtain ⟨φ, hφ⟩ := iso_of_ortho hI hJ
  exact cancel hK hp β0 s2 q2 hd φ hφ

end GlobalTheory.Mass.SameBad
