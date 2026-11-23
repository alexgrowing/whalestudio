import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalToGlobal.Divisibility.Tuples
import Formalism.LocalToGlobal.UnitaryNorms.CharTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderEqIffConjPl
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrdFNonnegOfIsInteger

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

namespace GlobalTheory.Mem.Chr.DetSD

variable {L : Type} [Field L] [NumberField L]

theorem exists_det_ge {N : ℕ} (M : Submodule (𝓞 L) (Fin N → L)) (w : HeightOneSpectrum (𝓞 L)) (k : L) (hk0 : k ≠ 0)
    (hk : k ∈ detSub M) :
    ∃ x : Fin N → Fin N → L, (∀ i, x i ∈ M) ∧ w.valuation L k ≤ w.valuation L (Matrix.of x).det := by
  by_contra hn
  push Not at hn
  have h0 : w.valuation L k ≠ 0 := by simpa using hk0
  have key : ∀ z ∈ detSub M, w.valuation L z < w.valuation L k := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem d hd =>
      obtain ⟨x, hx, rfl⟩ := hd
      exact hn x hx
    | zero => rw [map_zero]; exact zero_lt_iff.2 h0
    | add x y _ _ hx hy => exact Valuation.map_add_lt _ hx hy
    | smul r x _ hx =>
      rw [Algebra.smul_def, map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left' (w.valuation_le_one r)) hx
  exact lt_irrefl _ (key k hk)

theorem coord_le_one {N : ℕ} (M : Submodule (𝓞 L) (Fin N → L)) (w : HeightOneSpectrum (𝓞 L))
    (x : Fin N → Fin N → L) (hx : ∀ i, x i ∈ M) (hd : (Matrix.of x).det ≠ 0)
    (hmax : ∀ z ∈ detSub M, w.valuation L z ≤ w.valuation L (Matrix.of x).det) (m : Fin N → L) (hm : m ∈ M)
    (j : Fin N) : w.valuation L (Matrix.vecMul m (Matrix.of x)⁻¹ j) ≤ 1 := by
  have hu : IsUnit (Matrix.of x).det := IsUnit.mk0 _ hd
  have h1 := congrFun (Matrix.det_smul_inv_vecMul_eq_cramer_transpose (Matrix.of x) m hu) j
  rw [Matrix.cramer_transpose_apply] at h1
  have h2 : ((Matrix.of x).updateRow j m).det ∈ detSub M := by
    refine det_mem_detSub (Function.update x j m) fun i => ?_
    by_cases h : i = j
    · subst h; simpa using hm
    · simpa [Function.update_of_ne h] using hx i
  have h3 := hmax _ h2
  rw [← h1, Pi.smul_apply, smul_eq_mul, map_mul] at h3
  have h0 : 0 < w.valuation L (Matrix.of x).det := zero_lt_iff.2 (by simpa using hd)
  exact (mul_le_iff_le_one_right h0).1 h3

theorem exists_den_prime {V : Type} [AddCommGroup V] [Module (𝓞 L) V] {N : ℕ} (M : Submodule (𝓞 L) V) (hM : M.FG)
    (w : HeightOneSpectrum (𝓞 L)) (f : Fin N → V → L) (hadd : ∀ j x y, f j (x + y) = f j x + f j y)
    (hsm : ∀ j (r : 𝓞 L) x, ∃ r' : 𝓞 L, f j (r • x) = r' • f j x)
    (hf : ∀ j, ∀ m ∈ M, w.valuation L (f j m) ≤ 1) :
    ∃ s : 𝓞 L, s ∉ w.asIdeal ∧ ∀ j, ∀ m ∈ M, (s : L) * f j m ∈ (algebraMap (𝓞 L) L).range := by
  classical
  obtain ⟨t, rfl⟩ := hM
  have := w.isPrime
  choose n d h using fun p : Fin N × t => w.exists_primeCompl_mul_eq_of_integer (f p.1 p.2)
    (hf p.1 p.2 (Submodule.subset_span p.2.2))
  refine ⟨((∏ p, d p : w.asIdeal.primeCompl) : 𝓞 L), (∏ p, d p).2, fun j m hm => ?_⟩
  induction hm using Submodule.span_induction with
  | mem x hx =>
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ (j, (⟨x, hx⟩ : t)))]
    refine ⟨((∏ p ∈ Finset.univ.erase (j, (⟨x, hx⟩ : t)), d p : w.asIdeal.primeCompl) : 𝓞 L) * n (j, ⟨x, hx⟩), ?_⟩
    rw [map_mul, ← h]
    simp only [Submonoid.coe_mul]
    push_cast
    simp only [RingOfIntegers.coe_eq_algebraMap]
    ring
  | zero =>
    obtain ⟨r, hr⟩ := hsm j 0 0
    have h0 : f j 0 = 0 := by simpa using hadd j 0 0
    rw [h0, mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [hadd, mul_add]; exact add_mem hx hy
  | smul r x _ hx =>
    obtain ⟨r', hr⟩ := hsm j r x
    rw [hr, Algebra.smul_def, mul_left_comm]
    exact mul_mem ⟨r', rfl⟩ hx

variable [StarRing L]

theorem star_integer (r : 𝓞 L) : ∃ r' : 𝓞 L, (r' : L) = star (r : L) :=
  ⟨RingOfIntegers.mapRingEquiv (starRingAut : RingAut L) r, rfl⟩

theorem star_mul_integer {N : ℕ} (M : Submodule (𝓞 L) (Fin N → L))
    (hM : ∀ y ∈ M, ∀ x ∈ M, stdH L N x y ∈ (algebraMap (𝓞 L) L).range) (a b : L) (ha : a ∈ detSub M)
    (hb : b ∈ detSub M) : star a * b ∈ (algebraMap (𝓞 L) L).range := by
  induction ha using Submodule.span_induction with
  | mem d hd =>
    obtain ⟨x, hx, rfl⟩ := hd
    induction hb using Submodule.span_induction with
    | mem d hd =>
      obtain ⟨y, hy, rfl⟩ := hd
      have e : star (Matrix.of x).det * (Matrix.of y).det = (Matrix.of fun i j => stdH L N (x j) (y i)).det := by
        rw [← Matrix.det_conjTranspose, mul_comm, ← Matrix.det_mul]
        congr 1
        ext i j
        simp [Matrix.mul_apply, stdH, mul_comm]
      rw [e]
      exact Formalism.L2.LamCM.A2.isInteger_det _ fun i j => hM _ (hy i) _ (hx j)
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
    | smul r x _ hx => rw [Algebra.smul_def, mul_left_comm]; exact mul_mem ⟨r, rfl⟩ hx
  | zero => simp
  | add x y _ _ hx hy => rw [star_add, add_mul]; exact add_mem hx hy
  | smul r x _ hx =>
    obtain ⟨r', hr⟩ := star_integer r
    rw [Algebra.smul_def, star_mul', mul_assoc]
    exact mul_mem ⟨r', hr⟩ hx

theorem ordSub_add_eq_zero {N : ℕ} (M : Submodule (𝓞 L) (Fin N → L)) (hM : IsSDLat L N M)
    (w w' : HeightOneSpectrum (𝓞 L)) (hw : ∀ x : L, w'.valuation L (star x) = w.valuation L x) :
    ordSub w (detSub M) + ordSub w' (detSub M) = 0 := by
  obtain ⟨hfg, hsp, hsd⟩ := hM
  have hl := (ordSub_detSub_lattice L N M hfg hsp).2.1
  obtain ⟨⟨k, hk, ek⟩, hkl⟩ := hl w
  obtain ⟨⟨k', hk', ek'⟩, hkl'⟩ := hl w'
  have nz : ∀ (v : HeightOneSpectrum (𝓞 L)) (a : Lˣ), v.valuation L (a : L) ≠ 0 := fun v a => by simp
  apply le_antisymm
  · obtain ⟨x, hx, hxk⟩ := exists_det_ge M w k k.ne_zero hk
    have hd : (Matrix.of x).det ≠ 0 := by
      intro h
      rw [h, map_zero] at hxk
      exact nz w k (le_zero_iff.1 hxk)
    have hmax : ∀ z ∈ detSub M, w.valuation L z ≤ w.valuation L k := by
      intro z hz
      by_cases h0 : z = 0
      · simp [h0]
      · have h1 := hkl ⟨Units.mk0 z h0, hz, rfl⟩
        rw [← ek] at h1
        exact (WithZero.log_le_log (nz w (Units.mk0 z h0)) (nz w k)).1 (neg_le_neg_iff.1 h1)
    have hdk : w.valuation L (Matrix.of x).det = w.valuation L k := le_antisymm (hmax _ (det_mem_detSub x hx)) hxk
    have hc := coord_le_one M w x hx hd (fun z hz => hdk ▸ hmax z hz)
    set Y : Matrix (Fin N) (Fin N) L := ((Matrix.of x)⁻¹).conjTranspose with hY
    have hf : ∀ j m, stdH L N m (Y j) = star (Matrix.vecMul m (Matrix.of x)⁻¹ j) := by
      intro j m
      simp [stdH, hY, Matrix.vecMul, dotProduct]
    obtain ⟨s, hs, hint⟩ := exists_den_prime M hfg w' (fun j m => stdH L N m (Y j))
      (fun j a b => by simp [stdH, add_mul, Finset.sum_add_distrib])
      (fun j r a => by
        obtain ⟨r', hr⟩ := star_integer r
        refine ⟨r', ?_⟩
        have hr' : algebraMap (𝓞 L) L r' = star (algebraMap (𝓞 L) L r) := hr
        simp [stdH, Algebra.smul_def, hr', Finset.mul_sum, mul_assoc])
      (fun j m hm => by
        show w'.valuation L (stdH L N m (Y j)) ≤ 1
        rw [hf, hw]; exact hc m hm j)
    have hsY : ∀ j, ((s : L) • Y) j ∈ M := fun j => (hsd _).2 fun m hm => by
      have := hint j m hm
      convert this using 1
      simp [stdH, Finset.mul_sum, mul_left_comm]
    have hmem : ((s : L) • Y).det ∈ detSub M := det_mem_detSub (fun j => ((s : L) • Y) j) hsY
    have hsv : w'.valuation L (s : L) = 1 :=
      le_antisymm (w'.valuation_le_one s) (not_lt.1 fun h => hs ((w'.valuation_lt_one_iff_mem s).1 h))
    have hval : w'.valuation L ((s : L) • Y).det = (w.valuation L k)⁻¹ := by
      rw [Matrix.det_smul, map_mul, map_pow, hsv, one_pow, one_mul, hY, Matrix.det_conjTranspose, hw,
        Matrix.det_nonsing_inv, Ring.inverse_eq_inv', map_inv₀, hdk]
    have h0 : ((s : L) • Y).det ≠ 0 := by
      intro h
      rw [h, map_zero] at hval
      exact inv_ne_zero (nz w k) hval.symm
    have h1 := hkl' ⟨Units.mk0 _ h0, hmem, rfl⟩
    have h2 : ordF w' (Units.mk0 _ h0) = -ordF w k := by
      unfold ordF
      rw [Units.val_mk0, hval, WithZero.log_inv]
    omega
  · have h1 := star_mul_integer M (fun y hy => (hsd y).1 hy) k k' hk hk'
    have h2 := DetOrd.ordF_nonneg_of_isInteger w' (star k * k') h1
    rw [DetOrd.ordF_mul'] at h2
    have h3 : ordF w' (star k) = ordF w k := by
      unfold ordF
      rw [Units.coe_star, hw]
    omega

end GlobalTheory.Mem.Chr.DetSD

namespace GlobalTheory.Mem.Chr

open Classical in

theorem ordSub_detSub_selfDual : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (N : ℕ), letI := H.cmStar; ∀ (M : SDLat H.E N) (w w' : HeightOneSpectrum (𝓞 H.E)), IsConjPl H w w' → ordSub w (detSub M.1) + ordSub w' (detSub M.1) = 0 := by
  intro R H N
  letI := H.cmStar
  intro M w w' h
  have hc : ConjPl H.conj.toRingEquiv w w' := (conjPl_main.2.1 R H w w').1 h
  refine DetSD.ordSub_add_eq_zero M.1 M.2 w w' fun x => ?_
  have := H.isCMField_hostE
  have e : star x = H.conj x :=
    H.φ₀.injective ((NumberField.IsCMField.complexEmbedding_complexConj _ H.φ₀ x).trans
      (H.conjE_apply H.φ₀ x).symm)
  rw [e]
  exact hc x

end GlobalTheory.Mem.Chr
