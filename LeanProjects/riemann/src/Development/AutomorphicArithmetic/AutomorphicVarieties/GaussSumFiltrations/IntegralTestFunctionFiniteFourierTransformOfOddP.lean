import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EvenPos
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.IntMatrixIsometryPrimeOrderLatticeStability
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.WeilIndexConstantCongruentOneModPrime
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.IsDelNeZeroCoprimeDenominatorsDifferentGenerator
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.NormSumFreeOrbitsLeInvPrime
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EvenPosGramFormIntegralLatticeProperties
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.DualLatticeIndexEqDiscrPowMulDetPow
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries.GoodInv

theorem exists_place (F : Type) [Field F] [NumberField F] (p : ℕ) (hp : p.Prime) :
    ∃ w : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∈ w.asIdeal := by
  have hu : ¬ IsUnit ((p : ℕ) : 𝓞 F) := by
    intro h
    have h1 : IsUnit (algebraMap ℤ (𝓞 F) (p : ℤ)) := by simpa using h
    have h2 : IsUnit (p : ℤ) := isUnit_of_map_unit _ _ h1
    exact (Nat.prime_iff_prime_int.mp hp).not_unit h2
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal (Ideal.span {((p : ℕ) : 𝓞 F)}) (by
    rwa [Ne, Ideal.span_singleton_eq_top])
  have hmem : ((p : ℕ) : 𝓞 F) ∈ M := hle (Ideal.subset_span rfl)
  refine ⟨⟨M, hM.isPrime, ?_⟩, hmem⟩
  rintro rfl
  have : ((p : ℕ) : 𝓞 F) = 0 := by simpa using hmem
  exact hp.ne_zero (by exact_mod_cast this)

theorem val_nat {F : Type} [Field F] [NumberField F] {p n : ℕ} (h : n.Coprime p)
    (w : HeightOneSpectrum (𝓞 F)) (hw : ((p : ℕ) : 𝓞 F) ∈ w.asIdeal) : w.valuation F (n : F) = 1 := by
  have h1 : (n : F) = algebraMap (𝓞 F) F (n : 𝓞 F) := by simp
  rw [h1, HeightOneSpectrum.valuation_eq_one_iff_notMem]
  intro hn
  have hc : IsCoprime ((n : ℕ) : 𝓞 F) ((p : ℕ) : 𝓞 F) := Nat.Coprime.cast h
  obtain ⟨a, b, hab⟩ := hc
  exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (hab ▸ add_mem (Ideal.mul_mem_left _ _ hn) (Ideal.mul_mem_left _ _ hw)))

theorem norm_et {F : Type} [Field F] [NumberField F] {p : ℕ} [Fact p.Prime] (ι : Qbar p ≃+* ℂ) (x : F) :
    ‖ι.symm (et x)‖ = 1 := by
  set q : ℚ := Algebra.trace ℚ F x with hq
  have h : et x ^ q.den = 1 := by
    unfold et
    rw [← Complex.exp_nat_mul, ← hq]
    have h1 : (q.den : ℂ) * (q : ℂ) = (q.num : ℂ) := by exact_mod_cast Rat.den_mul_eq_num q
    have : (q.den : ℂ) * (2 * Real.pi * Complex.I * (q : ℂ)) = (q.num : ℂ) * (2 * Real.pi * Complex.I) := by
      rw [← h1]; ring
    rw [this, Complex.exp_int_mul_two_pi_mul_I]
  have h2 : ‖ι.symm (et x)‖ ^ q.den = 1 := by
    rw [← norm_pow, ← map_pow, h, map_one, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) q.den_nz).1 h2

theorem exists_perm {V : Type} [AddCommGroup V] {A B : AddSubgroup V} {T : Finset V} (hT : IsReps A B T)
    (s : V →+ V) (hA : ∀ x, s x ∈ A ↔ x ∈ A) (hB : ∀ x ∈ B, s x ∈ B) :
    ∃ σ : V → V, (∀ x ∈ T, σ x ∈ T ∧ s x - σ x ∈ A) ∧ Set.BijOn σ T T ∧
      ∀ n : ℕ, ∀ x ∈ T, s^[n] x = x → σ^[n] x = x := by
  classical
  have huniq : ∀ x ∈ T, ∀ y ∈ T, x - y ∈ A → x = y := fun x hx y hy h =>
    (hT.2 x (hT.1 x hx)).unique ⟨hx, by simpa using A.zero_mem⟩ ⟨hy, h⟩
  have hex : ∀ x, ∃ y, x ∈ T → y ∈ T ∧ s x - y ∈ A := fun x => by
    by_cases hx : x ∈ T
    · obtain ⟨y, hy, -⟩ := hT.2 _ (hB x (hT.1 x hx))
      exact ⟨y, fun _ => hy⟩
    · exact ⟨x, fun h => absurd h hx⟩
  choose σ hσ using hex
  have hit : ∀ n : ℕ, ∀ x ∈ T, σ^[n] x ∈ T ∧ s^[n] x - σ^[n] x ∈ A := by
    intro n x hx
    induction n with
    | zero => exact ⟨hx, by simpa using A.zero_mem⟩
    | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      refine ⟨(hσ _ ih.1).1, ?_⟩
      have h1 := (hA _).2 ih.2
      have h2 := (hσ _ ih.1).2
      rw [map_sub] at h1
      simpa using A.add_mem h1 h2
  refine ⟨σ, hσ, ?_, fun n x hx h => ?_⟩
  · have hm : Set.MapsTo σ (T : Set V) T := fun x hx => (hσ x hx).1
    refine (T.finite_toSet.injOn_iff_bijOn_of_mapsTo hm).1 fun x hx y hy h => huniq x hx y hy ?_
    rw [← hA, map_sub]
    have := A.sub_mem (hσ x hx).2 (hσ y hy).2
    rw [h] at this
    simpa using this
  · have := hit n x hx
    rw [h] at this
    exact (huniq _ hx _ this.1 this.2).symm

section Lat

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] [DecidableEq κ]

theorem smul_mem_LL {a : F} (ha : IsIntegral ℤ a) {x : κ → F} (hx : x ∈ LL F κ) : a • x ∈ LL F κ :=
  fun i hi => ha.mul (hx i hi)

theorem BF_smul_right (G : Matrix κ κ ℤ) (a : F) (x y : κ → F) : BF G x (a • y) = a * BF G x y := by
  simp only [BF, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem BF_add_right (G : Matrix κ κ ℤ) (x y z : κ → F) : BF G x (y + z) = BF G x y + BF G x z := by
  simp only [BF, Matrix.mulVec_add, dotProduct_add]

theorem isSB_wT {p : ℕ} (hp : p.Prime) {δ : F} (hδ : IsDel p δ) {G S : Matrix κ κ ℤ} {t : ℕ} (hL : LatD p G S t)
    (Φ : (κ → F) → ℂ) {N : ℕ} {T : Finset (κ → F)} {c : F} (hN : 0 < N) (hNp : N.Coprime p)
    (hT : ∀ x ∈ T, x ∈ aL κ (N : F)⁻¹) (hc : PUnit p (c / δ)) (k : ℕ) :
    ∃ M : ℕ, 0 < M ∧ M.Coprime p ∧ IsSB M (wT G k t (N : F) c T Φ) := by
  obtain ⟨hδ0, hint, htr, d, -, hd, -, -, hdu⟩ := GlobalTheory.T.isDel_ne_zero_coprime_denominators_different_generator F p hp δ hδ
  obtain ⟨-, hsm, hadd, hI, -, haL, het, -⟩ := GlobalTheory.T.evenPos_gramForm_integral_lattice_properties F κ G hL.pos
  obtain ⟨hlev, -⟩ := GlobalTheory.T.dualLattice_index_eq_discr_pow_mul_det_pow F κ G hL.pos
  obtain ⟨-, -, -, ht⟩ := GlobalTheory.T.intMatrix_isometry_prime_order_lattice_stability F p hp κ G S t hL
  have htp : t.Coprime p := ((Nat.Prime.coprime_iff_not_dvd hp).2 (by exact_mod_cast ht)).symm
  obtain ⟨w₀, hw₀⟩ := exists_place F p hp
  have hc0 : c ≠ 0 := by
    rintro rfl
    simpa using hc w₀ hw₀
  have hd0 : (d : F) ≠ 0 := by
    intro h
    simpa [h] using hdu w₀ hw₀
  have ht0 : (t : F) ≠ 0 := by
    intro h
    simpa [h] using val_nat htp w₀ hw₀
  have hN0 : (N : F) ≠ 0 := by exact_mod_cast hN.ne'
  obtain ⟨N₁, h1, h1p, h1i⟩ := hint (c / ((t : F) ^ 2 * d * N)) (by
    intro w hw
    have e : c / ((t : F) ^ 2 * d * N) = (c / δ) / ((t : F) ^ 2 * (d / δ) * N) := by field_simp
    rw [e, map_div₀, map_mul, map_mul, map_pow, hc w hw, hdu w hw, val_nat htp w hw, val_nat hNp w hw]
    simp)
  obtain ⟨N₂, h2, h2p, h2i⟩ := htr c⁻¹ (by
    intro w hw
    have e : δ * c⁻¹ = (c / δ)⁻¹ := by field_simp
    rw [e, map_inv₀, hc w hw]
    simp)
  have hN1 : (N₁ : F) ≠ 0 := by exact_mod_cast h1.ne'
  have hN2 : (N₂ : F) ≠ 0 := by exact_mod_cast h2.ne'
  have hnat : ∀ n : ℕ, IsIntegral ℤ (n : F) := fun n => by
    simpa using (isIntegral_algebraMap (R := ℤ) (A := F) (x := (n : ℤ)))
  refine ⟨N₁ * N₂ * N, by positivity, Nat.Coprime.mul_left (Nat.Coprime.mul_left h1p h2p) hNp, fun y hy => ?_,
    fun y l hl => ?_⟩
  · have hyd : ((N : F) / c) • y ∈ dualL F G := by
      by_contra h
      exact hy (by simp [wT, h])
    have h3 := smul_mem_LL ((hnat (N₂ * N)).mul h1i) (hlev _ hyd d hd)
    refine (haL _ _).2 ⟨_, h3, ?_⟩
    rw [smul_smul, smul_smul, smul_smul, hL.det]
    have e : ((N₁ * N₂ * N : ℕ) : F)⁻¹ * (((N₂ * N : ℕ) : F) * (N₁ * (c / ((t : F) ^ 2 * d * N)))) *
        ((((t : ℤ) ^ 2 : ℤ) : F) * d) * (N / c) = 1 := by
      push_cast
      field_simp
    rw [e, one_smul]
  · obtain ⟨l₀, hl₀, rfl⟩ := (haL _ _).1 hl
    have hld : ((N : F) / c) • (((N₁ * N₂ * N : ℕ) : F) • l₀) ∈ dualL F G := by
      intro l' hl'
      obtain ⟨n, hn⟩ := h2i _ ((hnat (N₁ * N * N)).mul ((hI l₀ hl₀).2 l' hl'))
      refine ⟨n, ?_⟩
      rw [← hn, (hsm _ _ _).1, (hsm _ _ _).1]
      congr 1
      push_cast
      field_simp
    have hiff : ((N : F) / c) • (y + ((N₁ * N₂ * N : ℕ) : F) • l₀) ∈ dualL F G ↔ ((N : F) / c) • y ∈ dualL F G := by
      rw [smul_add]
      exact (dualL F G).add_mem_cancel_right hld
    unfold wT
    rw [hiff]
    split_ifs with h
    · congr 1
      refine Finset.sum_congr rfl fun x hx => ?_
      obtain ⟨x₀, hx₀, rfl⟩ := (haL _ _).1 (hT x hx)
      rw [hadd, add_div, (het _ _).1, ((het (BF _ (_ • l₀) _ / c) 0).2.2.1).2, mul_one]
      obtain ⟨n, hn⟩ := h2i _ ((hnat N₁).mul ((hI l₀ hl₀).2 x₀ hx₀))
      refine ⟨n, ?_⟩
      rw [← hn, (hsm _ _ _).1, BF_smul_right]
      congr 1
      push_cast
      field_simp
    · rfl

end Lat

theorem good_wT : ∀ (F : Type) [Field F] [NumberField F] (p : ℕ) [Fact p.Prime] (ι : Qbar p ≃+* ℂ), p ≠ 2 → ∀ δ : F, IsDel p δ → ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (G S : Matrix κ κ ℤ) (t : ℕ), LatD p G S t → ∀ (Φ : (κ → F) → ℂ) (N : ℕ) (T : Finset (κ → F)) (c : F), Good ι S Φ → 0 < N → N.Coprime p → IsSB N Φ → IsReps (aL κ (N : F)) (aL κ (N : F)⁻¹) T → 0 ∈ T → PUnit p (c / δ) → Good ι S (wT G (p - 1) t (N : F) c T Φ) := by
  intro F _ _ p hpf ι hp2 δ hδ κ _ _ G S t hL Φ N T c hΦ hN hNp hSB hT h0 hc
  classical
  have hp : p.Prime := hpf.out
  obtain ⟨-, hinv, hint, hzero⟩ := hΦ
  obtain ⟨-, hsm, -, -, -, haL, het, -⟩ := GlobalTheory.T.evenPos_gramForm_integral_lattice_properties F κ G hL.pos
  obtain ⟨hiso, hS, hfree, -⟩ := GlobalTheory.T.intMatrix_isometry_prime_order_lattice_stability F p hp κ G S t hL
  have hC := GlobalTheory.T.weil_index_constant_congruent_one_mod_prime F p ι hp2 δ c hδ hc t N hNp hL.cong
  have hp1 : (p : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hp.one_le)
  have hC1 : ‖ι.symm (wC (p - 1) t (N : F) c)‖ ≤ 1 := by
    have := IsUltrametricDist.norm_add_le_max (ι.symm (wC (p - 1) t (N : F) c) - 1) 1
    rw [sub_add_cancel, norm_one] at this
    exact this.trans (max_le (hC.trans hp1) le_rfl)
  let s : (κ → F) →+ (κ → F) := (Matrix.mulVecLin (S.map (Int.cast : ℤ → F))).toAddMonoidHom
  have hs : ∀ x, s x = (S.map (Int.cast : ℤ → F)) *ᵥ x := fun _ => rfl
  obtain ⟨σ, hσ, hbij, hit⟩ := exists_perm hT s (fun x => (hS x).2.2.2 _) (fun x hx => ((hS x).2.2.2 _).2 hx)
  have huniq : ∀ x ∈ T, ∀ y ∈ T, x - y ∈ aL κ (N : F) → x = y := fun x hx y hy h =>
    (hT.2 x (hT.1 x hx)).unique ⟨hx, by simpa using (aL κ (N : F)).zero_mem⟩ ⟨hy, h⟩
  have hΦσ : ∀ x ∈ T, Φ (σ x) = Φ x := fun x hx => by
    rw [← hinv x, ← hSB.2 (σ x) _ (hσ x hx).2, hs, add_sub_cancel]
  refine ⟨isSB_wT hp hδ hL Φ hN hNp hT.1 hc _, fun y => ?_, fun y => ?_, ?_⟩
  · have hiff : ((N : F) / c) • (S.map (Int.cast : ℤ → F) *ᵥ y) ∈ dualL F G ↔ ((N : F) / c) • y ∈ dualL F G := by
      rw [← Matrix.mulVec_smul]
      exact (hS _).2.2.1
    unfold wT
    rw [hiff]
    split_ifs with h
    · congr 1
      symm
      refine Finset.sum_nbij σ (fun x hx => (hσ x hx).1) hbij.injOn hbij.surjOn fun x hx => ?_
      obtain ⟨l, hl, e⟩ := (haL _ _).1 (hσ x hx).2
      have e' : S.map (Int.cast : ℤ → F) *ᵥ x = σ x + (N : F) • l := by rw [← e, hs, add_sub_cancel]
      rw [hΦσ x hx, ← (hiso y x).1, e', BF_add_right, add_div, (het _ _).1, ((het (BF _ _ (_ • l) / c) 0).2.2.1).2, mul_one]
      obtain ⟨n, hn⟩ := hiff.2 h l hl
      refine ⟨n, ?_⟩
      rw [← hn, (hsm _ _ _).1, BF_smul_right]
      congr 1
      ring
    · rfl
  · unfold wT
    split_ifs with h
    · rw [map_mul, norm_mul, map_sum]
      refine mul_le_one₀ hC1 (norm_nonneg _) ?_
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun x _ => ?_
      rw [map_mul, norm_mul, norm_et, mul_one]
      exact hint x
    · simp
  · have e0 : wT G (p - 1) t (N : F) c T Φ 0 = wC (p - 1) t (N : F) c * (Φ 0 + ∑ x ∈ T.erase 0, Φ x) := by
      unfold wT
      rw [if_pos (by simpa using (dualL F G).zero_mem), Finset.add_sum_erase _ _ h0]
      congr 1
      refine Finset.sum_congr rfl fun x _ => ?_
      simp [BF, et]
    have hσ0 : σ 0 = 0 := (huniq _ h0 _ (hσ 0 h0).1 (by simpa using (hσ 0 h0).2)).symm
    have horb := GlobalTheory.T.norm_sum_free_orbits_le_inv_prime p ι _ σ (T.erase 0) Φ
      (fun x hx => by
        obtain ⟨hx0, hx⟩ := Finset.mem_erase.1 hx
        exact Finset.mem_erase.2 ⟨fun h => hx0 (hbij.injOn hx h0 (h.trans hσ0.symm)), (hσ x hx).1⟩)
      (fun x hx => hit p x (Finset.mem_of_mem_erase hx) (hS x).1)
      (fun x hx h => by
        obtain ⟨hx0, hx⟩ := Finset.mem_erase.1 hx
        have h1 := (hσ x hx).2
        rw [h] at h1
        exact hx0 (huniq x hx 0 h0 (by simpa using hfree N x hN hNp (hT.1 x hx) h1)))
      (fun x hx => hΦσ x (Finset.mem_of_mem_erase hx)) (fun x _ => hint x)
    rw [e0, map_mul, map_add]
    set a := ι.symm (wC (p - 1) t (N : F) c)
    set b := ι.symm (Φ 0)
    set r := ι.symm (∑ x ∈ T.erase 0, Φ x)
    have e : a * (b + r) - 1 = (a - 1) + (a * (b - 1) + a * r) := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hC ?_)
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) hC1).trans hzero
    · rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) hC1).trans horb

end GlobalTheory.HilbertThetaSeries.GoodInv

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_test_function_finite_fourier_transform_of_odd_prime : ∀ (F : Type) [Field F] [NumberField F] (p : ℕ) [Fact p.Prime] (ι : Qbar p ≃+* ℂ), p ≠ 2 → ∀ δ : F, IsDel p δ → ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (G S : Matrix κ κ ℤ) (t : ℕ), LatD p G S t → ∀ (Φ : (κ → F) → ℂ) (N : ℕ) (T : Finset (κ → F)) (c : F), Good ι S Φ → 0 < N → N.Coprime p → IsSB N Φ → IsReps (aL κ (N : F)) (aL κ (N : F)⁻¹) T → 0 ∈ T → PUnit p (c / δ) → Good ι S (wT G (p - 1) t (N : F) c T Φ) := by
  first | exact @GlobalTheory.HilbertThetaSeries.GoodInv.good_wT | exact GlobalTheory.HilbertThetaSeries.GoodInv.good_wT | (intros; apply GlobalTheory.HilbertThetaSeries.GoodInv.good_wT <;> assumption)
