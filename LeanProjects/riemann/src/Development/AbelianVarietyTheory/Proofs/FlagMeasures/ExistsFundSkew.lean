import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsNormalFormStabilizerMeasure
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsFundOne
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFundIpow
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ConjStableLatticeRealImagCovolumeLe
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemOfForall
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FinrankMulDiscrRpowLeSumSqOfMemTraceDual

open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical nonZeroDivisors

noncomputable section

namespace GlobalTheory.SkewFund

open GlobalTheory.HomCovolume

theorem one_le_covolume {ι : Type} [Fintype ι] (A : Submodule ℤ (ι → ℝ)) [DiscreteTopology A] [IsZLattice ℝ A]
    (h : ∀ x ∈ A, x ≠ 0 → 1 ≤ ‖x‖) : 1 ≤ ZLattice.covolume A volume := by
  by_contra hlt
  rw [not_le] at hlt
  have : Countable A.toAddSubgroup := inferInstanceAs (Countable A)
  have hF : IsAddFundamentalDomain A.toAddSubgroup (latticeDomain A) volume :=
    isAddFundamentalDomain_latticeDomain A volume
  obtain ⟨x, hx0, hx⟩ := exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure hF
    (s := Metric.ball 0 1) (fun x hx => by simpa using hx) (convex_ball _ _) (by
      rw [measure_latticeDomain, Real.volume_pi_ball _ one_pos, Module.finrank_fintype_fun_eq_card,
        mul_one, ENNReal.ofReal_pow zero_le_two, ENNReal.ofReal_ofNat]
      calc _ < 1 * 2 ^ Fintype.card ι :=
            ENNReal.mul_lt_mul_left (by simp) (by simp) (ENNReal.ofReal_lt_one.2 hlt)
        _ = _ := one_mul _)
  exact absurd (h x x.2 (fun h0 => hx0 (Subtype.ext h0))) (by simpa using hx)

theorem imag_covolume {ι : Type} [Fintype ι] (L : Submodule ℤ (ι → ℂ)) {c : ℝ} (hc : HasCov volume L c)
    (hs : ∀ z ∈ L, (fun v => starRingEnd ℂ (z v)) ∈ L) (hn : ∀ z ∈ L, z ≠ 0 → 1 ≤ ‖z‖) :
    ∃ B : Submodule ℤ (ι → ℝ), (∀ y, y ∈ B ↔ (fun v => (⟨0, y v⟩ : ℂ)) ∈ L) ∧
      ∃ b, HasCov volume B b ∧ 1 ≤ b ∧ b ≤ 2 ^ Fintype.card ι * c := by
  let e : ((ι → ℝ) × (ι → ℝ)) ≃L[ℝ] (ι → ℂ) := LinearEquiv.toContinuousLinearEquiv
    { toFun := fun p v => ⟨p.1 v, p.2 v⟩
      invFun := fun z => (fun v => (z v).re, fun v => (z v).im)
      map_add' := fun p q => by ext v; apply Complex.ext <;> simp
      map_smul' := fun c p => by ext v; apply Complex.ext <;> simp
      left_inv := fun p => rfl
      right_inv := fun z => rfl }
  have he : ∀ p v, e p v = ⟨p.1 v, p.2 v⟩ := fun _ _ => rfl
  have hmp : MeasurePreserving e (Measure.prod volume volume) volume :=
    (volume_preserving_pi (ι := ι) fun _ => Complex.volume_preserving_equiv_real_prod.symm).comp
      (volume_measurePreserving_arrowProdEquivProdArrow ℝ ℝ ι).symm
  let M : Submodule ℤ ((ι → ℝ) × (ι → ℝ)) := L.comap (e.toLinearMap.restrictScalars ℤ)
  have hM : ∀ p, p ∈ M ↔ e p ∈ L := fun _ => Iff.rfl
  have : ((volume : Measure (ι → ℝ)).prod (volume : Measure (ι → ℝ))).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure _ _
  obtain ⟨_, _, hcM⟩ := HasCov.of_measurePreserving e hmp hM hc
  let A : Submodule ℤ (ι → ℝ) := M.comap (LinearMap.inl ℤ _ _)
  let B : Submodule ℤ (ι → ℝ) := M.comap (LinearMap.inr ℤ _ _)
  obtain ⟨⟨_, _⟩, ⟨_, _⟩, h⟩ := GlobalTheory.ReImLattice.reflection_stable volume M (fun p hp => by
    rw [hM] at hp ⊢
    convert hs _ hp using 1
    ext v; apply Complex.ext <;> simp [he]) A B (fun _ => Iff.rfl) (fun _ => Iff.rfl)
  have key : ∀ (x : ι → ℝ) (z : ι → ℂ), z ∈ L → (∀ v, ‖z v‖ = ‖x v‖) → x ≠ 0 → 1 ≤ ‖x‖ := by
    intro x z hz hzx hx
    have h1 : ‖z‖ = ‖x‖ := by
      refine le_antisymm ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun v => ?_)
        ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun v => ?_)
      · rw [hzx]; exact norm_le_pi_norm x v
      · rw [← hzx]; exact norm_le_pi_norm z v
    rw [← h1]
    exact hn z hz (by rw [← norm_ne_zero_iff, h1]; exact norm_ne_zero_iff.2 hx)
  have hA : 1 ≤ ZLattice.covolume A volume := one_le_covolume A fun x hx =>
    key x (e (x, 0)) hx fun v => by
      have : e (x, 0) v = (x v : ℂ) := rfl
      rw [this, Complex.norm_real]
  have hB : 1 ≤ ZLattice.covolume B volume := one_le_covolume B fun x hx =>
    key x (e (0, x)) hx fun v => by
      have : e (0, x) v = (x v : ℂ) * Complex.I := by apply Complex.ext <;> simp [he]
      rw [this, norm_mul, Complex.norm_I, mul_one, Complex.norm_real]
  refine ⟨B, fun _ => Iff.rfl, _, ⟨inferInstance, inferInstance, rfl⟩, hB, ?_⟩
  rw [hcM, Module.finrank_fintype_fun_eq_card] at h
  exact (le_mul_of_one_le_left (zero_le_one.trans hB) hA).trans h

theorem prod_norm_sq (K : Type) [Field K] [NumberField K] (hK : IsTotallyComplex K) {ι : Type} [Fintype ι]
    (σ : ι → (K →+* ℂ)) (hσ : ∀ w : InfinitePlace K, ∃! v, InfinitePlace.mk (σ v) = w) (t : K) :
    ∏ v, ‖σ v t‖ ^ 2 = ((|Algebra.norm ℚ t| : ℚ) : ℝ) := by
  rw [← InfinitePlace.prod_eq_abs_norm]
  refine Fintype.prod_bijective _ ((Function.bijective_iff_existsUnique _).2 hσ) _ _ fun v => ?_
  rw [InfinitePlace.mult_isComplex ⟨_, hK.isComplex _⟩, InfinitePlace.apply]

theorem exists_fund_skew : ∀ (K : Type) [Field K] [NumberField K] [StarRing K], Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (ι : Type) [Fintype ι] (σ : ι → (K →+* ℂ)), IsPlaces σ → ∀ (𝔡 : Ideal (𝓞 K)) (n : ℕ), 𝔡 ≠ ⊥ → (∀ x ∈ 𝔡, ∃ y ∈ 𝔡, (y : K) = star (x : K)) → (Ideal.absNorm 𝔡 : ℝ) = (2 * Formalism.HermitianLatticesTheory.vInv K) ^ (2 * Fintype.card ι) → 1 ≤ Formalism.HermitianLatticesTheory.vInv K → ∃ F : Set (ι → ℝ), MeasurableSet F ∧ (∀ a : ι → ℝ, ∃! t : K, (t ∈ ipow 𝔡 (-(2 * (n : ℤ))) ∧ t + star t = 0) ∧ ((fun v => (2 * Formalism.HermitianLatticesTheory.vInv K) ^ (2 * n) * (σ v t).im) + a) ∈ F) ∧ ENNReal.ofReal ((8 * Formalism.HermitianLatticesTheory.vInv K) ^ (-(Fintype.card ι : ℝ))) ≤ volume F ∧ volume F ≤ ENNReal.ofReal ((8 * Formalism.HermitianLatticesTheory.vInv K) ^ (Fintype.card ι : ℝ)) := by
  intro K _ _ _ hK ι _ σ hσ 𝔡 n h𝔡 hs hN hv
  set v₀ := Formalism.HermitianLatticesTheory.vInv K with hv₀
  set c : ℝ := (2 * v₀) ^ (2 * n) with hc
  have hc0 : 0 < c := by positivity
  have h0 : (𝔡 : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.2 h𝔡
  obtain ⟨L₀, hL₀, hcov⟩ := GlobalTheory.IdealFund.exists_lat K hK.1 ι σ hσ.2 _ (zpow_ne_zero (-(2 * (n : ℤ))) h0)
  have hNa : ((FractionalIdeal.absNorm ((𝔡 : FractionalIdeal (𝓞 K)⁰ K) ^ (-(2 * (n : ℤ)))) : ℚ) : ℝ) =
      c⁻¹ ^ (2 * Fintype.card ι) := by
    rw [map_zpow₀, FractionalIdeal.coeIdeal_absNorm]
    push_cast
    rw [hN, _root_.zpow_neg, inv_pow, hc, show (2 * (n : ℤ)) = ((2 * n : ℕ) : ℤ) by push_cast; rfl, _root_.zpow_natCast,
      ← pow_mul, ← pow_mul, mul_comm (2 * n)]
  let f : (ι → ℂ) →ₗ[ℝ] (ι → ℂ) := c⁻¹ • LinearMap.id
  have hf : ∀ z v, f z v = (c : ℂ)⁻¹ * z v := fun _ _ => by simp [f]
  have hdet : LinearMap.det f = c⁻¹ ^ (2 * Fintype.card ι) := by
    rw [LinearMap.det_smul, LinearMap.det_id, mul_one, Module.finrank_pi_fintype]
    simp [mul_comm]
  have hpos : 0 < c⁻¹ ^ (2 * Fintype.card ι) := by positivity
  let L : Submodule ℤ (ι → ℂ) := L₀.comap (f.restrictScalars ℤ)
  have h := HasCov.of_det f (L := L) (by rw [hdet]; exact hpos.ne') (fun _ => Iff.rfl) hcov
  rw [hNa, hdet, abs_of_pos hpos, mul_div_cancel_left₀ _ hpos.ne'] at h
  have hcc : (c : ℂ) ≠ 0 := by exact_mod_cast hc0.ne'
  have hL : ∀ z, z ∈ L ↔ ∃ t ∈ ipow 𝔡 (-(2 * (n : ℤ))), z = fun v => c * σ v t := by
    intro z
    change f z ∈ L₀ ↔ _
    rw [hL₀]
    refine exists_congr fun y => and_congr Iff.rfl ⟨fun h => funext fun v => ?_, fun h v => ?_⟩
    · rw [← h, hf, mul_inv_cancel_left₀ hcc]
    · rw [hf, h, inv_mul_cancel_left₀ hcc]
  obtain ⟨B, hB, b, ⟨_, _, hb⟩, hb1, hb2⟩ := imag_covolume L h (fun z hz => by
    obtain ⟨t, ht, rfl⟩ := (hL z).1 hz
    exact (hL _).2 ⟨star t, IdealPow.star_mem h𝔡 hs ht, funext fun v => by simp [hσ.1]⟩) (fun z hz hz0 => by
    obtain ⟨t, ht, rfl⟩ := (hL z).1 hz
    have ht0 : t ≠ 0 := by rintro rfl; exact hz0 (funext fun v => by simp)
    have h1 : c⁻¹ ^ (2 * Fintype.card ι) ≤ ∏ v, ‖σ v t‖ ^ 2 := by
      rw [← hNa, prod_norm_sq K hK.1 σ hσ.2]
      exact_mod_cast GlobalTheory.absNorm_le_abs_norm_of_mem ht ht0
    by_contra hlt
    rw [not_le, pi_norm_lt_iff one_pos] at hlt
    obtain ⟨u, -⟩ := (hσ.2 (Classical.arbitrary _)).exists
    refine absurd h1 (not_le.2 ?_)
    rw [pow_mul, ← Finset.card_univ, ← Finset.prod_const]
    refine Finset.prod_lt_prod_of_nonempty (fun v _ => pow_pos (norm_pos_iff.2 ((map_ne_zero _).2 ht0)) _)
      (fun v _ => pow_lt_pow_left₀ ?_ (norm_nonneg _) two_ne_zero) ⟨u, Finset.mem_univ _⟩
    have := hlt v
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hc0.le] at this
    rwa [← one_mul c⁻¹, lt_mul_inv_iff₀ hc0, mul_comm])
  obtain ⟨u, -⟩ := (hσ.2 (Classical.arbitrary _)).exists
  have hre : ∀ t : K, t + star t = 0 → ∀ v, (σ v t).re = 0 := fun t ht v => by
    have := congrArg (fun x => (σ v x).re) ht
    simp only [map_add, hσ.1, map_zero, Complex.add_re, Complex.conj_re, Complex.zero_re] at this
    linarith
  have hB' : ∀ y, y ∈ B ↔ ∃ t : K, (t ∈ ipow 𝔡 (-(2 * (n : ℤ))) ∧ t + star t = 0) ∧
      y = fun v => c * (σ v t).im := by
    intro y
    rw [hB, hL]
    constructor
    · rintro ⟨t, ht, hy⟩
      refine ⟨t, ⟨ht, (σ u).injective ?_⟩, funext fun v => by simpa using congrArg Complex.im (congrFun hy v)⟩
      have h1 : (σ u t).re = 0 := by simpa [hc0.ne'] using congrArg Complex.re (congrFun hy u)
      rw [map_add, hσ.1, map_zero]
      apply Complex.ext <;> simp [h1]
    · rintro ⟨t, ⟨ht, ht'⟩, rfl⟩
      exact ⟨t, ht, funext fun v => by apply Complex.ext <;> simp [hre t ht']⟩
  refine ⟨latticeDomain B, measurableSet_latticeDomain B, fun a => ?_, ?_, ?_⟩
  · obtain ⟨z, hz, hu⟩ := existsUnique_add_mem_latticeDomain B a
    obtain ⟨t, ht, hzt⟩ := (hB' z).1 z.2
    refine ⟨t, ⟨ht, by rw [← hzt, add_comm]; exact hz⟩, ?_⟩
    rintro t' ⟨ht', h'⟩
    have h1 := hu ⟨_, (hB' _).2 ⟨t', ht', rfl⟩⟩ (by rw [add_comm] at h'; exact h')
    have h2 := congrFun ((congrArg Subtype.val h1).trans hzt) u
    exact (σ u).injective (Complex.ext (by rw [hre t ht.2, hre t' ht'.2]) (mul_left_cancel₀ hc0.ne' h2))
  · rw [measure_latticeDomain, hb]
    exact ENNReal.ofReal_le_ofReal ((Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by simp)).trans hb1)
  · rw [measure_latticeDomain, hb, Real.rpow_natCast]
    refine ENNReal.ofReal_le_ofReal (hb2.trans ?_)
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by linarith) (by linarith) _

end GlobalTheory.SkewFund
