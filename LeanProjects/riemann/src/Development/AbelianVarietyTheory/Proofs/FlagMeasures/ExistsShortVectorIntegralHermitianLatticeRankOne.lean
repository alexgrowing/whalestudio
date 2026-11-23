import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLatticeDiscriminantOrderNeZeroUnimodula
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RegulatorLeSumSmallIdealsInClass

open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

namespace GlobalTheory.Mass.ShortVector

open GlobalTheory.Mass.DiscOrder

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

omit [StarRing K] [Module K V] [IsScalarTower (𝓞 K) K V] in

theorem idxN_span (x : V) (S : Submodule (𝓞 K) V) :
    idxN (Submodule.span (𝓞 K) {x}) S =
      Ideal.absNorm (S.comap (LinearMap.toSpanSingleton (𝓞 K) V x) : Ideal (𝓞 K)) := by
  have hr : (Submodule.span (𝓞 K) {x}).toAddSubgroup =
      (⊤ : AddSubgroup (𝓞 K)).map (LinearMap.toSpanSingleton (𝓞 K) V x).toAddMonoidHom := by
    ext y
    simp [Submodule.mem_span_singleton]
  unfold idxN
  rw [hr, ← AddSubgroup.relIndex_comap, AddSubgroup.relIndex_top_right, Ideal.absNorm_apply,
    Submodule.cardQuot_apply]
  rfl

omit [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem nondeg (h : V →ₗ⋆[K] V →ₗ[K] K) (hp : PD h) : h.Nondegenerate := by
  obtain ⟨τ⟩ : Nonempty (K →+* ℂ) := inferInstance
  refine And.intro (fun x hx => ?_) (fun y hy => ?_)
  · by_contra h0
    have hpos := hp τ x h0
    rw [hx x, map_zero, Complex.zero_re] at hpos
    exact lt_irrefl _ hpos
  · by_contra h0
    have hpos := hp τ y h0
    rw [hy y, map_zero, Complex.zero_re] at hpos
    exact lt_irrefl _ hpos

omit [StarRing K] in
theorem span_isLattice (h1 : Module.finrank K V = 1) {x : V} (hx : x ≠ 0) :
    Submodule.IsLattice K (Submodule.span (𝓞 K) {x}) := by
  have : FiniteDimensional K V := Module.finite_of_finrank_eq_succ h1
  refine ⟨Submodule.fg_span_singleton x, ?_⟩
  rw [Submodule.span_span_of_tower]
  exact (finrank_eq_one_iff_of_nonzero x hx).mp h1

private theorem apply_self_ne_zero_and_span_of_finrank_one [FiniteDimensional K V] (h : V →ₗ⋆[K] V →ₗ[K] K)
    (hn : h.Nondegenerate) (h1 : Module.finrank K V = 1) {m : V} (hm : m ≠ 0) :
    h m m ≠ 0 ∧ ∀ y : V, ∃ c : K, c • m = y := by
  have hsp : Submodule.span K {m} = ⊤ := (finrank_eq_one_iff_of_nonzero m hm).mp h1
  have hy : ∀ y : V, ∃ c : K, c • m = y := fun y =>
    Submodule.mem_span_singleton.mp (hsp ▸ Submodule.mem_top)
  refine ⟨fun h0 => hm (hn.1 m fun y => ?_), hy⟩
  obtain ⟨c, rfl⟩ := hy y
  rw [LinearMap.map_smul, h0, smul_zero]

private theorem exists_integer_eq_conj (s : 𝓞 K) :
    ∃ t : 𝓞 K, algebraMap (𝓞 K) K t = starRingEnd K (algebraMap (𝓞 K) K s) :=
  ⟨⟨starRingEnd K (algebraMap (𝓞 K) K s),
    (RingOfIntegers.isIntegral_coe s).map (starRingEnd K).toIntAlgHom⟩, rfl⟩

private theorem smul_mem_dual_span_of_mul_apply_self_integral (h : V →ₗ⋆[K] V →ₗ[K] K) (x : V) (c : K) (t : 𝓞 K)
    (ht : algebraMap (𝓞 K) K t = c * h x x) :
    c • x ∈ dual h (Submodule.span (𝓞 K) {x}) := by
  rw [dualBasic_mem_dual]
  intro y hy
  obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hy
  obtain ⟨s', hs'⟩ := exists_integer_eq_conj s
  rw [← algebraMap_smul K s x, LinearMap.map_smulₛₗ₂, LinearMap.map_smul, smul_eq_mul, smul_eq_mul]
  refine Submodule.mem_one.mpr ⟨s' * t, ?_⟩
  rw [map_mul, ht, hs']

theorem exists_gen [FiniteDimensional K V] (h : V →ₗ⋆[K] V →ₗ[K] K) (hs : h.IsSymm) (hn : h.Nondegenerate)
    (h1 : Module.finrank K V = 1) (M : Submodule (𝓞 K) V) (hM : IsIntLat h M) :
    ∃ (x : V) (b : 𝓞 K) (I : Ideal (𝓞 K)), x ≠ 0 ∧ (b : K) * h x x = 1 ∧ I ≠ ⊥ ∧ (∀ r ∈ I, r • x ∈ M) ∧
      Ideal.absNorm I ^ 2 = Ideal.absNorm (Ideal.span {b}) * discN h M := by
  have : Nontrivial V := Module.nontrivial_of_finrank_eq_succ h1
  have hMne : M ≠ ⊥ := by
    intro hbot
    have h2 := hM.1.span_eq_top
    rw [hbot] at h2
    simp at h2
  obtain ⟨m, hmM, hm0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hMne
  obtain ⟨hmm, hspan⟩ := apply_self_ne_zero_and_span_of_finrank_one h hn h1 hm0
  set x₀ : V := (h m m)⁻¹ • m with hx₀
  have hx0 : x₀ ≠ 0 := smul_ne_zero (inv_ne_zero hmm) hm0
  obtain ⟨hxx, -⟩ := apply_self_ne_zero_and_span_of_finrank_one h hn h1 hx0
  set L : Submodule (𝓞 K) V := Submodule.span (𝓞 K) {x₀} with hL
  have hMd : M ≤ dual h M := fun y hy =>
    (dualBasic_mem_dual h M y).mpr fun z hz => hM.2 z hz y hy
  have hdL : dual h M ≤ L := by
    intro y hy
    obtain ⟨c, rfl⟩ := hspan y
    obtain ⟨u, hu⟩ := Submodule.mem_one.mp ((dualBasic_mem_dual h M _).mp hy m hmM)
    rw [LinearMap.map_smul, smul_eq_mul] at hu
    refine Submodule.mem_span_singleton.mpr ⟨u, ?_⟩
    rw [← algebraMap_smul K u x₀, hu, hx₀, smul_smul, mul_assoc, mul_inv_cancel₀ hmm, mul_one]
  have hML : M ≤ L := hMd.trans hdL
  have hLd : dual h L ≤ dual h M := fun y hy =>
    (dualBasic_mem_dual h M y).mpr fun z hz => (dualBasic_mem_dual h L y).mp hy z (hML hz)
  obtain ⟨b, hb⟩ : ∃ b : 𝓞 K, b • x₀ = (h x₀ x₀)⁻¹ • x₀ :=
    Submodule.mem_span_singleton.mp
      (hdL (hLd (smul_mem_dual_span_of_mul_apply_self_integral h x₀ _ 1 (by rw [map_one, inv_mul_cancel₀ hxx]))))
  have hbK : algebraMap (𝓞 K) K b = (h x₀ x₀)⁻¹ := by
    rw [← algebraMap_smul K b x₀] at hb
    exact smul_left_injective K hx0 hb
  have hcomap : Submodule.comap (LinearMap.toSpanSingleton (𝓞 K) V x₀) (dual h L) =
      Ideal.span {b} := by
    ext r
    simp only [Submodule.mem_comap, LinearMap.toSpanSingleton_apply, Ideal.mem_span_singleton']
    constructor
    · intro hr
      obtain ⟨u, hu⟩ := Submodule.mem_one.mp
        ((dualBasic_mem_dual h L _).mp hr x₀ (Submodule.mem_span_singleton_self x₀))
      refine ⟨u, FaithfulSMul.algebraMap_injective (𝓞 K) K ?_⟩
      rw [map_mul, hu, ← algebraMap_smul K r x₀, LinearMap.map_smul, smul_eq_mul, hbK, mul_assoc,
        mul_inv_cancel₀ hxx, mul_one]
    · rintro ⟨u, rfl⟩
      rw [← algebraMap_smul K (u * b) x₀]
      exact smul_mem_dual_span_of_mul_apply_self_integral h x₀ _ u (by rw [map_mul, hbK, mul_assoc, inv_mul_cancel₀ hxx, mul_one])
  have hLlat : Submodule.IsLattice K L := span_isLattice h1 hx0
  have e1 := idxN_mul hMd hdL
  have e2 := idxN_mul hLd hdL
  have e3 := idxN_dual h hs hn hM.1 _ L hLlat hML rfl
  have e4 := idxN_span x₀ M
  have e5 := idxN_span x₀ (dual h L)
  rw [hcomap] at e5
  refine ⟨x₀, b, Submodule.comap (LinearMap.toSpanSingleton (𝓞 K) V x₀) M, hx0, ?_, ?_, ?_, ?_⟩
  · exact (congrArg (· * h x₀ x₀) hbK).trans (inv_mul_cancel₀ hxx)
  · obtain ⟨t, ht⟩ := Submodule.mem_one.mp (hM.2 m hmM m hmM)
    intro hbot
    have htI : t ∈ Submodule.comap (LinearMap.toSpanSingleton (𝓞 K) V x₀) M := by
      simp only [Submodule.mem_comap, LinearMap.toSpanSingleton_apply]
      rw [← algebraMap_smul K t x₀, ht, hx₀, smul_smul, mul_inv_cancel₀ hmm, one_smul]
      exact hmM
    rw [hbot] at htI
    have ht0 : t = 0 := (Submodule.mem_bot _).mp htI
    rw [ht0, map_zero] at ht
    exact hmm ht.symm
  · intro r hr
    exact hr
  · rw [← e4, ← e5, discN, ← e2, e3, ← e1]
    ring

theorem main : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → PD h → Module.finrank K V = 1 → ∀ M : Submodule (𝓞 K) V, IsIntLat h M → ∃ x ∈ M, x ≠ 0 ∧ ∀ τ : K →+* ℂ, (τ (h x x)).re ≤ (2 * vInv K) * (discN h M : ℝ) ^ ((1 : ℝ) / (2 * fDeg K)) := by
  intro K V _ _ _ _ _ _ _ _ h hK hs hp h1 M hM
  have hn := nondeg h hp
  obtain ⟨x₀, b, I, hx0, hb, hI, hIM, hnorm⟩ := exists_gen h hs hn h1 M hM
  have hTC : IsTotallyComplex K := hK.1
  have hstar := hK.2.1
  have hbK0 : (b : K) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hb
    exact zero_ne_one hb
  have hb0 : b ≠ 0 := by
    rintro rfl
    simp at hbK0
  have hNI : (0 : ℝ) < Ideal.absNorm I := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hNb : (0 : ℝ) < Ideal.absNorm (Ideal.span {b}) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hb0))
  have hnormR : ((Ideal.absNorm I : ℕ) : ℝ) ^ 2 =
      (Ideal.absNorm (Ideal.span {b}) : ℝ) * (discN h M : ℝ) := by
    exact_mod_cast hnorm
  have hD : (0 : ℝ) < discN h M := by
    by_contra hD
    have h0 : (discN h M : ℝ) = 0 := le_antisymm (not_lt.mp hD) (Nat.cast_nonneg _)
    rw [h0, mul_zero] at hnormR
    exact (pow_pos hNI 2).ne' hnormR
  have hf : (0 : ℝ) < fDeg K := by
    unfold fDeg
    exact_mod_cast Fintype.card_pos
  have hf0 := hf.ne'
  have hdK : (0 : ℝ) < |(discr K : ℝ)| := abs_pos.mpr (by exact_mod_cast discr_ne_zero K)
  have hv : 2 * vInv K = |(discr K : ℝ)| ^ ((1 : ℝ) / (2 * (fDeg K : ℝ))) := by
    rw [vInv]
    ring
  have hT : 0 < 2 * vInv K * (discN h M : ℝ) ^ ((1 : ℝ) / (2 * fDeg K)) := by
    rw [hv]
    exact mul_pos (Real.rpow_pos_of_pos hdK _) (Real.rpow_pos_of_pos hD _)
  have hlogT : (fDeg K : ℝ) * Real.log (2 * vInv K * (discN h M : ℝ) ^ ((1 : ℝ) / (2 * fDeg K))) =
      (Real.log |(discr K : ℝ)| + Real.log (discN h M : ℝ)) / 2 := by
    rw [hv, Real.log_mul (Real.rpow_pos_of_pos hdK _).ne' (Real.rpow_pos_of_pos hD _).ne',
      Real.log_rpow hdK, Real.log_rpow hD]
    field_simp
  have hI2 : 2 * Real.log (Ideal.absNorm I : ℝ) =
      Real.log (Ideal.absNorm (Ideal.span {b}) : ℝ) + Real.log (discN h M : ℝ) := by
    rw [← Real.log_mul hNb.ne' hD.ne', ← hnormR, Real.log_pow]
    norm_num
  set T : ℝ := 2 * vInv K * (discN h M : ℝ) ^ ((1 : ℝ) / (2 * fDeg K)) with hTdef
  have hmult : ∀ w : InfinitePlace K, (w.mult : ℝ) = 2 := by
    intro w
    simp [InfinitePlace.mult, InfinitePlace.not_isReal_iff_isComplex.mpr (hTC.isComplex w)]
  have hsum := GlobalTheory.RegulatorClassBound.sum_mult_log K b hb0
  have hc : ∑ w : InfinitePlace K, (w.mult : ℝ) * ((Real.log T + Real.log (w (b : K))) / 2) =
      Real.log ((Ideal.absNorm I : ℝ) * Real.sqrt |(discr K : ℝ)|) := by
    have e : ∀ w : InfinitePlace K, (w.mult : ℝ) * ((Real.log T + Real.log (w (b : K))) / 2) =
        Real.log T + (w.mult : ℝ) * Real.log (w (b : K)) / 2 := by
      intro w
      rw [hmult w]
      ring
    rw [Finset.sum_congr rfl fun w _ => e w, Finset.sum_add_distrib, ← Finset.sum_div, hsum,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      Real.log_mul hNI.ne' (Real.sqrt_pos.mpr hdK).ne', Real.log_sqrt hdK.le]
    have hfc : ((Fintype.card (InfinitePlace K) : ℕ) : ℝ) = (fDeg K : ℝ) := rfl
    rw [hfc]
    linarith [hlogT, hI2]
  obtain ⟨a, haI, ha0, hab⟩ := GlobalTheory.RegulatorClassBound.exists_mem_box K I hI
    (fun w => (Real.log T + Real.log (w (b : K))) / 2) hc
  have haK : algebraMap (𝓞 K) K a ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 K) K)).mpr ha0
  refine ⟨a • x₀, hIM a haI, ?_, fun τ => ?_⟩
  · rw [← algebraMap_smul K a x₀]
    exact smul_ne_zero haK hx0
  · have hh0 : starRingEnd K (h x₀ x₀) = h x₀ x₀ := hs.eq x₀ x₀
    have hreal : (((τ (h x₀ x₀)).re : ℝ) : ℂ) = τ (h x₀ x₀) := by
      apply Complex.conj_eq_iff_re.mp
      rw [← hstar, ← starRingEnd_apply, hh0]
    obtain ⟨r, hrc⟩ : ∃ r : ℝ, (r : ℂ) = τ (h x₀ x₀) := ⟨_, hreal⟩
    have hr : 0 < r := by
      have hpos := hp τ x₀ hx0
      rwa [← hrc, Complex.ofReal_re] at hpos
    have hbr : ‖τ (b : K)‖ * r = 1 := by
      have e := congrArg (fun z => ‖τ z‖) hb
      simp only [map_mul, map_one, norm_mul, norm_one] at e
      rw [← hrc, Complex.norm_real, Real.norm_of_nonneg hr.le] at e
      exact e
    have hw : ∀ z : K, (InfinitePlace.mk τ) z = ‖τ z‖ := fun z => InfinitePlace.apply τ z
    have hbpos : 0 < ‖τ (b : K)‖ := norm_pos_iff.mpr ((map_ne_zero τ).mpr hbK0)
    have ha' := hab (InfinitePlace.mk τ)
    rw [hw, hw] at ha'
    have hsq : ‖τ (a : K)‖ * ‖τ (a : K)‖ < T * ‖τ (b : K)‖ := by
      have hmm := mul_self_lt_mul_self (norm_nonneg _) ha'
      rwa [← Real.exp_add, add_halves, Real.exp_add, Real.exp_log hT, Real.exp_log hbpos] at hmm
    have hvx : (τ (h (a • x₀) (a • x₀))).re = ‖τ (a : K)‖ * ‖τ (a : K)‖ * r := by
      rw [← algebraMap_smul K a x₀, LinearMap.map_smulₛₗ₂, LinearMap.map_smul, smul_eq_mul,
        smul_eq_mul, map_mul, map_mul, starRingEnd_apply, hstar, ← hrc, ← mul_assoc,
        ← Complex.normSq_eq_conj_mul_self, ← Complex.ofReal_mul, Complex.ofReal_re,
        Complex.normSq_eq_norm_sq, sq]
    rw [hvx]
    calc ‖τ (a : K)‖ * ‖τ (a : K)‖ * r ≤ T * ‖τ (b : K)‖ * r :=
          mul_le_mul_of_nonneg_right hsq.le hr.le
      _ = T := by rw [mul_assoc, hbr, mul_one]

end GlobalTheory.Mass.ShortVector
