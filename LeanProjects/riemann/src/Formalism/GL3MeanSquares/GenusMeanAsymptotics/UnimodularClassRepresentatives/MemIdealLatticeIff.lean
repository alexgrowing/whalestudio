import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.TendstoTsumDivPow
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.AbsNormEqProdOfMem

open NumberField Module Filter Topology MeasureTheory Pointwise
open scoped Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.BoxSum

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

def sBox (F : Type) [Field F] [NumberField F] : Set (mixedEmbedding.mixedSpace F) :=
  {x | ∀ w, 0 < x.1 w ∧ x.1 w ≤ 1}

def gW (F : Type) [Field F] [NumberField F] (m : ℕ) : mixedEmbedding.mixedSpace F → ℝ :=
  fun x => ∏ w, (x.1 w) ^ (m - 1)

theorem sBox_eq : sBox F = (Set.univ.pi fun _ => Set.Ioc (0 : ℝ) 1) ×ˢ Set.univ := by
  ext x; simp [sBox, Set.mem_pi]

theorem measurableSet_sBox : MeasurableSet (sBox F) := by
  rw [sBox_eq]
  exact (MeasurableSet.univ_pi fun _ => measurableSet_Ioc).prod MeasurableSet.univ

theorem convex_sBox : Convex ℝ (sBox F) := by
  rw [sBox_eq]
  exact (convex_pi fun _ _ => convex_Ioc _ _).prod convex_univ

theorem isBounded_sBox [IsTotallyReal F] : Bornology.IsBounded (sBox F) := by
  refine (Metric.isBounded_closedBall (x := 0) (r := 1)).subset fun x hx => ?_
  rw [mem_closedBall_zero_iff, Prod.norm_def, max_le_iff]
  constructor
  · rw [pi_norm_le_iff_of_nonneg zero_le_one]
    intro w
    rw [Real.norm_eq_abs, abs_of_pos (hx w).1]
    exact (hx w).2
  · rw [pi_norm_le_iff_of_nonneg zero_le_one]
    intro w
    exact absurd (IsTotallyReal.isReal w.1) (InfinitePlace.not_isReal_iff_isComplex.2 w.2)

theorem continuous_gW (m : ℕ) : Continuous (gW F m) := by
  unfold gW
  fun_prop

theorem integral_gW [IsTotallyReal F] {m : ℕ} (hm : 1 ≤ m) :
    ∫ x in sBox F, gW F m x = ((m : ℝ)⁻¹) ^ Fintype.card {w : InfinitePlace F // w.IsReal} := by
  have hE : IsEmpty {w : InfinitePlace F // w.IsComplex} :=
    ⟨fun w => absurd (IsTotallyReal.isReal w.1) (InfinitePlace.not_isReal_iff_isComplex.2 w.2)⟩
  have h1 : (volume : Measure ({w : InfinitePlace F // w.IsComplex} → ℂ)).real Set.univ = 1 := by
    rw [volume_pi, Measure.pi_of_empty]
    simp
  rw [sBox_eq, Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
  unfold gW
  rw [integral_fun_fst (f := fun y : {w : InfinitePlace F // w.IsReal} → ℝ => ∏ w, y w ^ (m - 1)),
    h1, one_smul, volume_pi, Measure.restrict_pi_pi,
    integral_fintype_prod_eq_prod (fun _ (y : ℝ) => y ^ (m - 1)), Finset.prod_const,
    Finset.card_univ]
  congr 1
  rw [← intervalIntegral.integral_of_le zero_le_one, integral_pow, Nat.cast_sub hm]
  simp

def fracU {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) : (FractionalIdeal (nonZeroDivisors (𝓞 F)) F)ˣ :=
  Units.mk0 (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (FractionalIdeal.coeIdeal_ne_zero.2 hI)

theorem mem_idealLattice_iff {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) (y : mixedEmbedding.mixedSpace F) :
    y ∈ mixedEmbedding.idealLattice F (fracU hI) ↔ ∃ n ∈ I, mixedEmbedding F (n : F) = y := by
  rw [mixedEmbedding.mem_idealLattice]
  constructor
  · rintro ⟨a, ha, rfl⟩
    have ha' : a ∈ (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := ha
    obtain ⟨n, hn, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 ha'
    exact ⟨n, hn, rfl⟩
  · rintro ⟨n, hn, rfl⟩
    exact ⟨(n : F), (FractionalIdeal.mem_coeIdeal _).2 ⟨n, hn, rfl⟩, rfl⟩

theorem gW_smul (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (m : ℕ) {T : ℝ} {n : 𝓞 F}
    (hn : n ∈ boxSet K F T) (c : ℝ) :
    gW F m (c • mixedEmbedding F (n : F)) =
      (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (m - 1) * c ^ (Formalism.HermitianLatticesTheory.fDeg K * (m - 1)) := by
  unfold gW
  rw [absNorm_eq_prod_of_mem hK hF hn, ← Finset.prod_pow, pow_mul, ← card_real hK hF,
    ← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [Prod.smul_fst, Pi.smul_apply, mixedEmbedding.mixedEmbedding_apply_isReal, smul_eq_mul, mul_pow,
    rEmb_apply, mul_comm]

theorem tsum_eq (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (m : ℕ) {I : Ideal (𝓞 F)}
    (hI : I ≠ ⊥) {N : ℝ} (hN : 0 < N) :
    ∑' x : ↑(sBox F ∩ N⁻¹ • (mixedEmbedding.idealLattice F (fracU hI) : Set (mixedEmbedding.mixedSpace F))), gW F m x =
      (∑ᶠ n ∈ {n : 𝓞 F | n ∈ boxSet K F N ∧ n ∈ I},
        (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (m - 1)) * N⁻¹ ^ (Formalism.HermitianLatticesTheory.fDeg K * (m - 1)) := by
  have hfin : {n : 𝓞 F | n ∈ boxSet K F N ∧ n ∈ I}.Finite :=
    (finite_boxSet hK hF N).subset fun n hn => hn.1
  have hmem : ∀ n : {n : 𝓞 F | n ∈ boxSet K F N ∧ n ∈ I}, N⁻¹ • mixedEmbedding F ((n : 𝓞 F) : F) ∈
      sBox F ∩ N⁻¹ • (mixedEmbedding.idealLattice F (fracU hI) : Set (mixedEmbedding.mixedSpace F)) := by
    rintro ⟨n, hn, hnI⟩
    refine ⟨fun w => ?_, Set.smul_mem_smul_set ((mem_idealLattice_iff hI _).2 ⟨n, hnI, rfl⟩)⟩
    have h1 := (mem_boxSet_iff hK hF).1 hn w
    rw [Prod.smul_fst, Pi.smul_apply, mixedEmbedding.mixedEmbedding_apply_isReal, smul_eq_mul,
      ← rEmb_apply]
    refine ⟨mul_pos (inv_pos.2 hN) h1.1, ?_⟩
    rw [inv_mul_le_iff₀ hN, mul_one]
    exact h1.2
  let ε : {n : 𝓞 F | n ∈ boxSet K F N ∧ n ∈ I} →
      ↑(sBox F ∩ N⁻¹ • (mixedEmbedding.idealLattice F (fracU hI) : Set (mixedEmbedding.mixedSpace F))) := fun n => ⟨_, hmem n⟩
  have hε : Function.Bijective ε := by
    constructor
    · intro n n' h
      have h1 : N⁻¹ • mixedEmbedding F ((n : 𝓞 F) : F) = N⁻¹ • mixedEmbedding F ((n' : 𝓞 F) : F) :=
        congrArg Subtype.val h
      have h2 := smul_right_injective _ (inv_ne_zero hN.ne') h1
      exact Subtype.ext (RingOfIntegers.coe_injective (mixedEmbedding_injective F h2))
    · rintro ⟨x, hx, hxL⟩
      obtain ⟨y, hy, rfl⟩ := hxL
      obtain ⟨n, hnI, rfl⟩ := (mem_idealLattice_iff hI _).1 hy
      refine ⟨⟨n, (mem_boxSet_iff hK hF).2 fun w => ?_, hnI⟩, rfl⟩
      have h1 := hx w
      simp only [] at h1
      rw [Prod.smul_fst, Pi.smul_apply, mixedEmbedding.mixedEmbedding_apply_isReal, smul_eq_mul,
        ← rEmb_apply, inv_mul_le_iff₀ hN, mul_one] at h1
      exact ⟨(mul_pos_iff_of_pos_left (inv_pos.2 hN)).1 h1.1, h1.2⟩
  have : Finite {n : 𝓞 F | n ∈ boxSet K F N ∧ n ∈ I} := hfin
  rw [← (Equiv.ofBijective ε hε).tsum_eq, tsum_eq_finsum (Set.toFinite _), finsum_mem_mul,
    ← finsum_set_coe_eq_finsum_mem]
  refine finsum_congr fun n => ?_
  exact gW_smul hK hF m n.2.1 _

theorem tendsto_sum_ideal (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {m : ℕ} (hm : 1 ≤ m)
    {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) :
    Tendsto (fun j : ℕ => ((j : ℝ) ^ 2) ^ (-((Formalism.HermitianLatticesTheory.fDeg K * m : ℕ) : ℤ)) *
        ∑ᶠ n ∈ {n : 𝓞 F | n ∈ boxSet K F ((j : ℝ) ^ 2) ∧ n ∈ I},
          (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (m - 1))
      atTop (𝓝 ((m : ℝ) ^ (-(Formalism.HermitianLatticesTheory.fDeg K : ℤ)) /
        Real.sqrt ((2 * Formalism.HermitianLatticesTheory.vInv K) ^ Formalism.HermitianLatticesTheory.fDeg K) / (Ideal.absNorm I : ℝ))) := by
  have hR : IsTotallyReal F := QuadraticExtensionConjugation.isTotallyReal hK hF
  obtain ⟨-, hfr, hdisc⟩ := discrTower K F hK hF
  have key := LatSum.tendsto_tsum_div_pow (mixedEmbedding.idealLattice F (fracU hI)) volume
    isBounded_sBox measurableSet_sBox (convex_sBox.addHaar_frontier volume) (continuous_gW m)
  rw [integral_gW hm, card_real hK hF, mixedEmbedding.covolume_idealLattice,
    mixedEmbedding.finrank, hfr, IsTotallyReal.nrComplexPlaces_eq_zero, pow_zero, mul_one] at key
  have hsq : Tendsto (fun j : ℕ => j ^ 2) atTop atTop := tendsto_pow_atTop two_ne_zero
  have key2 := key.comp hsq
  have hlim : ((m : ℝ)⁻¹) ^ Formalism.HermitianLatticesTheory.fDeg K /
      (((FractionalIdeal.absNorm ((fracU hI : (FractionalIdeal (nonZeroDivisors (𝓞 F)) F)ˣ) :
        FractionalIdeal (nonZeroDivisors (𝓞 F)) F) : ℚ) : ℝ) * Real.sqrt |(discr F : ℝ)|) =
      (m : ℝ) ^ (-(Formalism.HermitianLatticesTheory.fDeg K : ℤ)) /
        Real.sqrt ((2 * Formalism.HermitianLatticesTheory.vInv K) ^ Formalism.HermitianLatticesTheory.fDeg K) / (Ideal.absNorm I : ℝ) := by
    have h1 : FractionalIdeal.absNorm ((fracU hI : (FractionalIdeal (nonZeroDivisors (𝓞 F)) F)ˣ) :
        FractionalIdeal (nonZeroDivisors (𝓞 F)) F) = (Ideal.absNorm I : ℚ) :=
      FractionalIdeal.coeIdeal_absNorm I
    have h2 : |(discr F : ℝ)| = (2 * Formalism.HermitianLatticesTheory.vInv K) ^ Formalism.HermitianLatticesTheory.fDeg K := by
      rw [hdisc, abs_of_nonneg (pow_nonneg (mul_nonneg zero_le_two (vInv_pos K).le) _)]
    rw [h1, h2, zpow_neg, zpow_natCast, inv_pow, div_div, Rat.cast_natCast, mul_comm]
  rw [hlim] at key2
  refine Tendsto.congr' ?_ key2
  filter_upwards [eventually_gt_atTop 0] with j hj
  have hj' : (0 : ℝ) < (j : ℝ) ^ 2 := by positivity
  have hcast : ((j ^ 2 : ℕ) : ℝ) = (j : ℝ) ^ 2 := by push_cast; rfl
  have h3 := tsum_eq hK hF m hI (N := ((j ^ 2 : ℕ) : ℝ)) (by rw [hcast]; exact hj')
  rw [Function.comp_apply, h3, hcast, zpow_neg, zpow_natCast, inv_pow, div_eq_mul_inv, mul_assoc, ← mul_inv, ← pow_add, mul_comm]
  congr 3
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  ring

end Formalism.HermitianLattices.Ext.L3.BoxSum
