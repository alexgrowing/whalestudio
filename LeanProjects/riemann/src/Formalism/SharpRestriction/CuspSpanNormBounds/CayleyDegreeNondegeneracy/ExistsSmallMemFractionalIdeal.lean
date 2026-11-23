import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.ShortVectorEveryPlace

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField NumberField.mixedEmbedding Formalism.HermitianLatticesTheory
open scoped nonZeroDivisors NNReal ENNReal

theorem rootDiscr_pow_eq_sqrt_discr (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] :
    rootDiscriminant K ^ InfinitePlace.nrComplexPlaces K = Real.sqrt |(discr K : ℝ)| := by
  have h1 := InfinitePlace.card_add_two_mul_card_eq_rank K
  rw [IsTotallyComplex.nrRealPlaces_eq_zero K, zero_add] at h1
  have hpos : 0 < Module.finrank ℚ K := Module.finrank_pos
  have hn : (Module.finrank ℚ K : ℝ) = 2 * (InfinitePlace.nrComplexPlaces K : ℝ) := by
    exact_mod_cast h1.symm
  have hc : (InfinitePlace.nrComplexPlaces K : ℝ) ≠ 0 := by
    have : 0 < InfinitePlace.nrComplexPlaces K := by omega
    exact_mod_cast this.ne'
  unfold rootDiscriminant
  rw [← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _), hn, Real.sqrt_eq_rpow]
  congr 1
  field_simp

theorem rootDiscr_nonneg (K : Type) [Field K] [NumberField K] : 0 ≤ rootDiscriminant K := Real.rpow_nonneg (abs_nonneg _) _

open scoped Classical in

theorem exists_small_mem_fractional_ideal (K : Type) [Field K] [NumberField K] [IsTotallyComplex K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (hI : FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) ≤ 1) :
    ∃ a ∈ (I : FractionalIdeal (𝓞 K)⁰ K), a ≠ 0 ∧ ∀ w : InfinitePlace K, (w a) ^ 2 ≤ rootDiscriminant K := by
  have h1 := InfinitePlace.card_add_two_mul_card_eq_rank K
  rw [IsTotallyComplex.nrRealPlaces_eq_zero K, zero_add] at h1
  have hpos : 0 < Module.finrank ℚ K := Module.finrank_pos
  have hr2 : 0 < InfinitePlace.nrComplexPlaces K := by omega
  have hr0 : 0 ≤ rootDiscriminant K := by unfold rootDiscriminant; positivity
  let f : InfinitePlace K → NNReal := fun _ => NNReal.sqrt (Real.toNNReal (rootDiscriminant K))
  have hmult : ∀ w : InfinitePlace K, w.mult = 2 := fun w => by
    rw [InfinitePlace.mult, if_neg]
    exact InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w)
  have hcard : Fintype.card (InfinitePlace K) = InfinitePlace.nrComplexPlaces K := by
    rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyComplex.nrRealPlaces_eq_zero K, zero_add]
  have hS : (∏ w, f w ^ w.mult) = NNReal.sqrt ‖discr K‖₊ := by
    apply NNReal.eq
    rw [NNReal.coe_prod, Real.coe_sqrt, coe_nnnorm, Int.norm_eq_abs, ← rootDiscr_pow_eq_sqrt_discr K]
    simp only [hmult, f, NNReal.coe_pow, NNReal.sq_sqrt, Real.coe_toNNReal _ hr0, Finset.prod_const,
      Finset.card_univ, hcard]
  have hbound : minkowskiBound K I < MeasureTheory.volume (convexBodyLT K f) := by
    rw [convexBodyLT_volume, hS]
    unfold minkowskiBound
    rw [volume_fundamentalDomain_fractionalIdealLatticeBasis, volume_fundamentalDomain_latticeBasis,
      mixedEmbedding.finrank]
    unfold convexBodyLTFactor
    rw [IsTotallyComplex.nrRealPlaces_eq_zero K, pow_zero, one_mul, ← h1]
    have hs0 : ((NNReal.sqrt ‖discr K‖₊ : NNReal) : ℝ≥0∞) ≠ 0 := by
      simpa using discr_ne_zero K
    have hst : ((NNReal.sqrt ‖discr K‖₊ : NNReal) : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
    have hN : ENNReal.ofReal (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ) ≤ 1 := by
      rw [ENNReal.ofReal_le_one]
      exact_mod_cast hI
    calc ENNReal.ofReal (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ) *
          (2⁻¹ ^ InfinitePlace.nrComplexPlaces K * ((NNReal.sqrt ‖discr K‖₊ : NNReal) : ℝ≥0∞)) *
          2 ^ (2 * InfinitePlace.nrComplexPlaces K)
        ≤ 1 * (2⁻¹ ^ InfinitePlace.nrComplexPlaces K * ((NNReal.sqrt ‖discr K‖₊ : NNReal) : ℝ≥0∞)) *
          2 ^ (2 * InfinitePlace.nrComplexPlaces K) := by gcongr
      _ = 2 ^ InfinitePlace.nrComplexPlaces K * ((NNReal.sqrt ‖discr K‖₊ : NNReal) : ℝ≥0∞) := by
          rw [one_mul, pow_mul, mul_comm, ← mul_assoc, ← mul_pow]
          congr 1
          · rw [show ((2 : ℝ≥0∞) ^ 2 * 2⁻¹) = 2 by
              rw [pow_two, mul_assoc, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, mul_one]]
      _ < ((NNReal.pi ^ InfinitePlace.nrComplexPlaces K : NNReal) : ℝ≥0∞) *
          ((NNReal.sqrt ‖discr K‖₊ : NNReal) : ℝ≥0∞) := by
          rw [mul_comm _ ((NNReal.sqrt ‖discr K‖₊ : NNReal) : ℝ≥0∞),
            mul_comm _ ((NNReal.sqrt ‖discr K‖₊ : NNReal) : ℝ≥0∞)]
          refine ENNReal.mul_lt_mul_right hs0 hst ?_
          rw [ENNReal.coe_pow]
          refine ENNReal.pow_lt_pow_left hr2.ne' ?_
          rw [← ENNReal.coe_ofNat, ENNReal.coe_lt_coe]
          exact NNReal.coe_lt_coe.1 (by rw [NNReal.coe_real_pi, NNReal.coe_ofNat]; linarith [Real.pi_gt_three])
  obtain ⟨a, haI, ha0, hlt⟩ := exists_ne_zero_mem_ideal_lt K I hbound
  refine ⟨a, haI, ha0, fun w => ?_⟩
  have h2 := hlt w
  have hw0 : 0 ≤ w a := AbsoluteValue.nonneg _ _
  have hf2 : ((f w : NNReal) : ℝ) ^ 2 = rootDiscriminant K := by
    rw [← NNReal.coe_pow, NNReal.sq_sqrt, Real.coe_toNNReal _ hr0]
  calc (w a) ^ 2 ≤ ((f w : NNReal) : ℝ) ^ 2 := pow_le_pow_left₀ hw0 h2.le 2
    _ = rootDiscriminant K := hf2

section Alg

variable {K : Type} [Field K] [NumberField K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V]
  (h : V →ₗ⋆[K] V →ₗ[K] K) (e : Fin 2 → V)

theorem eq_sum_coords_orthonormal_pair (hspan : Submodule.span K (Set.range e) = ⊤)
    (ho : ∀ i j, h (e i) (e j) = if i = j then 1 else 0) (v : V) :
    v = h (e 0) v • e 0 + h (e 1) v • e 1 := by
  have hv : v ∈ Submodule.span K (Set.range e) := by
    rw [hspan]
    exact Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hv
  have hcoef : ∀ j, h (e j) v = c j := by
    intro j
    rw [← hc, map_sum]
    simp [map_smul, ho]
  rw [hcoef 0, hcoef 1]
  conv_lhs => rw [← hc]
  rw [Fin.sum_univ_two]

theorem inner_eq_coords_orthonormal_pair (hspan : Submodule.span K (Set.range e) = ⊤)
    (ho : ∀ i j, h (e i) (e j) = if i = j then 1 else 0) (u v : V) :
    h u v = star (h (e 0) u) * h (e 0) v + star (h (e 1) u) * h (e 1) v := by
  conv_lhs => rw [eq_sum_coords_orthonormal_pair h e hspan ho u, eq_sum_coords_orthonormal_pair h e hspan ho v]
  simp only [map_add, LinearMap.add_apply, LinearMap.map_smulₛₗ₂, map_smul, smul_eq_mul, ho, starRingEnd_apply]
  simp
  ring

def orthCompanion (x : V) : V := -(star (h (e 1) x)) • e 0 + star (h (e 0) x) • e 1

theorem orthCompanion_inner_apply (x v : V) :
    h (orthCompanion h e x) v = -(h (e 1) x) * h (e 0) v + h (e 0) x * h (e 1) v := by
  simp only [orthCompanion, map_add, LinearMap.add_apply, LinearMap.map_smulₛₗ₂, smul_eq_mul, starRingEnd_apply,
    star_neg, star_star]

theorem coords_orthCompanion (ho : ∀ i j, h (e i) (e j) = if i = j then 1 else 0) (x : V) :
    h (e 0) (orthCompanion h e x) = -(star (h (e 1) x)) ∧ h (e 1) (orthCompanion h e x) = star (h (e 0) x) := by
  constructor <;> simp [orthCompanion, ho]

theorem inner_self_orthCompanion (hspan : Submodule.span K (Set.range e) = ⊤)
    (ho : ∀ i j, h (e i) (e j) = if i = j then 1 else 0) (x : V) :
    h (orthCompanion h e x) (orthCompanion h e x) = h x x := by
  rw [inner_eq_coords_orthonormal_pair h e hspan ho, inner_eq_coords_orthonormal_pair h e hspan ho x x, (coords_orthCompanion h e ho x).1,
    (coords_orthCompanion h e ho x).2]
  simp only [star_neg, star_star]
  ring

theorem inner_orthCompanion_eq_zero (hspan : Submodule.span K (Set.range e) = ⊤)
    (ho : ∀ i j, h (e i) (e j) = if i = j then 1 else 0) (x : V) :
    h x (orthCompanion h e x) = 0 := by
  rw [inner_eq_coords_orthonormal_pair h e hspan ho, (coords_orthCompanion h e ho x).1, (coords_orthCompanion h e ho x).2]
  ring

theorem lagrange_identity_orthCompanion (hspan : Submodule.span K (Set.range e) = ⊤)
    (ho : ∀ i j, h (e i) (e j) = if i = j then 1 else 0) (x v v' : V) :
    h (orthCompanion h e x) v * star (h (orthCompanion h e x) v') = h x x * h v' v - h x v * h v' x := by
  rw [orthCompanion_inner_apply, orthCompanion_inner_apply, inner_eq_coords_orthonormal_pair h e hspan ho x x, inner_eq_coords_orthonormal_pair h e hspan ho v' v,
    inner_eq_coords_orthonormal_pair h e hspan ho x v, inner_eq_coords_orthonormal_pair h e hspan ho v' x]
  simp only [star_add, star_mul', star_neg, star_star]
  ring

theorem inner_self_ne_zero_of_orthonormal (hcm : ∀ (φ : K →+* ℂ) (a : K), φ (star a) = starRingEnd ℂ (φ a))
    (hspan : Submodule.span K (Set.range e) = ⊤)
    (ho : ∀ i j, h (e i) (e j) = if i = j then 1 else 0) (x : V) (hx : x ≠ 0) : h x x ≠ 0 := by
  intro h0
  apply hx
  obtain ⟨φ⟩ : Nonempty (K →+* ℂ) := inferInstance
  have hpar := inner_eq_coords_orthonormal_pair h e hspan ho x x
  rw [h0] at hpar
  have h1 := congrArg φ hpar
  simp only [map_zero, map_add, map_mul, hcm] at h1
  have e0 : ((Complex.normSq (φ (h (e 0) x)) + Complex.normSq (φ (h (e 1) x)) : ℝ) : ℂ) = 0 := by
    push_cast
    rw [Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_conj_mul_self]
    exact h1.symm
  have e0' := Complex.ofReal_eq_zero.1 e0
  have n0 := Complex.normSq_nonneg (φ (h (e 0) x))
  have n1 := Complex.normSq_nonneg (φ (h (e 1) x))
  have hb0 : φ (h (e 0) x) = 0 := Complex.normSq_eq_zero.1 (by linarith)
  have hb1 : φ (h (e 1) x) = 0 := Complex.normSq_eq_zero.1 (by linarith)
  have hb0' : h (e 0) x = 0 := (map_eq_zero_iff φ φ.injective).1 hb0
  have hb1' : h (e 1) x = 0 := (map_eq_zero_iff φ φ.injective).1 hb1
  rw [eq_sum_coords_orthonormal_pair h e hspan ho x, hb0', hb1', zero_smul, zero_smul, add_zero]

end Alg

theorem star_mem_integers {K : Type} [Field K] [NumberField K] [StarRing K] {a : K}
    (ha : a ∈ Set.range (algebraMap (𝓞 K) K)) : star a ∈ Set.range (algebraMap (𝓞 K) K) := by
  obtain ⟨o, rfl⟩ := ha
  have hint : IsIntegral ℤ (star (algebraMap (𝓞 K) K o)) :=
    (NumberField.RingOfIntegers.isIntegral_coe o).map (starRingEnd K).toIntAlgHom
  exact ⟨⟨star (algebraMap (𝓞 K) K o), hint⟩, rfl⟩

theorem inner_orthCompanion_symm {K : Type} [Field K] [NumberField K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (e : Fin 2 → V) (hspan : Submodule.span K (Set.range e) = ⊤)
    (ho : ∀ i j, h (e i) (e j) = if i = j then 1 else 0) (x v : V) :
    h v (orthCompanion h e x) = star (h (orthCompanion h e x) v) := by
  rw [inner_eq_coords_orthonormal_pair h e hspan ho v, inner_eq_coords_orthonormal_pair h e hspan ho (orthCompanion h e x) v]
  simp only [star_add, star_mul', star_star]
  ring

theorem exists_orthogonal_second_vector (K : Type) [Field K] [NumberField K] [StarRing K] (hK : Formalism.HermitianLatticesTheory.IsCMUnram K)
    (V : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) (hL : Formalism.HermitianLatticesTheory.IsOrthoLattice h L 2)
    (M : Submodule (𝓞 K) V) (hlat : Submodule.IsLattice K M) (hint : Formalism.HermitianLatticesTheory.IsIntegralLat h M)
    (huni : Formalism.HermitianLatticesTheory.dual h M = M) (x : V) (hx : x ∈ M) (hx0 : x ≠ 0) :
    ∃ y ∈ M, y ≠ 0 ∧ h x y = 0 ∧ ∀ φ : K →+* ℂ, ‖φ (h y y)‖ ≤ ‖φ (h x x)‖ * rootDiscriminant K := by
  obtain ⟨e, -, hspan, -, ho⟩ := hL
  have : IsTotallyComplex K := hK.1
  have hcm := hK.2.1
  set y0 := orthCompanion h e x with hy0
  have hα : h x x ≠ 0 := inner_self_ne_zero_of_orthonormal h e hcm hspan ho x hx0
  have hy0y0 : h y0 y0 = h x x := inner_self_orthCompanion h e hspan ho x
  have hy0ne : y0 ≠ 0 := by
    intro h0
    apply hα
    rw [← hy0y0, h0]
    simp
  have hI : ∀ u ∈ M, ∀ v ∈ M, h u v ∈ Set.range (algebraMap (𝓞 K) K) := fun u hu v hv => by
    have := hint u hu v hv
    rwa [Submodule.mem_one] at this
  have hLag : ∀ v ∈ M, ∀ v' ∈ M, h y0 v * star (h y0 v') ∈ Set.range (algebraMap (𝓞 K) K) := by
    intro v hv v' hv'
    rw [hy0, lagrange_identity_orthCompanion h e hspan ho x v v']
    obtain ⟨a, ha⟩ := hI x hx x hx
    obtain ⟨b, hb⟩ := hI v' hv' v hv
    obtain ⟨c, hc⟩ := hI x hx v hv
    obtain ⟨d, hd⟩ := hI v' hv' x hx
    exact ⟨a * b - c * d, by rw [map_sub, map_mul, map_mul, ha, hb, hc, hd]⟩
  suffices hb : ∃ b : K, b ≠ 0 ∧ (∀ v ∈ M, b * star (h y0 v) ∈ Set.range (algebraMap (𝓞 K) K)) ∧
      ∀ φ : K →+* ℂ, ‖φ b‖ ^ 2 ≤ rootDiscriminant K by
    obtain ⟨b, hb0, hbM, hbφ⟩ := hb
    refine ⟨b • y0, ?_, smul_ne_zero hb0 hy0ne, ?_, ?_⟩
    · rw [← huni]
      simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap]
      intro v hv
      rw [Submodule.mem_one]
      have h1 : h v (b • y0) = b * star (h y0 v) := by
        rw [map_smul, smul_eq_mul, hy0, inner_orthCompanion_symm h e hspan ho x v]
      obtain ⟨c, hc⟩ := hbM v hv
      exact ⟨c, by rw [hc]; exact h1.symm⟩
    · rw [map_smul, hy0, inner_orthCompanion_eq_zero h e hspan ho x, smul_zero]
    · intro φ
      have h1 : h (b • y0) (b • y0) = star b * (b * h x x) := by
        have h2 : h (b • y0) (b • y0) = star b * (b * h y0 y0) := by
          simp only [LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, RingHom.id_apply]
          ring
        rw [h2, hy0y0]
      rw [h1, map_mul, map_mul, hcm, norm_mul, norm_mul, RCLike.norm_conj]
      calc ‖φ b‖ * (‖φ b‖ * ‖φ (h x x)‖) = ‖φ (h x x)‖ * ‖φ b‖ ^ 2 := by ring
        _ ≤ ‖φ (h x x)‖ * rootDiscriminant K := mul_le_mul_of_nonneg_left (hbφ φ) (norm_nonneg _)
  let cc : Submodule (𝓞 K) K := M.map ((h y0).restrictScalars (𝓞 K))
  have hfg : cc.FG := hlat.fg.map _
  let ccF : FractionalIdeal (𝓞 K)⁰ K := ⟨cc, FractionalIdeal.isFractional_of_fg hfg⟩
  have hmem : ∀ c, c ∈ ccF ↔ ∃ v ∈ M, h y0 v = c := by
    intro c
    change c ∈ cc ↔ _
    simp only [cc, Submodule.mem_map, LinearMap.restrictScalars_apply]
  have hne : ccF ≠ 0 := by
    intro h0
    have hz : ∀ v ∈ M, h y0 v = 0 := fun v hv => by
      have h1 : h y0 v ∈ ccF := (hmem _).2 ⟨v, hv, rfl⟩
      rw [h0] at h1
      exact (FractionalIdeal.mem_zero_iff _).1 h1
    have hy : y0 ∈ Submodule.span K (M : Set V) := hlat.span_eq_top ▸ Submodule.mem_top
    have hle : Submodule.span K (M : Set V) ≤ LinearMap.ker (h y0) :=
      Submodule.span_le.2 fun v hv => LinearMap.mem_ker.2 (hz v hv)
    exact hα (hy0y0 ▸ LinearMap.mem_ker.1 (hle hy))
  have hprod : FractionalIdeal.absNorm ccF * FractionalIdeal.absNorm ccF⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hne, map_one]
  by_cases hc : FractionalIdeal.absNorm ccF ≤ 1
  · obtain ⟨a, ha, ha0, hw⟩ := exists_small_mem_fractional_ideal K (Units.mk0 ccF hne) hc
    obtain ⟨v', hv', rfl⟩ := (hmem a).1 ha
    exact ⟨h y0 v', ha0, fun v hv => hLag v' hv' v hv, fun φ => by
      rw [← InfinitePlace.apply]; exact hw _⟩
  · have hc' : FractionalIdeal.absNorm ccF⁻¹ ≤ 1 := by
      by_contra hlt
      rw [not_le] at hlt hc
      nlinarith
    obtain ⟨a, ha, ha0, hw⟩ := exists_small_mem_fractional_ideal K (Units.mk0 ccF hne)⁻¹ (by simpa using hc')
    have ha' : a ∈ ccF⁻¹ := by simpa using ha
    rw [FractionalIdeal.mem_inv_iff hne] at ha'
    refine ⟨star a, star_ne_zero.2 ha0, fun v hv => ?_, fun φ => ?_⟩
    · have h1 := ha' (h y0 v) ((hmem _).2 ⟨v, hv, rfl⟩)
      rw [FractionalIdeal.mem_one_iff] at h1
      rw [← star_mul']
      exact star_mem_integers h1
    · rw [hcm, RCLike.norm_conj, ← InfinitePlace.apply]
      exact hw _

end Formalism.MainNotions.BridgeLemma₂

end
