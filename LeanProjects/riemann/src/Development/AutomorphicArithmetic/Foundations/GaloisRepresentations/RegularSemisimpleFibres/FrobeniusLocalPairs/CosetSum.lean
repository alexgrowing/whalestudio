import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.MatchSmulAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.QuotFubiniHolds

open MeasureTheory PositivityTheory.Rg.Tf.Loc

private theorem exists_reps {G ι : Type} [Group G] (H U : Subgroup G) (R : Finset ι) (x : ι → G)
    (hd : ∀ i ∈ R, ∀ j ∈ R, (∃ h ∈ H, ∃ u ∈ U, x i = h * x j * u) → i = j) :
    ∃ r : G → G, (∀ g, ∃ h ∈ H, ∃ u ∈ U, g = h * r g * u) ∧ (∀ g, ∀ h ∈ H, ∀ u ∈ U, r (h * g * u) = r g) ∧
      ∀ i ∈ R, r (x i) = x i := by
  classical
  let S : Setoid G :=
    { r := fun g g' => ∃ h ∈ H, ∃ u ∈ U, g = h * g' * u
      iseqv :=
        { refl := fun g => ⟨1, H.one_mem, 1, U.one_mem, by simp⟩
          symm := by
            rintro g g' ⟨h, hh, u, hu, rfl⟩
            exact ⟨h⁻¹, H.inv_mem hh, u⁻¹, U.inv_mem hu, by group⟩
          trans := by
            rintro g g' g'' ⟨h₁, hh₁, u₁, hu₁, rfl⟩ ⟨h₂, hh₂, u₂, hu₂, rfl⟩
            exact ⟨h₁ * h₂, H.mul_mem hh₁ hh₂, u₂ * u₁, U.mul_mem hu₂ hu₁, by group⟩ } }
  let f : Quotient S → G := fun q =>
    if hq : ∃ i ∈ R, Quotient.mk S (x i) = q then x hq.choose else q.out
  have hf : ∀ g, S.r g (f (Quotient.mk S g)) := by
    intro g
    by_cases hq : ∃ i ∈ R, Quotient.mk S (x i) = Quotient.mk S g
    · simp only [f, dif_pos hq]
      exact Quotient.exact (hq.choose_spec.2.symm)
    · simp only [f, dif_neg hq]
      exact Quotient.exact (Quotient.out_eq (Quotient.mk S g)).symm
  refine ⟨fun g => f (Quotient.mk S g), hf, ?_, ?_⟩
  · intro g h hh u hu
    have : Quotient.mk S (h * g * u) = Quotient.mk S g := Quotient.sound ⟨h, hh, u, hu, rfl⟩
    simp only [this]
  · intro i hi
    have hq : ∃ j ∈ R, Quotient.mk S (x j) = Quotient.mk S (x i) := ⟨i, hi, rfl⟩
    simp only [f, dif_pos hq]
    rw [hd _ hq.choose_spec.1 i hi (Quotient.exact hq.choose_spec.2)]

theorem UpperTheory.Gal.InertialTypesAlt.L.cosetSum :
    UpperTheory.Gal.InertialTypesAlt.L.CosetSum := by
  intro G _ _ _ _ _ _ _ _ μ hμ K H hKo hKc hHc hcomm ν hν ι R x V S hV hS hd
  classical
  haveI : SFinite μ := inferInstance
  haveI : LocallyCompactSpace H := hHc.locallyCompactSpace
  haveI : SFinite ν := inferInstance
  letI cH : CommGroup H :=
    { (inferInstance : Group H) with mul_comm := fun a b => Subtype.ext (hcomm a a.2 b b.2) }
  haveI : ν.IsInvInvariant := @Measure.IsHaarMeasure.isInvInvariant_of_regular H cH _ _ _ _ ν hν _ _
  obtain ⟨rep, hrep, hinv, hfix⟩ := exists_reps H K R x hd
  let W : G → Set H := fun y => {h | y⁻¹ * (h : G) * y ∈ K}
  have hWcont : ∀ y : G, Continuous fun h : H => y⁻¹ * (h : G) * y := fun y => by fun_prop
  have hWopen : ∀ y, IsOpen (W y) := fun y => hKo.preimage (hWcont y)
  have hWpos : ∀ y, ν (W y) ≠ 0 := fun y =>
    ((hWopen y).measure_pos ν ⟨1, by simp [W, K.one_mem]⟩).ne'
  have hWfin : ∀ y, ν (W y) ≠ ⊤ := by
    intro y
    have hc : IsCompact (W y) := by
      have e : W y = Subtype.val ⁻¹' ((fun k => y * k * y⁻¹) '' (K : Set G)) := by
        ext h
        simp only [W, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_image]
        constructor
        · intro hk
          exact ⟨_, hk, by group⟩
        · rintro ⟨k, hk, hk'⟩
          rw [← hk']
          have e2 : y⁻¹ * (y * k * y⁻¹) * y = k := by group
          rw [e2]
          exact hk
      rw [e]
      exact hHc.isClosedEmbedding_subtypeVal.isCompact_preimage (hKc.image (by fun_prop))
    exact hc.measure_lt_top.ne
  have hrepK : ∀ g, ∀ k ∈ K, rep (g * k) = rep g := fun g k hk => by
    simpa using hinv g 1 H.one_mem k hk
  have hrepH : ∀ g, ∀ h ∈ H, rep (h * g) = rep g := fun g h hh => by
    simpa using hinv g h hh 1 K.one_mem
  let ρ : G → ENNReal := fun g => if (rep g)⁻¹ * g ∈ K then (ν (W (rep g)))⁻¹ else 0
  have hρK : ∀ g, ∀ k ∈ K, ρ (g * k) = ρ g := by
    intro g k hk
    simp only [ρ, hrepK g k hk, ← mul_assoc, K.mul_mem_cancel_right hk]
  have hρm : Measurable ρ := by
    have : IsLocallyConstant ρ := by
      rw [IsLocallyConstant.iff_eventually_eq]
      intro g
      have ho : IsOpen ((fun z => g⁻¹ * z) ⁻¹' (K : Set G)) := hKo.preimage (by fun_prop)
      filter_upwards [ho.mem_nhds (by simp [K.one_mem])] with z hz
      have : z = g * (g⁻¹ * z) := by group
      rw [this, hρK g _ hz]
    exact this.continuous.measurable
  have hρn : IsQuotNormaliser H ν ρ := by
    refine ⟨hρm, fun g => ?_⟩
    obtain ⟨h0, hh0, k0, hk0, hg⟩ := hrep g
    set y := rep g with hy
    have key : ∀ h : H, ρ (↑h * g) = (W y).indicator (fun _ => (ν (W y))⁻¹) (⟨h0, hh0⟩ * h) := by
      intro h
      have hr : rep (↑h * g) = y := hrepH g h h.2
      simp only [ρ, hr, Set.indicator, W, Set.mem_setOf_eq]
      have e : y⁻¹ * (↑h * g) = (y⁻¹ * ↑(⟨h0, hh0⟩ * h : H) * y) * k0 := by
        rw [hg]
        simp only [Subgroup.coe_mul]
        rw [(hcomm h0 hh0 h h.2).eq]
        group
      rw [e, K.mul_mem_cancel_right hk0]
    simp_rw [key]
    rw [lintegral_indicator_const_comp (measurable_const_mul _) (hWopen y).measurableSet]
    rw [measure_preimage_mul, ENNReal.inv_mul_cancel (hWpos y) (hWfin y)]
  rcases R.eq_empty_or_nonempty with hR | ⟨i0, hi0⟩
  · have hS0 : S = ∅ := by
      ext g
      simp [hS g, hR]
    simp [quotIntegral, hS0, hR]
  have hWV : ∀ i ∈ R, W (x i) = V := by
    intro i hi
    ext h
    exact (hV i hi h).symm
  have hV0 : ν V ≠ 0 := hWV i0 hi0 ▸ hWpos (x i0)
  have hVt : ν V ≠ ⊤ := hWV i0 hi0 ▸ hWfin (x i0)
  have hSK : ∀ g, ∀ k ∈ K, g ∈ S → g * k ∈ S := by
    intro g k hk hg
    obtain ⟨i, hi, h, hh, κ, hκ, rfl⟩ := (hS _).1 hg
    exact (hS _).2 ⟨i, hi, h, hh, κ * k, K.mul_mem hκ hk, by group⟩
  have hSH : ∀ g, ∀ h ∈ H, h * g ∈ S ↔ g ∈ S := by
    intro g h hh
    constructor
    · intro hg
      obtain ⟨i, hi, h', hh', κ, hκ, e⟩ := (hS _).1 hg
      refine (hS _).2 ⟨i, hi, h⁻¹ * h', H.mul_mem (H.inv_mem hh) hh', κ, hκ, ?_⟩
      rw [mul_assoc (h⁻¹ * h'), mul_assoc h⁻¹, ← mul_assoc h', ← e]
      group
    · intro hg
      obtain ⟨i, hi, h', hh', κ, hκ, rfl⟩ := (hS _).1 hg
      exact (hS _).2 ⟨i, hi, h * h', H.mul_mem hh hh', κ, hκ, by group⟩
  have hSo : IsOpen S := by
    rw [isOpen_iff_forall_mem_open]
    intro g hg
    refine ⟨(fun z => g⁻¹ * z) ⁻¹' (K : Set G), ?_, hKo.preimage (by fun_prop), by simp [K.one_mem]⟩
    intro z hz
    have : z = g * (g⁻¹ * z) := by group
    rw [this]
    exact hSK g _ hz hg
  let F : G → ENNReal := S.indicator 1
  have hFm : Measurable F := measurable_one.indicator hSo.measurableSet
  have hFH : ∀ h ∈ H, ∀ g, F (h * g) = F g := by
    intro h hh g
    by_cases hg : g ∈ S
    · simp [F, hg, (hSH g h hh).2 hg]
    · simp [F, hg, mt (hSH g h hh).1 hg]
  have hex : ∃ ρ, IsQuotNormaliser H ν ρ := ⟨ρ, hρn⟩
  have hswap := lintegral_normaliser_eq (μG := μ) hFm hFH hex.choose_spec hρn
  have hpt : ∀ g, F g * ρ g =
      ∑ i ∈ R, ((fun z => (x i)⁻¹ * z) ⁻¹' (K : Set G)).indicator (fun _ => (ν V)⁻¹) g := by
    intro g
    by_cases hg : g ∈ S
    · obtain ⟨i, hi, h, hh, κ, hκ, rfl⟩ := (hS _).1 hg
      have hr : rep (h * x i * κ) = x i := by rw [hinv _ h hh κ hκ, hfix i hi]
      rw [Finset.sum_eq_single_of_mem i hi]
      · simp [F, Set.indicator_of_mem hg, ρ, hr, hWV i hi, Set.indicator]
      · intro j hj hji
        rw [Set.indicator_of_notMem]
        intro hm
        apply hji
        refine hd j hj i hi ⟨h, hh, κ * ((x j)⁻¹ * (h * x i * κ))⁻¹, K.mul_mem hκ (K.inv_mem hm), ?_⟩
        group
    · have hF0 : F g = 0 := Set.indicator_of_notMem hg _
      rw [hF0, zero_mul]
      symm
      apply Finset.sum_eq_zero
      intro i hi
      rw [Set.indicator_of_notMem]
      intro hm
      apply hg
      exact (hS _).2 ⟨i, hi, 1, H.one_mem, (x i)⁻¹ * g, hm, by group⟩
  have hcomp : ∫⁻ g, F g * ρ g ∂μ = R.card * ((ν V)⁻¹ * μ K) := by
    rw [lintegral_congr (fun g => hpt g), lintegral_finset_sum]
    · simp_rw [lintegral_indicator_const (hKo.measurableSet.preimage (measurable_const_mul _)),
        measure_preimage_mul]
      rw [Finset.sum_const, nsmul_eq_mul]
    · intro i _
      exact measurable_const.indicator (hKo.measurableSet.preimage (measurable_const_mul _))
  have hI : ∫⁻ g, F g * hex.choose g ∂μ = R.card * ((ν V)⁻¹ * μ K) := hswap.trans hcomp
  have hfin : (R.card : ENNReal) * ((ν V)⁻¹ * μ K) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
      (ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hV0) hKc.measure_lt_top.ne)
  have hpt2 : ∀ g, (S.indicator 1 g : ℂ) * (((hex.choose g).toReal : ℝ) : ℂ)
      = (((F g * hex.choose g).toReal : ℝ) : ℂ) := by
    intro g
    by_cases hg : g ∈ S <;> simp [F, hg]
  unfold quotIntegral
  rw [dif_pos hex]
  simp_rw [hpt2]
  have hm2 : Measurable fun g => F g * hex.choose g := hFm.mul hex.choose_spec.1
  rw [integral_complex_ofReal, integral_toReal hm2.aemeasurable (ae_lt_top hm2 (hI ▸ hfin)), hI]
  congr 1
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    measureReal_def, measureReal_def]
  ring
