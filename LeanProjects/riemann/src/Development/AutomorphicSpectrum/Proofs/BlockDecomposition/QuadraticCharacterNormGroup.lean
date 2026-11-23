import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GTil
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel NNReal ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.GaussLam.Til

open Topology

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem modulus_neg_eq (x : F) : modulus (-x) = modulus x := by
  have h : modulus (-1 : F) = 1 := by
    have h1 : modulus (-1 : F) * modulus (-1 : F) = 1 := by
      rw [← modulus_mul]; simp
    have h2 : modulus (-1 : F) ^ 2 = 1 := by rw [sq]; exact h1
    exact (pow_eq_one_iff.1 h2).resolve_right (by norm_num)
  rw [show -x = -1 * x by ring, modulus_mul, h, one_mul]

theorem eventually_modulus_eq {x : F} (hx : x ≠ 0) : ∀ᶠ y in 𝓝 x, modulus y = modulus x := by
  have hO : {z : F | z - x ∈ valBall F (ord x + 1)} ∈ 𝓝 x :=
    ((isOpen_valBall _).preimage (continuous_id.sub continuous_const)).mem_nhds (by simp)
  filter_upwards [hO] with y hy
  have := ord_add_eq hx hy
  rw [add_sub_cancel] at this
  rw [modulus_of_ne_zero this.1, modulus_of_ne_zero hx, this.2]

theorem eventually_eq_of_sign {η : Fˣ →* ℂˣ} (hc : Continuous η)
    (hs : ∀ a, ((η a : ℂˣ) : ℂ) = 1 ∨ ((η a : ℂˣ) : ℂ) = -1) (u : Fˣ) :
    ∀ᶠ v in 𝓝 u, η v = η u := by
  have hf : Continuous fun v : Fˣ => ((η v : ℂˣ) : ℂ) := Units.continuous_val.comp hc
  filter_upwards [(hf.tendsto u).eventually (Metric.ball_mem_nhds _ one_pos)] with v hv
  apply Units.ext
  have hv' : ‖((η v : ℂˣ) : ℂ) - ((η u : ℂˣ) : ℂ)‖ < 1 := by simpa [dist_eq_norm] using hv
  rcases hs v with h1 | h1 <;> rcases hs u with h2 | h2 <;> rw [h1, h2] at hv' <;> rw [h1, h2]
  · norm_num at hv'
  · norm_num at hv'

variable (E : Type) [CommRing E] [Algebra F E]

theorem gTil_zero (g : F → ℂ) : gTil E g (0 : F) = 0 := by
  simp [gTil]

theorem mem_of_gTil_ne_zero {g : F → ℂ} {N M : ℤ} (hN : ∀ h ∈ valBall F N, g h = 0)
    (hM : ∀ x, g x ≠ 0 → x ∈ valBall F M) {y : F} (hy : gTil E g y ≠ 0) :
    y ∈ valBall F (-N) ∧ y ∉ valBall F (1 - M) := by
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact hy (gTil_zero E g)
  have hg : g (-y⁻¹) ≠ 0 := by
    intro h
    exact hy (by simp [gTil, h])
  have hi : y⁻¹ ≠ 0 := inv_ne_zero hy0
  have h1 : y⁻¹ ∉ valBall F N := fun h => hg (hN _ (neg_mem h))
  have h2 : y⁻¹ ∈ valBall F M := by
    have := neg_mem (hM _ hg)
    simpa using this
  rw [mem_valBall_iff_le_ord hi, ord_inv hy0] at h1 h2
  rw [mem_valBall_iff_le_ord hy0, mem_valBall_iff_le_ord hy0]
  omega

theorem gTil_mem {η : Fˣ →* ℂˣ} (hc : Continuous η)
    (hη : ∀ a : Fˣ, ((η a : ℂˣ) : ℂ) = nsg E (a : F)) {g : F → ℂ} (hg : g ∈ schwartzBruhat F)
    (h0 : g 0 = 0) : gTil E g ∈ schwartzBruhat F := by
  obtain ⟨N, M, hN, hM⟩ := exists_invariant_of_mem_schwartzBruhat hg
  have hN' : ∀ h ∈ valBall F N, g h = 0 := fun h hh => by
    have := hN 0 h hh
    rwa [zero_add, h0] at this
  have hs : ∀ a, ((η a : ℂˣ) : ℂ) = 1 ∨ ((η a : ℂˣ) : ℂ) = -1 := fun a => by
    rw [hη, nsg]
    split_ifs <;> simp
  refine ⟨IsLocallyConstant.iff_eventually_eq _ |>.2 fun x => ?_, ?_⟩
  · by_cases hx : x = 0
    · subst hx
      have hO : (valBall F (1 - M) : Set F) ∈ 𝓝 (0 : F) :=
        (isOpen_valBall _).mem_nhds (zero_mem _)
      filter_upwards [hO] with y hy
      rw [gTil_zero]
      by_contra hne
      exact (mem_of_gTil_ne_zero E hN' hM hne).2 hy
    · have e1 : ∀ᶠ y in 𝓝 x, g (-y⁻¹) = g (-x⁻¹) := by
        have ht : Filter.Tendsto (fun y : F => -y⁻¹) (𝓝 x) (𝓝 (-x⁻¹)) :=
          (continuousAt_inv₀ hx).tendsto.neg
        exact ht.eventually ((IsLocallyConstant.iff_eventually_eq _).1 hg.1 _)
      have e2 : ∀ᶠ y in 𝓝 x, nsg E (-y) = nsg E (-x) := by
        let u : Fˣ := Units.mk0 x hx
        have hm : Filter.map (Units.val : Fˣ → F) (𝓝 u) = 𝓝 x :=
          (isOpenEmbedding_units_val (K := F)).map_nhds_eq u
        rw [← hm, Filter.eventually_map]
        filter_upwards [eventually_eq_of_sign hc hs u] with v hv
        have hneg : ∀ w : Fˣ, nsg E (-(w : F)) = ((η (-1) : ℂˣ) : ℂ) * ((η w : ℂˣ) : ℂ) := fun w => by
          rw [show -(w : F) = (((-1 : Fˣ) * w : Fˣ) : F) by simp, ← hη, map_mul, Units.val_mul]
        have hx' : x = (u : F) := rfl
        rw [hneg v, hx', hneg u, hv]
      filter_upwards [e1, e2, eventually_modulus_eq hx] with y h1 h2 h3
      simp only [gTil, h1, h2, h3]
  · refine HasCompactSupport.intro (isCompact_valBall (-N)) fun x hx => ?_
    by_contra hne
    exact hx (mem_of_gTil_ne_zero E hN' hM hne).1

theorem half_cpow {m : ℝ} (hm : 0 < m) :
    ∃ w : ℂ, w ≠ 0 ∧ ((m : ℂ)) ^ (1 / 2 : ℂ) = w ∧ ((m⁻¹ : ℝ) : ℂ) ^ (1 / 2 : ℂ) = w⁻¹ ∧
      (m : ℂ) = w * w := by
  have hne : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  refine ⟨(m : ℂ) ^ (1 / 2 : ℂ), ?_, rfl, ?_, ?_⟩
  · simpa [Complex.cpow_eq_zero_iff] using hne
  · rw [Complex.ofReal_inv, Complex.inv_cpow _ _ (by
      rw [Complex.arg_ofReal_of_nonneg hm.le]; exact Real.pi_ne_zero.symm)]
  · rw [← Complex.cpow_add _ _ hne]
    norm_num

variable [MeasurableSpace F] [BorelSpace F]

theorem zeta_gTil {η : Fˣ →* ℂˣ} (hη : ∀ a : Fˣ, ((η a : ℂˣ) : ℂ) = nsg E (a : F)) (g : F → ℂ)
    (c : Fˣ →* ℂˣ) :
    localZeta (gTil E g) c (1 / 2) = ((c (-1) : ℂˣ) : ℂ) * localZeta g (η * c⁻¹) (1 / 2) := by
  haveI hlU : LocallyCompactSpace Fˣ := (isOpenEmbedding_units_val (K := F)).locallyCompactSpace
  haveI hsU : SecondCountableTopology Fˣ :=
    (isOpenEmbedding_units_val (K := F)).isEmbedding.secondCountableTopology
  haveI hI : (multHaar F).IsInvInvariant := Measure.IsHaarMeasure.isInvInvariant_of_regular _
  have hs : ∀ a, ((η a : ℂˣ) : ℂ) = 1 ∨ ((η a : ℂˣ) : ℂ) = -1 := fun a => by
    rw [hη, nsg]
    split_ifs <;> simp
  unfold localZeta
  rw [← integral_const_mul]
  set f : Fˣ → ℂ := fun u => gTil E g u * ((c u : ℂˣ) : ℂ) * ((modulus (u : F) : ℝ) : ℂ) ^ (1 / 2 : ℂ)
    with hf
  calc ∫ u, f u ∂multHaar F = ∫ u, f (-1 * u) ∂multHaar F :=
        (integral_mul_left_eq_self f (-1)).symm
    _ = ∫ u, f (-1 * u⁻¹) ∂multHaar F :=
        (integral_inv_eq_self (fun u => f (-1 * u)) (multHaar F)).symm
    _ = _ := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
      have hu : (((-1 : Fˣ) * v⁻¹ : Fˣ) : F) = -(v : F)⁻¹ := by simp
      have hm0 : 0 < ((modulus (v : F) : ℝ≥0) : ℝ) := by exact_mod_cast modulus_pos v.ne_zero
      obtain ⟨w, hw0, hw1, hw2, hw3⟩ := half_cpow hm0
      have hmod : ((modulus (-(v : F)⁻¹) : ℝ≥0) : ℝ) = ((modulus (v : F) : ℝ≥0) : ℝ)⁻¹ := by
        rw [modulus_neg_eq, modulus_inv, NNReal.coe_inv]
      have hn : nsg E (- -(v : F)⁻¹) = ((η v : ℂˣ) : ℂ) := by
        rw [neg_neg, ← Units.val_inv_eq_inv_val, ← hη, map_inv, Units.val_inv_eq_inv_val]
        rcases hs v with h | h <;> simp [h]
      have hg' : g (-(-(v : F)⁻¹)⁻¹) = g v := by simp
      have hcv : ((c v : ℂˣ) : ℂ) ≠ 0 := (c v).ne_zero
      simp only [hf, gTil, hu, hg', hn, hmod]
      rw [map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val, hw2, MonoidHom.mul_apply,
        MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val, hw1]
      push_cast
      rw [inv_inv, hw3]
      field_simp

end GlobalTheory.CompanionTheory.GaussLam.Til

namespace GlobalTheory.CompanionTheory.GaussLam

theorem gTil_schwartzBruhat_zeta : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E] [Algebra.IsSeparable F E] [Fact (Module.finrank F E = 2)] (η : Fˣ →* ℂˣ), Continuous η → (∀ a : Fˣ, ((η a : ℂˣ) : ℂ) = nsg E (a : F)) → ∀ g : F → ℂ, g ∈ schwartzBruhat F → g 0 = 0 → GlobalTheory.CompanionTheory.GaussLam.gTil E g ∈ schwartzBruhat F ∧ ∀ c : Fˣ →* ℂˣ, localZeta (GlobalTheory.CompanionTheory.GaussLam.gTil E g) c (1 / 2) = ((c (-1) : ℂˣ) : ℂ) * localZeta g (η * c⁻¹) (1 / 2) := by
  intro F _ _ _ _ _ _ E _ _ _ _ _ _ _ _ _ _ _ η hc hη g hg h0
  exact ⟨Til.gTil_mem E hc hη hg h0, fun c => Til.zeta_gTil E hη g c⟩

end GlobalTheory.CompanionTheory.GaussLam
