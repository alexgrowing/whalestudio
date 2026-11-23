import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.LocalFunctionalEquationFinite

noncomputable section
open MeasureTheory GroundTheory.LocalField GroundTheory.Automorphic Ad3
open scoped ValuativeRel Topology NNReal

namespace GlobalTheory.CompanionTheory.GamEquiv

variable {F F' : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Field F'] [ValuativeRel F'] [TopologicalSpace F'] [IsNonarchimedeanLocalField F']

theorem ord_pow_nat {x : F} (hx : x ≠ 0) (n : ℕ) : ord (x ^ n) = n * ord x := by
  induction n with
  | zero => simp [ord_one]
  | succ k ih => rw [pow_succ, ord_mul (pow_ne_zero _ hx) hx, ih]; push_cast; ring

theorem ord_zpow' {x : F} (hx : x ≠ 0) (k : ℤ) : ord (x ^ k) = k * ord x := by
  have := ord_units_zpow (Units.mk0 x hx) k
  simpa [Units.val_zpow_eq_zpow_val] using this

theorem ord_pos_iff_tendsto {x : F} (hx : x ≠ 0) :
    0 < ord x ↔ Filter.Tendsto (fun n : ℕ => x ^ n) Filter.atTop (𝓝 0) := by
  constructor
  · intro h
    rw [(hasBasis_nhds_zero_valBall (K := F)).tendsto_right_iff]
    intro i _
    filter_upwards [Filter.eventually_ge_atTop i.toNat] with n hn
    rw [SetLike.mem_coe, mem_valBall_iff_le_ord (pow_ne_zero _ hx), ord_pow_nat hx]
    have : (i.toNat : ℤ) ≤ n := by exact_mod_cast hn
    have h2 : i ≤ n := by omega
    nlinarith
  · intro h
    by_contra hc
    have hm := h (valBall_mem_nhds (K := F) 1)
    obtain ⟨n, hn⟩ := (Filter.eventually_atTop.mp (Filter.mem_map.mp hm))
    have := hn (n + 1) (by omega)
    simp only [Set.mem_preimage, SetLike.mem_coe] at this
    rw [mem_valBall_iff_le_ord (pow_ne_zero _ hx), ord_pow_nat hx] at this
    push_cast at this
    nlinarith

section Tr

variable (φ : F ≃+* F') (h1 : Continuous φ) (h2 : Continuous φ.symm)
include h1 h2

theorem ord_pos_iff {x : F} (hx : x ≠ 0) : 0 < ord (φ x) ↔ 0 < ord x := by
  have hx' : φ x ≠ 0 := by simpa using hx
  rw [ord_pos_iff_tendsto hx, ord_pos_iff_tendsto hx']
  constructor
  · intro h
    simpa [Function.comp_def, map_pow] using ((h2.tendsto' _ _ (by simp)).comp h)
  · intro h
    simpa [Function.comp_def, map_pow] using ((h1.tendsto' _ _ (by simp)).comp h)

theorem ord_eq_zero_iff {x : F} (hx : x ≠ 0) : ord (φ x) = 0 ↔ ord x = 0 := by
  have hx' : φ x ≠ 0 := by simpa using hx
  have a := ord_pos_iff φ h1 h2 hx
  have b := ord_pos_iff φ h1 h2 (inv_ne_zero hx)
  rw [map_inv₀, ord_inv hx, ord_inv hx'] at b
  omega

theorem ord_map {x : F} (hx : x ≠ 0) : ord (φ x) = ord x := by
  obtain ⟨π, hπ0, hπ⟩ := exists_ord_eq F 1
  obtain ⟨π', hπ0', hπ'⟩ := exists_ord_eq F' 1
  set ρ := φ.symm π' with hρ
  have hρ0 : ρ ≠ 0 := by simpa [hρ] using hπ0'
  have hφρ : φ ρ = π' := by simp [hρ]
  have hφπ0 : φ π ≠ 0 := by simpa using hπ0
  have hm : 0 < ord (φ π) := (ord_pos_iff φ h1 h2 hπ0).mpr (by omega)
  have hn : 0 < ord ρ := (ord_pos_iff φ h1 h2 hρ0).mp (by rw [hφρ]; omega)
  set m := ord (φ π) with hmdef
  have hz : ord (π * ρ ^ (-m)) = 0 := by
    refine (ord_eq_zero_iff φ h1 h2 (mul_ne_zero hπ0 (zpow_ne_zero _ hρ0))).mp ?_
    rw [map_mul, map_zpow₀, hφρ, ord_mul hφπ0 (zpow_ne_zero _ hπ0'), ord_zpow' hπ0', hπ', ← hmdef]
    ring
  rw [ord_mul hπ0 (zpow_ne_zero _ hρ0), ord_zpow' hρ0, hπ] at hz
  have hm1 : m = 1 := by
    have hmn : m * ord ρ = 1 := by linarith
    nlinarith
  have hw : ord (x * π ^ (-ord x)) = 0 := by
    rw [ord_mul hx (zpow_ne_zero _ hπ0), ord_zpow' hπ0, hπ]
    ring
  have hw' := (ord_eq_zero_iff φ h1 h2 (mul_ne_zero hx (zpow_ne_zero _ hπ0))).mpr hw
  have hx' : φ x ≠ 0 := by simpa using hx
  rw [map_mul, map_zpow₀, ord_mul hx' (zpow_ne_zero _ hφπ0), ord_zpow' hφπ0, ← hmdef, hm1] at hw'
  linarith

theorem map_mem_valBall_iff (n : ℤ) {x : F} : φ x ∈ valBall F' n ↔ x ∈ valBall F n := by
  by_cases hx : x = 0
  · simp [hx, zero_mem]
  have hx' : φ x ≠ 0 := by simpa using hx
  rw [mem_valBall_iff_le_ord hx, mem_valBall_iff_le_ord hx', ord_map φ h1 h2 hx]

theorem preimage_valBall (n : ℤ) : φ ⁻¹' (valBall F' n : Set F') = valBall F n := by
  ext x
  exact map_mem_valBall_iff φ h1 h2 n

section Meas

variable [MeasurableSpace F] [BorelSpace F] [MeasurableSpace F'] [BorelSpace F']

theorem map_haarIntegers : Measure.map φ (haarIntegers F) = haarIntegers F' := by
  let e : F ≃ₜ+ F' := { φ.toAddEquiv with continuous_toFun := h1, continuous_invFun := h2 }
  have : (Measure.map e (haarIntegers F)).IsAddHaarMeasure := e.isAddHaarMeasure_map _
  have h : (Measure.map φ (haarIntegers F)).IsAddHaarMeasure := this
  have h3 := eq_smul_haarIntegers (Measure.map φ (haarIntegers F))
  rw [← coe_valBall_zero, Measure.map_apply h1.measurable (measurableSet_valBall 0),
    preimage_valBall φ h1 h2, coe_valBall_zero, haarIntegers_integers, one_smul] at h3
  exact h3

theorem residueCard_eq : residueCard F = residueCard F' := by
  have h : Measure.map φ (haarIntegers F) (valBall F' 1 : Set F') = haarIntegers F' (valBall F' 1 : Set F') := by
    rw [map_haarIntegers φ h1 h2]
  rw [Measure.map_apply h1.measurable (measurableSet_valBall 1), preimage_valBall φ h1 h2,
    haarIntegers_valBall, haarIntegers_valBall] at h
  have h' : ((residueCard F : ℝ≥0) ^ (-1 : ℤ)) = ((residueCard F' : ℝ≥0) ^ (-1 : ℤ)) := by
    exact_mod_cast h
  rw [zpow_neg_one, zpow_neg_one, inv_inj] at h'
  exact_mod_cast h'

theorem modulus_map (x : F) : modulus (φ x) = modulus x := by
  by_cases hx : x = 0
  · simp [hx]
  have hx' : φ x ≠ 0 := by simpa using hx
  rw [modulus_of_ne_zero hx, modulus_of_ne_zero hx', ord_map φ h1 h2 hx, residueCard_eq φ h1 h2]

omit [MeasurableSpace F] [BorelSpace F] [MeasurableSpace F'] [BorelSpace F'] in
theorem addCharConductor_comp (ψ : AddChar F' Circle) :
    addCharConductor (ψ.compAddMonoidHom (φ : F →+ F')) = addCharConductor ψ := by
  unfold addCharConductor
  congr 1
  ext n
  constructor
  · intro h y hy
    have := h (φ.symm y) ((map_mem_valBall_iff φ h1 h2 n).mp (by simpa using hy))
    simpa using this
  · intro h x hx
    exact h (φ x) ((map_mem_valBall_iff φ h1 h2 n).mpr hx)

theorem map_selfDualMeasure (ψ : AddChar F' Circle) :
    Measure.map φ (selfDualMeasure (ψ.compAddMonoidHom (φ : F →+ F'))) = selfDualMeasure ψ := by
  unfold selfDualMeasure
  rw [Measure.map_smul, map_haarIntegers φ h1 h2, addCharConductor_comp φ h1 h2,
    residueCard_eq φ h1 h2]

end Meas

section Char

abbrev um : Fˣ →* F'ˣ := Units.map (φ : F →* F')

omit h1 h2 in
theorem um_surjective (v : F'ˣ) : ∃ u : Fˣ, um φ u = v :=
  ⟨Units.map (φ.symm : F' →* F) v, by ext; simp⟩

theorem mem_filt_iff (n : ℕ) (u : Fˣ) :
    um φ u ∈ unitFiltrationUnits F' n ↔ u ∈ unitFiltrationUnits F n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [mem_unitFiltrationUnits_zero_iff_ord, mem_unitFiltrationUnits_zero_iff_ord]
    exact ord_eq_zero_iff φ h1 h2 u.ne_zero
  · rw [mem_unitFiltrationUnits_iff_valBall hn, mem_unitFiltrationUnits_iff_valBall hn,
      ← map_mem_valBall_iff φ h1 h2]
    simp

theorem filt_le_ker_iff (μ : F'ˣ →* ℂˣ) (n : ℕ) :
    unitFiltrationUnits F n ≤ (μ.comp (um φ)).ker ↔ unitFiltrationUnits F' n ≤ μ.ker := by
  constructor
  · intro h v hv
    obtain ⟨u, rfl⟩ := um_surjective φ v
    exact h ((mem_filt_iff φ h1 h2 n u).mp hv)
  · intro h u hu
    exact h ((mem_filt_iff φ h1 h2 n u).mpr hu)

theorem isUnramified_comp_iff (μ : F'ˣ →* ℂˣ) :
    IsUnramifiedChar (μ.comp (um φ)) ↔ IsUnramifiedChar μ :=
  filt_le_ker_iff φ h1 h2 μ 0

theorem conductor_comp (μ : F'ˣ →* ℂˣ) :
    quasiCharConductor (μ.comp (um φ)) = quasiCharConductor μ := by
  unfold quasiCharConductor
  congr 1
  ext n
  exact filt_le_ker_iff φ h1 h2 μ n

theorem unif_comp {μ : F'ˣ →* ℂˣ} (hμ : IsUnramifiedChar μ) :
    (μ.comp (um φ)) (unifUnit F) = μ (unifUnit F') := by
  have hord : ord (((um φ (unifUnit F)) * (unifUnit F')⁻¹ : F'ˣ) : F') = 0 := by
    rw [ord_units_mul, ord_units_inv, ord_unifUnit]
    have : ord ((um φ (unifUnit F) : F'ˣ) : F') = ord (φ (unifUnit F : F)) := rfl
    rw [this, ord_map φ h1 h2 (unifUnit F).ne_zero, ord_unifUnit]
    ring
  have := isUnramifiedChar_iff.mp hμ _ hord
  rw [map_mul, map_inv, mul_inv_eq_one] at this
  exact this

variable [MeasurableSpace F] [BorelSpace F] [MeasurableSpace F'] [BorelSpace F']

theorem localLFactor_comp (μ : F'ˣ →* ℂˣ) (s : ℂ) :
    localLFactor (μ.comp (um φ)) s = localLFactor μ s := by
  by_cases hμ : IsUnramifiedChar μ
  · rw [localLFactor_of_isUnramified hμ,
      localLFactor_of_isUnramified ((isUnramified_comp_iff φ h1 h2 μ).mpr hμ),
      unif_comp φ h1 h2 hμ, residueCard_eq φ h1 h2]
  · rw [localLFactor_of_not_isUnramified hμ,
      localLFactor_of_not_isUnramified (mt (isUnramified_comp_iff φ h1 h2 μ).mp hμ)]

omit h1 h2 [MeasurableSpace F] [BorelSpace F] [MeasurableSpace F'] [BorelSpace F'] in
theorem quasiCharExt_comp (μ : F'ˣ →* ℂˣ) (x : F) :
    quasiCharExt (μ.comp (um φ))⁻¹ x = quasiCharExt μ⁻¹ (φ x) := by
  by_cases hx : x = 0
  · simp [quasiCharExt, hx]
  have e : φ x = ((um φ (Units.mk0 x hx) : F'ˣ) : F') := rfl
  rw [e, quasiCharExt_units]
  conv_lhs => rw [show x = ((Units.mk0 x hx : Fˣ) : F) from rfl, quasiCharExt_units]
  rfl

theorem localEpsilon_comp (ψ : AddChar F' Circle) (μ : F'ˣ →* ℂˣ) (s : ℂ) :
    localEpsilon (μ.comp (um φ)) (ψ.compAddMonoidHom (φ : F →+ F')) s = localEpsilon μ ψ s := by
  by_cases hμ : IsUnramifiedChar μ
  · rw [localEpsilon_of_isUnramified hμ,
      localEpsilon_of_isUnramified ((isUnramified_comp_iff φ h1 h2 μ).mpr hμ),
      unif_comp φ h1 h2 hμ, residueCard_eq φ h1 h2, addCharConductor_comp φ h1 h2]
  · rw [localEpsilon_of_not_isUnramified hμ,
      localEpsilon_of_not_isUnramified (mt (isUnramified_comp_iff φ h1 h2 μ).mp hμ),
      addCharConductor_comp φ h1 h2, conductor_comp φ h1 h2, ← map_selfDualMeasure φ h1 h2 ψ]
    let e : F ≃ₜ F' := { φ.toEquiv with continuous_toFun := h1, continuous_invFun := h2 }
    have hemb : MeasurableEmbedding φ := e.measurableEmbedding
    rw [hemb.setIntegral_map]
    have hpre : φ ⁻¹' ((valBall F' (addCharConductor ψ - quasiCharConductor μ) : Set F') \
        valBall F' (addCharConductor ψ - quasiCharConductor μ + 1)) =
        (valBall F (addCharConductor ψ - quasiCharConductor μ) : Set F) \
        valBall F (addCharConductor ψ - quasiCharConductor μ + 1) := by
      rw [Set.preimage_diff, preimage_valBall φ h1 h2, preimage_valBall φ h1 h2]
    rw [hpre]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    rw [quasiCharExt_comp, modulus_map φ h1 h2]
    rfl

end Char

end Tr

theorem gam_equiv : ∀ (F F' : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] [Field F'] [ValuativeRel F'] [TopologicalSpace F'] [IsNonarchimedeanLocalField F'] [MeasurableSpace F'] [BorelSpace F'] (φ : F ≃+* F'), Continuous φ → Continuous φ.symm → ∀ ψ : AddChar F' Circle, Continuous ψ → ψ ≠ 1 → ∀ μ : F'ˣ →* ℂˣ, IsUnit1 μ → ∀ s : ℂ, gam (ψ.compAddMonoidHom (φ : F →+ F')) (μ.comp (Units.map (φ : F →* F'))) s = gam ψ μ s := by
  intro F F' _ _ _ _ _ _ _ _ _ _ _ _ φ h1 h2 ψ _ _ μ _ s
  have hinv : (μ.comp (Units.map (φ : F →* F')))⁻¹ = (μ⁻¹).comp (Units.map (φ : F →* F')) := rfl
  unfold gam
  rw [hinv, localLFactor_comp φ h1 h2, localLFactor_comp φ h1 h2, localEpsilon_comp φ h1 h2]

end GlobalTheory.CompanionTheory.GamEquiv
