import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntInd
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 GlobalTheory.CompanionTheory.SphTheta
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.SphTheta

section Split

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem intInd_of_mem {x : F} (h : x ∈ 𝒪[F]) : intInd x = 1 := by
  simp [intInd, h]

theorem intInd_of_notMem {x : F} (h : x ∉ 𝒪[F]) : intInd x = 0 := by
  simp [intInd, h]

theorem intInd_congr {x y : F} (h : modulus x = modulus y) : intInd x = intInd y := by
  have hiff : x ∈ 𝒪[F] ↔ y ∈ 𝒪[F] := by
    rw [← modulus_le_one_iff, ← modulus_le_one_iff, h]
  by_cases hx : x ∈ 𝒪[F]
  · rw [intInd_of_mem hx, intInd_of_mem (hiff.1 hx)]
  · rw [intInd_of_notMem hx, intInd_of_notMem (fun hy => hx (hiff.2 hy))]

theorem isLocallyConstant_intInd : IsLocallyConstant (intInd : F → ℂ) := by
  have hO : IsOpen (𝒪[F] : Set F) := by
    rw [← coe_valBall_zero]; exact isOpen_valBall 0
  have hC : IsCompact (𝒪[F] : Set F) := by
    rw [← coe_valBall_zero]; exact isCompact_valBall 0
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  by_cases hx : x ∈ 𝒪[F]
  · filter_upwards [hO.mem_nhds hx] with y hy
    rw [intInd_of_mem hy, intInd_of_mem hx]
  · filter_upwards [hC.isClosed.isOpen_compl.mem_nhds hx] with y hy
    rw [intInd_of_notMem hy, intInd_of_notMem hx]

theorem isLocallyConstant_phiS : IsLocallyConstant (phiS : F × F → ℂ) :=
  (isLocallyConstant_intInd.comp_continuous continuous_fst).mul
    (isLocallyConstant_intInd.comp_continuous continuous_snd)

theorem hasCompactSupport_phiS : HasCompactSupport (phiS : F × F → ℂ) := by
  have hC : IsCompact (𝒪[F] : Set F) := by
    rw [← coe_valBall_zero]; exact isCompact_valBall 0
  refine HasCompactSupport.intro (hC.prod hC) fun p hp => ?_
  unfold phiS
  by_cases h1 : p.1 ∈ 𝒪[F]
  · have h2 : p.2 ∉ 𝒪[F] := fun h2 => hp ⟨h1, h2⟩
    rw [intInd_of_notMem h2, mul_zero]
  · rw [intInd_of_notMem h1, zero_mul]

theorem mem_units_iff_modulus {u : Fˣ} :
    u ∈ unitFiltrationUnits F 0 ↔ modulus (u : F) = 1 := by
  rw [mem_unitFiltrationUnits_zero_iff_ord, modulus_of_ne_zero u.ne_zero]
  constructor
  · intro h; rw [h]; simp
  · intro h
    have h1 : (residueCard F : NNReal) ^ (-ord (u : F)) = (residueCard F : NNReal) ^ (0 : ℤ) := by
      rw [h, zpow_zero]
    have := zpow_right_injective₀ (zero_lt_one.trans one_lt_residueCard_nnreal)
      one_lt_residueCard_nnreal.ne' h1
    omega

theorem char_eq_one {c : Fˣ →* ℂˣ} (hc : IsUnramifiedChar c) {u : Fˣ}
    (hu : modulus (u : F) = 1) : ((c u : ℂˣ) : ℂ) = 1 := by
  have : c u = 1 := hc (mem_units_iff_modulus.2 hu)
  rw [this, Units.val_one]

def sphJ (c₁ c₂ : Fˣ →* ℂˣ) (D m : F) (u : Fˣ) : ℂ :=
  intInd (m * u)⁻¹ * intInd (D * u / m) * ((c₁ u : ℂˣ) : ℂ) * (((c₂ u)⁻¹ : ℂˣ) : ℂ)

theorem sphJ_congr (c₁ c₂ : Fˣ →* ℂˣ) {D D' m m' : F} (hD : modulus D = modulus D')
    (hm : modulus m = modulus m') : sphJ c₁ c₂ D m = sphJ c₁ c₂ D' m' := by
  funext u
  unfold sphJ
  rw [intInd_congr (x := (m * u)⁻¹) (y := (m' * u)⁻¹) (by simp only [modulus_inv, modulus_mul, hm]),
    intInd_congr (x := D * u / m) (y := D' * u / m')
      (by simp only [div_eq_mul_inv, modulus_inv, modulus_mul, hm, hD])]

theorem sphJ_eq_zero (c₁ c₂ : Fˣ →* ℂˣ) {D m : F} (hm : m ≠ 0)
    (h : ¬ modulus D ≤ modulus m ^ 2) (u : Fˣ) : sphJ c₁ c₂ D m u = 0 := by
  unfold sphJ
  by_cases h1 : (m * u)⁻¹ ∈ 𝒪[F]
  · by_cases h2 : D * u / m ∈ 𝒪[F]
    · exfalso
      apply h
      have hm0 := modulus_pos hm
      have hu0 := modulus_pos u.ne_zero
      have a1 := modulus_le_one_iff.2 h1
      have a2 := modulus_le_one_iff.2 h2
      rw [modulus_inv, modulus_mul] at a1
      rw [div_eq_mul_inv, modulus_mul, modulus_mul, modulus_inv] at a2
      have b1 : 1 ≤ modulus m * modulus (u : F) :=
        (inv_le_one₀ (mul_pos hm0 hu0)).1 a1
      have b2 : modulus D * modulus (u : F) ≤ modulus m := by
        have := mul_le_mul_of_nonneg_right a2 (le_of_lt hm0)
        rwa [mul_assoc, inv_mul_cancel₀ hm0.ne', mul_one, one_mul] at this
      calc modulus D ≤ modulus D * (modulus m * modulus (u : F)) := le_mul_of_one_le_right zero_le b1
        _ = modulus m * (modulus D * modulus (u : F)) := by ring
        _ ≤ modulus m * modulus m := mul_le_mul_right b2 _
        _ = modulus m ^ 2 := by ring
    · rw [intInd_of_notMem h2]; simp
  · rw [intInd_of_notMem h1]; simp

end Split

theorem spherical_split_of_pointwise :
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (χ : AddChar F Circle) (c₁ c₂ : Fˣ →* ℂˣ), Ad3.IsStd χ → IsUnramifiedChar c₁ → IsUnramifiedChar c₂ → (∀ (g : GL (Fin 2) F) (u : Fˣ), Ad3.K.GL2LocalData.rW χ Ad3.K.GL2LocalData.swapE ((selfDualMeasure χ).prod (selfDualMeasure χ)) 1 (g.val 0 0 / (g.val).det) (g.val 0 1) (g.val 1 0 / (g.val).det) (g.val 1 1) (fun x => phiS (x * ((g.val).det, 1))) ((u : F), ((u⁻¹ : Fˣ) : F)) = (((modulus (mRow g) : ℝ)⁻¹ : ℝ) : ℂ) * (χ (xRow g) : ℂ) * intInd (mRow g * u)⁻¹ * intInd ((g.val).det * u / mRow g)) → (∀ (g k : GL (Fin 2) F), k ∈ GLnLocal.integralGL F 2 → mRow g ≠ 0 ∧ modulus ((g * k).val).det = modulus (g.val).det ∧ modulus (mRow (g * k)) = modulus (mRow g) ∧ (modulus (g.val).det ≤ modulus (mRow g) ^ 2 → xRow (g * k) - xRow g ∈ 𝒪[F])) → ∃ W ∈ Ad3.K.GL2LocalData.VWS χ c₁ c₂, Ad3.K.QuadraticBaseChangeGL3.SphN W := by
  intro F _ _ _ _ _ _ χ c₁ c₂ hχ hc₁ hc₂ H1 H2
  have key : ∀ g : GL (Fin 2) F, GL2LocalData.WcS χ c₁ c₂ phiS g =
      ((c₁ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * mp (Matrix.GeneralLinearGroup.det g) (1 / 2) *
        ((((modulus (mRow g) : ℝ)⁻¹ : ℝ) : ℂ) * (χ (xRow g) : ℂ) *
          ∫ u, sphJ c₁ c₂ (g.val).det (mRow g) u ∂multHaar F) := by
    intro g
    unfold GL2LocalData.WcS
    congr 1
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [H1 g u, sphJ]
    ring
  refine ⟨GL2LocalData.WcS χ c₁ c₂ phiS, Submodule.subset_span
    ⟨phiS, isLocallyConstant_phiS, hasCompactSupport_phiS, 1, by simp⟩, ?_, ?_⟩
  · intro k hk g
    obtain ⟨hm, hD, hM, hx⟩ := H2 g k hk
    have hk1 : modulus (k.val).det = 1 := by
      have := (H2 1 k hk).2.1
      simpa using this
    have hdet : Matrix.GeneralLinearGroup.det (g * k) =
        Matrix.GeneralLinearGroup.det g * Matrix.GeneralLinearGroup.det k := map_mul _ _ _
    have hc : ((c₁ (Matrix.GeneralLinearGroup.det (g * k)) : ℂˣ) : ℂ) =
        ((c₁ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) := by
      rw [hdet, map_mul, Units.val_mul, char_eq_one hc₁ (u := Matrix.GeneralLinearGroup.det k) hk1, mul_one]
    have hmp : mp (Matrix.GeneralLinearGroup.det (g * k)) (1 / 2) =
        mp (Matrix.GeneralLinearGroup.det g) (1 / 2) := by
      unfold mp
      have : modulus ((Matrix.GeneralLinearGroup.det (g * k) : Fˣ) : F) =
          modulus ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) := hD
      rw [this]
    rw [key, key, hc, hmp, hM, sphJ_congr c₁ c₂ hD hM]
    by_cases hle : modulus (g.val).det ≤ modulus (mRow g) ^ 2
    · have ht := hx hle
      have h1 : χ (xRow (g * k) - xRow g) = 1 := by
        have h := isTrivialOn_addCharConductor hχ.1 hχ.2.1
        rw [hχ.2.2] at h
        exact h _ (mem_valBall_zero_iff.2 ht)
      have h2 : χ (xRow (g * k)) = χ (xRow g) := by
        have e : xRow (g * k) = (xRow (g * k) - xRow g) + xRow g := by ring
        rw [e, AddChar.map_add_eq_mul, h1, one_mul]
      rw [h2]
    · have h0 : (fun u => sphJ c₁ c₂ (g.val).det (mRow g) u) = fun _ => 0 :=
        funext (sphJ_eq_zero c₁ c₂ hm hle)
      simp only [h0, integral_zero, mul_zero]
  · rw [key]
    have hm1 : mRow (1 : GL (Fin 2) F) = 1 := by
      simp [mRow]
    have hx1 : xRow (1 : GL (Fin 2) F) = 0 := by
      simp [xRow]
    have hJ : (fun u => sphJ c₁ c₂ ((1 : GL (Fin 2) F).val).det 1 u) =
        (unitFiltrationUnits F 0 : Set Fˣ).indicator (fun _ => (1 : ℂ)) := by
      funext u
      by_cases hu : u ∈ (unitFiltrationUnits F 0 : Set Fˣ)
      · have hu1 : modulus (u : F) = 1 := mem_units_iff_modulus.1 hu
        rw [Set.indicator_of_mem hu]
        have e1 : ((c₂ u)⁻¹ : ℂˣ) = 1 := by
          have : c₂ u = 1 := hc₂ (mem_units_iff_modulus.2 hu1)
          rw [this, inv_one]
        unfold sphJ
        rw [e1, char_eq_one hc₁ hu1, intInd_of_mem, intInd_of_mem]
        · simp
        · rw [← modulus_le_one_iff]; simp [modulus_mul, hu1]
        · rw [← modulus_le_one_iff]; simp [modulus_mul, modulus_inv, hu1]
      · rw [Set.indicator_of_notMem hu]
        have hu1 : modulus (u : F) ≠ 1 := fun h => hu (mem_units_iff_modulus.2 h)
        unfold sphJ
        rcases lt_or_gt_of_ne hu1 with h | h
        · rw [intInd_of_notMem (x := (1 * (u : F))⁻¹)]
          · simp
          · rw [← modulus_le_one_iff, one_mul, modulus_inv, not_le]
            exact (one_lt_inv₀ (modulus_pos u.ne_zero)).2 h
        · rw [intInd_of_notMem (x := ((1 : GL (Fin 2) F).val).det * u / 1)]
          · simp
          · rw [← modulus_le_one_iff, not_le]
            simpa using h
    have hmeas : MeasurableSet (unitFiltrationUnits F 0 : Set Fˣ) := by
      exact (isOpen_unitFiltrationUnits 0).measurableSet
    have hint : ∫ u, sphJ c₁ c₂ ((1 : GL (Fin 2) F).val).det 1 u ∂multHaar F = 1 := by
      rw [hJ, integral_indicator_const _ hmeas]
      simp [Measure.real, multHaar_unitFiltrationUnits_zero]
    rw [hm1, hx1, hint]
    simp [mp]

end GlobalTheory.CompanionTheory.SphTheta
