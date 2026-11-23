import Mathlib

open MeasureTheory

namespace GlobalTheory

theorem iwasawa_slice_lintegral_le :
    ∀ (G : Type) [Group G] [MeasurableSpace G] [MeasurableMul₂ G] (N M K : Subgroup G) (μN μM μK : Measure G) [SFinite μN] [SFinite μM] [SFinite μK] (δ : G → ENNReal) (κ : G → G) (D DN DM : Set G), Measurable δ → Measurable κ → MeasurableSet DN → MeasurableSet DM → μN (N : Set G)ᶜ = 0 → μM (M : Set G)ᶜ = 0 → μK (K : Set G)ᶜ = 0 → μK Set.univ = 1 → (∀ k ∈ K, κ k ∈ K ⊓ M) → (∀ l ∈ K ⊓ M, μM.map (fun g => g * l) = μM) → (∀ l ∈ K ⊓ M, ∀ m ∈ M, δ (m * l) = δ m) → (∀ u ∈ N, ∀ m ∈ M, ∀ k ∈ K, u * m * k ∈ D → u ∈ DN ∧ m * κ k ∈ DM) → ∫⁻ u, ∫⁻ m, δ m * ∫⁻ k, D.indicator (1 : G → ENNReal) (u * m * k) ∂μK ∂μM ∂μN ≤ μN DN * ∫⁻ m in DM, δ m ∂μM := by
  intro G _ _ _ N M K μN μM μK _ _ _ δ κ D DN DM hδ hκ hDN hDM hN hM hK hK1 hκK hinv hδinv hD
  have aeM : ∀ᵐ m ∂μM, m ∈ (M : Set G) := mem_ae_iff.2 hM
  have aeK : ∀ᵐ k ∂μK, k ∈ (K : Set G) := mem_ae_iff.2 hK
  have aeN : ∀ᵐ u ∂μN, u ∈ (N : Set G) := mem_ae_iff.2 hN

  have htrans : ∀ l ∈ K ⊓ M,
      ∫⁻ m, δ m * DM.indicator (1 : G → ENNReal) (m * l) ∂μM = ∫⁻ m in DM, δ m ∂μM := by
    intro l hl
    have hfun : (fun m => δ m * DM.indicator (1 : G → ENNReal) (m * l))
        =ᵐ[μM] fun m => DM.indicator δ (m * l) := by
      filter_upwards [aeM] with m hm
      have hδml := hδinv l hl m hm
      by_cases hml : m * l ∈ DM
      · simp [hml, hδml]
      · simp [hml]
    rw [lintegral_congr_ae hfun, ← lintegral_map (hδ.indicator hDM) (measurable_mul_const l),
      hinv l hl, lintegral_indicator hDM]

  have hF : Measurable (Function.uncurry
      (fun (m k : G) => δ m * DM.indicator (1 : G → ENNReal) (m * κ k))) :=
    (hδ.comp measurable_fst).mul
      ((measurable_one.indicator hDM).comp (measurable_fst.mul (hκ.comp measurable_snd)))

  have hinner : ∀ u ∈ (N : Set G),
      ∫⁻ m, δ m * ∫⁻ k, D.indicator (1 : G → ENNReal) (u * m * k) ∂μK ∂μM
        ≤ DN.indicator (fun _ => ∫⁻ m in DM, δ m ∂μM) u := by
    intro u hu
    by_cases huD : u ∈ DN
    · rw [Set.indicator_of_mem huD]
      calc ∫⁻ m, δ m * ∫⁻ k, D.indicator (1 : G → ENNReal) (u * m * k) ∂μK ∂μM
          ≤ ∫⁻ m, δ m * ∫⁻ k, DM.indicator (1 : G → ENNReal) (m * κ k) ∂μK ∂μM := by
            apply lintegral_mono_ae
            filter_upwards [aeM] with m hm
            gcongr δ m * ?_
            apply lintegral_mono_ae
            filter_upwards [aeK] with k hk
            by_cases hmem : u * m * k ∈ D
            · have h2 := (hD u hu m hm k hk hmem).2
              simp [hmem, h2]
            · simp [hmem]
        _ = ∫⁻ m, ∫⁻ k, δ m * DM.indicator (1 : G → ENNReal) (m * κ k) ∂μK ∂μM := by
            apply lintegral_congr
            intro m
            have hmeas : Measurable (fun k => DM.indicator (1 : G → ENNReal) (m * κ k)) :=
              (measurable_one.indicator hDM).comp (measurable_const.mul hκ)
            exact (lintegral_const_mul (δ m) hmeas).symm
        _ = ∫⁻ k, ∫⁻ m, δ m * DM.indicator (1 : G → ENNReal) (m * κ k) ∂μM ∂μK :=
            lintegral_lintegral_swap hF.aemeasurable
        _ = ∫⁻ _k, ∫⁻ m in DM, δ m ∂μM ∂μK := by
            apply lintegral_congr_ae
            filter_upwards [aeK] with k hk
            exact htrans (κ k) (hκK k hk)
        _ = ∫⁻ m in DM, δ m ∂μM := by
            rw [lintegral_const, hK1, mul_one]
    · have hind : DN.indicator (fun _ => ∫⁻ m in DM, δ m ∂μM) u = 0 := by
        simp [huD]
      rw [hind]
      calc ∫⁻ m, δ m * ∫⁻ k, D.indicator (1 : G → ENNReal) (u * m * k) ∂μK ∂μM
          ≤ ∫⁻ _m, (0 : ENNReal) ∂μM := by
            apply lintegral_mono_ae
            filter_upwards [aeM] with m hm
            have hae : (fun k => D.indicator (1 : G → ENNReal) (u * m * k))
                =ᵐ[μK] fun _ => (0 : ENNReal) := by
              filter_upwards [aeK] with k hk
              have hmem : u * m * k ∉ D := fun h => huD (hD u hu m hm k hk h).1
              simp [hmem]
            rw [lintegral_congr_ae hae, lintegral_zero, mul_zero]
        _ = 0 := lintegral_zero
  calc ∫⁻ u, ∫⁻ m, δ m * ∫⁻ k, D.indicator (1 : G → ENNReal) (u * m * k) ∂μK ∂μM ∂μN
      ≤ ∫⁻ u, DN.indicator (fun _ => ∫⁻ m in DM, δ m ∂μM) u ∂μN := by
        apply lintegral_mono_ae
        filter_upwards [aeN] with u hu
        exact hinner u hu
    _ = μN DN * ∫⁻ m in DM, δ m ∂μM := by
        rw [lintegral_indicator hDN, setLIntegral_const]
        exact mul_comm _ _

end GlobalTheory
