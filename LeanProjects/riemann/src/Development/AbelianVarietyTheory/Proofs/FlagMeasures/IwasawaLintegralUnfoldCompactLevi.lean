import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetHsBall

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

namespace GlobalTheory.IwConst

theorem iwasawa_shift_lintegral {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G]
    (M : Set G) (μM μK : Measure G) [SFinite μK] (δ φ ψ : G → ENNReal)
    (hδ : Measurable δ) (hφ : Measurable φ) (hψ : Measurable ψ) (hM : μM Mᶜ = 0) (l : G)
    (h1 : μM.map (fun g => g * l) = μM) (h2 : μK.map (fun g => l * g) = μK)
    (h3 : ∀ m ∈ M, δ (m * l) = δ m) (u : G) :
    ∫⁻ m, δ m * ∫⁻ k, φ (u * m * k) * ψ k ∂μK ∂μM
      = ∫⁻ m, δ m * ∫⁻ k, φ (u * m * k) * ψ (l * k) ∂μK ∂μM := by
  have hae : ∀ᵐ m ∂μM, m ∈ M := by rw [ae_iff]; exact hM

  have hK : ∀ m, ∫⁻ k, φ (u * m * k) * ψ (l * k) ∂μK
      = ∫⁻ k, φ (u * (m * l⁻¹) * k) * ψ k ∂μK := by
    intro m
    conv_rhs => rw [← h2, show (fun g : G => l * g) = ⇑(MeasurableEquiv.mulLeft l) from rfl,
      lintegral_map_equiv]
    simp [mul_assoc]
  simp_rw [hK]

  conv_rhs => rw [← h1, show (fun g : G => g * l) = ⇑(MeasurableEquiv.mulRight l) from rfl,
    lintegral_map_equiv]
  apply lintegral_congr_ae
  filter_upwards [hae] with m hm
  simp [mul_assoc, h3 m hm]

theorem iwasawa_unfold_lintegral : ∀ (G : Type) [Group G] [MeasurableSpace G] [MeasurableMul₂ G] (M L : Set G) (μN μM μK νL : Measure G) [SFinite μN] [SFinite μM] [SFinite μK] [SFinite νL] (δ φ ψ : G → ENNReal), Measurable δ → Measurable φ → Measurable ψ → μM Mᶜ = 0 → νL Lᶜ = 0 → (∀ l ∈ L, μM.map (fun g => g * l) = μM) → (∀ l ∈ L, μK.map (fun g => l * g) = μK) → (∀ l ∈ L, ∀ m ∈ M, δ (m * l) = δ m) → νL Set.univ * ∫⁻ u, ∫⁻ m, δ m * ∫⁻ k, φ (u * m * k) * ψ k ∂μK ∂μM ∂μN = ∫⁻ u, ∫⁻ m, δ m * ∫⁻ k, φ (u * m * k) * ∫⁻ l, ψ (l * k) ∂νL ∂μK ∂μM ∂μN := by
  intro G _ _ _ M L μN μM μK νL _ _ _ _ δ φ ψ hδ hφ hψ hM hL h1 h2 h3
  have hLae : ∀ᵐ l ∂νL, l ∈ L := by rw [ae_iff]; exact hL

  have hH : Measurable fun p : G × G × G =>
      δ p.2.1 * ∫⁻ k, φ (p.1 * p.2.1 * k) * ψ (p.2.2 * k) ∂μK := by
    refine Measurable.mul (hδ.comp measurable_snd.fst) ?_
    exact Measurable.lintegral_prod_right'
      (f := fun q : (G × G × G) × G => φ (q.1.1 * q.1.2.1 * q.2) * ψ (q.1.2.2 * q.2)) (by fun_prop)
  have hX : Measurable fun p : G × G =>
      ∫⁻ m, δ m * ∫⁻ k, φ (p.1 * m * k) * ψ (p.2 * k) ∂μK ∂μM :=
    Measurable.lintegral_prod_right' (f := fun q : (G × G) × G =>
        δ q.2 * ∫⁻ k, φ (q.1.1 * q.2 * k) * ψ (q.1.2 * k) ∂μK)
      (hH.comp (f := fun q : (G × G) × G => (q.1.1, q.2, q.1.2)) (by fun_prop))

  have step1 : ∀ u m, δ m * ∫⁻ k, φ (u * m * k) * ∫⁻ l, ψ (l * k) ∂νL ∂μK
      = ∫⁻ l, δ m * ∫⁻ k, φ (u * m * k) * ψ (l * k) ∂μK ∂νL := by
    intro u m
    have hg : Measurable fun l => ∫⁻ k, φ (u * m * k) * ψ (l * k) ∂μK :=
      Measurable.lintegral_prod_right' (f := fun q : G × G => φ (u * m * q.2) * ψ (q.1 * q.2))
        (by fun_prop)
    calc δ m * ∫⁻ k, φ (u * m * k) * ∫⁻ l, ψ (l * k) ∂νL ∂μK
        = δ m * ∫⁻ k, ∫⁻ l, φ (u * m * k) * ψ (l * k) ∂νL ∂μK := by
          congr 1
          exact lintegral_congr fun k => (lintegral_const_mul _ (hψ.comp (measurable_mul_const k))).symm
      _ = δ m * ∫⁻ l, ∫⁻ k, φ (u * m * k) * ψ (l * k) ∂μK ∂νL := by
          congr 1
          exact lintegral_lintegral_swap (by
            exact (show Measurable fun q : G × G => φ (u * m * q.1) * ψ (q.2 * q.1) by fun_prop).aemeasurable)
      _ = ∫⁻ l, δ m * ∫⁻ k, φ (u * m * k) * ψ (l * k) ∂μK ∂νL := (lintegral_const_mul _ hg).symm
  have step2 : ∀ u, ∫⁻ m, δ m * ∫⁻ k, φ (u * m * k) * ∫⁻ l, ψ (l * k) ∂νL ∂μK ∂μM
      = ∫⁻ l, ∫⁻ m, δ m * ∫⁻ k, φ (u * m * k) * ψ (l * k) ∂μK ∂μM ∂νL := by
    intro u
    calc _ = ∫⁻ m, ∫⁻ l, δ m * ∫⁻ k, φ (u * m * k) * ψ (l * k) ∂μK ∂νL ∂μM :=
          lintegral_congr fun m => step1 u m
      _ = _ := lintegral_lintegral_swap (by
          exact (hH.comp (f := fun q : G × G => (u, q.1, q.2)) (by fun_prop)).aemeasurable)

  have key : ∀ᵐ l ∂νL, ∫⁻ u, ∫⁻ m, δ m * ∫⁻ k, φ (u * m * k) * ψ (l * k) ∂μK ∂μM ∂μN
      = ∫⁻ u, ∫⁻ m, δ m * ∫⁻ k, φ (u * m * k) * ψ k ∂μK ∂μM ∂μN := by
    filter_upwards [hLae] with l hl
    exact lintegral_congr fun u =>
      (iwasawa_shift_lintegral M μM μK δ φ ψ hδ hφ hψ hM l (h1 l hl) (h2 l hl) (h3 l hl) u).symm
  calc νL Set.univ * ∫⁻ u, ∫⁻ m, δ m * ∫⁻ k, φ (u * m * k) * ψ k ∂μK ∂μM ∂μN
      = ∫⁻ _l, (∫⁻ u, ∫⁻ m, δ m * ∫⁻ k, φ (u * m * k) * ψ k ∂μK ∂μM ∂μN) ∂νL := by
        rw [lintegral_const]; exact mul_comm _ _
    _ = ∫⁻ l, ∫⁻ u, ∫⁻ m, δ m * ∫⁻ k, φ (u * m * k) * ψ (l * k) ∂μK ∂μM ∂μN ∂νL :=
        lintegral_congr_ae (key.mono fun _ hl => hl.symm)
    _ = ∫⁻ u, ∫⁻ l, ∫⁻ m, δ m * ∫⁻ k, φ (u * m * k) * ψ (l * k) ∂μK ∂μM ∂νL ∂μN :=
        (lintegral_lintegral_swap (by exact hX.aemeasurable)).symm
    _ = _ := lintegral_congr fun u => (step2 u).symm

end GlobalTheory.IwConst
