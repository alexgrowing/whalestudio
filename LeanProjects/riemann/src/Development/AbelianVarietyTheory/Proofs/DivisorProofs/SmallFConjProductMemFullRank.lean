import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRankCoinvariantInducedIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRankNormalFormOrbit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRankZetaSurjective
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

namespace GlobalTheory.FullRankCoinv

theorem smallF_mul_conj_mem_fullRk : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
    (n d : ℕ) (ν : kˣ →* ℂˣ), n ≤ d → GlobalTheory.SmGL.IsSmoothChar ν →
    ∀ Ψ₁ ∈ GlobalTheory.FullRankCoinv.fullRk k n d, ∀ Ψ₂ ∈ GlobalTheory.FullRankCoinv.fullRk k n d,
      (fun Y => GlobalTheory.SplitFlip.smallF (GlobalTheory.SplitFlip.haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν Ψ₁ Y * (starRingEnd ℂ) (Ψ₂ Y))
        ∈ GlobalTheory.FullRankCoinv.fullRk k n d := by
  intro k _ _ _ _ _ _ n d ν hnd hν Ψ₁ hΨ₁ Ψ₂ hΨ₂
  obtain ⟨U, hU, hinv⟩ := GlobalTheory.FullRankCoinv.sb_right_invariant k n d Ψ₁ hΨ₁.1
  have hF : ∀ (Y : Matrix (Fin n) (Fin d) k), ∀ u ∈ U,
      GlobalTheory.SplitFlip.smallF (GlobalTheory.SplitFlip.haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν Ψ₁ (Y * u.val) =
        GlobalTheory.SplitFlip.smallF (GlobalTheory.SplitFlip.haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν Ψ₁ Y := by
    intro Y u hu
    simp only [GlobalTheory.SplitFlip.smallF]
    congr 1; funext g
    rw [← Matrix.mul_assoc, hinv u hu]
  refine ⟨⟨?_, ?_⟩, fun Y hY => ?_⟩
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro Y
    have h2 := hΨ₂.1.1.eventually_eq Y
    by_cases hY : Y.rank = n
    · obtain ⟨h, rfl⟩ := GlobalTheory.FullRankCoinv.exists_eq_normal_form_mul_of_rank_eq k n d hnd Y hY
      set V : Set (GL (Fin d) k) := {u | h⁻¹ * u * h ∈ U} with hVdef
      have hV : V ∈ 𝓝 1 := by
        have hc : Continuous fun u : GL (Fin d) k => h⁻¹ * u * h :=
          (continuous_const.mul continuous_id).mul continuous_const
        have := hc.tendsto 1
        simp only [mul_one, inv_mul_cancel] at this
        exact this hU
      have ht : Filter.Tendsto (fun Z : Matrix (Fin n) (Fin d) k => Z * (h⁻¹).val)
          (𝓝 (GlobalTheory.FullRankCoinv.Y0 k n d * h.val)) (𝓝 (GlobalTheory.FullRankCoinv.Y0 k n d)) := by
        have := ((continuous_id.matrix_mul continuous_const :
          Continuous fun Z : Matrix (Fin n) (Fin d) k => Z * (h⁻¹).val)).tendsto (GlobalTheory.FullRankCoinv.Y0 k n d * h.val)
        simpa only [id, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one] using this
      filter_upwards [ht (GlobalTheory.FullRankOnto.eventually_Y0_mul hnd hV), h2] with Z hZ hZ2
      obtain ⟨u, hu, e⟩ := hZ
      have e' : Z = (GlobalTheory.FullRankCoinv.Y0 k n d * h.val) * (h⁻¹ * u * h).val := by
        have e2 : Z = Z * (h⁻¹).val * h.val := by
          rw [Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
        rw [e2]
        simp only at e
        rw [e]
        simp only [Units.val_mul, Matrix.mul_assoc]
        rw [← Matrix.mul_assoc h.val (h⁻¹).val, ← Units.val_mul h h⁻¹, mul_inv_cancel, Units.val_one, Matrix.one_mul]
      have hu' : h⁻¹ * u * h ∈ U := hu
      have hFZ : GlobalTheory.SplitFlip.smallF (GlobalTheory.SplitFlip.haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν Ψ₁ Z =
          GlobalTheory.SplitFlip.smallF (GlobalTheory.SplitFlip.haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν Ψ₁
            (GlobalTheory.FullRankCoinv.Y0 k n d * h.val) := by
        rw [e', hF _ _ hu']
      rw [hFZ, hZ2]
    · have h0 : Ψ₂ Y = 0 := hΨ₂.2 Y hY
      filter_upwards [h2] with Z hZ
      simp [hZ, h0]
  · exact (hΨ₂.1.2.comp_left (g := starRingEnd ℂ) (map_zero _)).mul_left
  · simp [hΨ₂.2 Y hY]

end GlobalTheory.FullRankCoinv
