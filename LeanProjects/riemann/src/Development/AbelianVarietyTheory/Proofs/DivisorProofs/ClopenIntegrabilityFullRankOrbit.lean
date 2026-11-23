import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LastColsVal

noncomputable section

open MeasureTheory GlobalTheory.SplitFlip ValuativeRel
open scoped Matrix
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

namespace GlobalTheory.FullRankCoinv.Reduce

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem lact_mem {n d : ℕ} (ν : kˣ →* ℂˣ) (g : GL (Fin n) k) {Ψ : Matrix (Fin n) (Fin d) k → ℂ}
    (hΨ : Ψ ∈ fullRk k n d) : lact ν g Ψ ∈ fullRk k n d := by
  have hmem : (fun Y => Ψ ((g.1)ᵀ * Y)) ∈ fullRk k n d := by
    let e : Matrix (Fin n) (Fin d) k ≃ₜ Matrix (Fin n) (Fin d) k :=
      { toFun := fun X => (g.1)ᵀ * X
        invFun := fun X => ((g⁻¹).1)ᵀ * X
        left_inv := fun X => by
          simp only [← Matrix.mul_assoc, ← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one,
            Matrix.one_mul]
        right_inv := fun X => by
          simp only [← Matrix.mul_assoc, ← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one,
            Matrix.one_mul]
        continuous_toFun := by fun_prop
        continuous_invFun := by fun_prop }
    refine ⟨⟨hΨ.1.1.comp_continuous e.continuous, hΨ.1.2.comp_homeomorph e⟩, fun Y hY => hΨ.2 _ ?_⟩
    rwa [Matrix.rank_mul_eq_right_of_isUnit_det _ _
      (by rw [Matrix.det_transpose]; exact Matrix.isUnits_det_units g)]
  exact (fullRk k n d).smul_mem ((ν (gdet g) : ℂ) * apow (gdet g) ((d : ℂ) / 2)) hmem

theorem indicator_mem {n d : ℕ} {T : Set (Matrix (Fin n) (Fin d) k)} (hT : IsClopen T)
    {Ψ : Matrix (Fin n) (Fin d) k → ℂ} (hΨ : Ψ ∈ fullRk k n d) : T.indicator Ψ ∈ fullRk k n d := by
  refine ⟨⟨?_, ?_⟩, fun Y hY => ?_⟩
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    by_cases hx : x ∈ T
    · filter_upwards [hT.isOpen.mem_nhds hx, hΨ.1.1.eventually_eq x] with y hy h
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem hy, h]
    · filter_upwards [hT.compl.isOpen.mem_nhds hx] with y hy
      rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hy]
  · refine HasCompactSupport.mono hΨ.1.2 fun y hy h => hy ?_
    by_cases hy' : y ∈ T
    · rw [Set.indicator_of_mem hy', h]
    · exact Set.indicator_of_notMem hy' _
  · by_cases hy' : Y ∈ T
    · rw [Set.indicator_of_mem hy', hΨ.2 Y hY]
    · exact Set.indicator_of_notMem hy' _

end

theorem reduce_support : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (n d : ℕ) (ν : kˣ →* ℂˣ) (S : Set (Matrix (Fin n) (Fin d) k)), IsClopen S →
    (∀ Φ ∈ GlobalTheory.FullRankCoinv.fullRk k n d, ∀ Y : Matrix (Fin n) (Fin d) k, Integrable (fun g : GL (Fin n) k =>
      Φ (g.val * Y) * (ν (gdet g) : ℂ) * apow (gdet g) ((Fintype.card (Fin d) : ℂ) / 2))
      (haarVol (GlobalTheory.SplitWeil.KO k (Fin n)))) →
    ∀ (s : Finset (GL (Fin n) k)), ∀ Ψ ∈ GlobalTheory.FullRankCoinv.fullRk k n d,
    (∀ Y, Ψ Y ≠ 0 → ∃ E ∈ s, E.val * Y ∈ S) →
    ∃ Φ ∈ GlobalTheory.FullRankCoinv.fullRk k n d, (∀ Y, Y ∉ S → Φ Y = 0) ∧ Ψ - Φ ∈ GlobalTheory.FullRankCoinv.augRk n d ν ∧
      ∀ Y, smallF (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν Φ Y = smallF (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν Ψ Y := by
  intro k _ _ _ _ _ _ n d ν S hS hint s
  classical
  have hadd : ∀ Ψ ∈ fullRk k n d, ∀ Φ ∈ fullRk k n d, ∀ Y,
      smallF (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν (Ψ + Φ) Y =
        smallF (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν Ψ Y + smallF (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν Φ Y := by
    intro Ψ hΨ Φ hΦ Y
    simp only [smallF, Pi.add_apply]
    rw [← integral_add (hint Ψ hΨ Y) (hint Φ hΦ Y)]
    congr 1; funext g; ring
  induction s using Finset.induction_on with
  | empty =>
    intro Ψ hΨ h
    refine ⟨Ψ, hΨ, fun Y _ => ?_, by simp, fun _ => rfl⟩
    by_contra h0
    simpa using h Y h0
  | insert E s _ ih =>
    intro Ψ hΨ h
    set T : Set (Matrix (Fin n) (Fin d) k) := (fun Y => E.val * Y) ⁻¹' S with hTdef
    have hT : IsClopen T := hS.preimage (by fun_prop)
    have h1 := indicator_mem hT hΨ
    have h2 := indicator_mem hT.compl hΨ
    have hsum : T.indicator Ψ + Tᶜ.indicator Ψ = Ψ := Set.indicator_self_add_compl T Ψ
    obtain ⟨Φ₂, hΦ₂, hS₂, ha₂, hF₂⟩ := ih _ h2 fun Y hY => by
      have hYT : Y ∈ Tᶜ := by
        by_contra hc
        exact hY (Set.indicator_of_notMem hc _)
      rw [Set.indicator_of_mem hYT] at hY
      obtain ⟨E', hE', hS'⟩ := h Y hY
      rcases Finset.mem_insert.1 hE' with rfl | hE'
      · exact absurd hS' hYT
      · exact ⟨E', hE', hS'⟩
    have hΦ₁ := lact_mem ν (invT E) h1
    refine ⟨lact ν (invT E) (T.indicator Ψ) + Φ₂, add_mem hΦ₁ hΦ₂, fun Y hY => ?_, ?_, fun Y => ?_⟩
    · have hn : (invT E).1ᵀ * Y ∉ T := by
        intro hc
        apply hY
        have hc' : E.val * ((invT E).1ᵀ * Y) ∈ S := hc
        rwa [invT_val, Matrix.transpose_transpose, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul] at hc'
      simp only [Pi.add_apply, hS₂ Y hY, lact, Set.indicator_of_notMem hn, mul_zero, add_zero]
    · have ha₁ : lact ν (invT E) (T.indicator Ψ) - T.indicator Ψ ∈ augRk n d ν :=
        Submodule.subset_span ⟨_, _, h1, rfl⟩
      have : Ψ - (lact ν (invT E) (T.indicator Ψ) + Φ₂) =
          (Tᶜ.indicator Ψ - Φ₂) - (lact ν (invT E) (T.indicator Ψ) - T.indicator Ψ) := by
        linear_combination -hsum
      rw [this]
      exact sub_mem ha₂ ha₁
    · rw [hadd _ hΦ₁ _ hΦ₂, UnitMinor.smallF_lact, hF₂, ← hadd _ h1 _ h2, hsum]

end GlobalTheory.FullRankCoinv.Reduce
