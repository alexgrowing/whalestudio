import Mathlib
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.UniformCoefficientBounds.CoefCC

open Matrix MeasureTheory Set
open scoped ContDiff InnerProductSpace ENNReal

noncomputable section

namespace CompanionTheory.D.Upq.Coef

open CompanionTheory.D.Upq.Sm Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Formalism.FourierDecayAlt.P.CutBP.Jmu

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem inCC_cf_of_dec (hK : PI.KFinSmooth) {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool}
    {lam : Fin (2 * r + k + 1) → ℝ} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {σ : Mx k r → (H →L[ℂ] H)}
    (hlam : Formalism.QuantumDeterminants.IsHCParam lam) (hσ : PI.UpqRep.IsDSHpk k r ε lam σ)
    {w : H}
    (hw : PI.UpqRep.IsKFinHpk (k := k) (r := r) σ w) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (x₀ : E) {A : ℝ}
    (hdec : ∀ a ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ,
      ∀ b ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ,
      ∃ C : ℝ, ∀ g ∈ B.GV k r, B.gN g ^ A * ‖⟪a, σ g b⟫_ℂ‖ ≤ C) (m : ℕ) :
    B.InCC A m (cf σ x₀ w w) := by
  obtain ⟨P, ⟨⟨hP, hPJ⟩, -⟩, -, -, ⟨⟨h1, hm⟩, hiso, -⟩, -⟩ := id hσ
  obtain ⟨hc1, -⟩ := conj_facts hP hPJ
  have hG : PI.IsMatGroup (B.GV k r) := PI.QuotSetU.UnitaryGroupMassFormula.unitary_hermitian_group k r
  have hrep : RepOn (B.GV k r) σ := repOn_of_conj hP hPJ h1 hm
  have hiso' : ∀ g ∈ B.GV k r, ∀ v, ‖σ g v‖ = ‖v‖ := fun g hg v => by
    obtain ⟨b, hb, rfl⟩ := hc1 g hg
    exact hiso b hb v
  obtain ⟨S, hS, hwS, hSK⟩ := hw
  have hT : GoodSub (B.GV k r) (B.GV k r ∩ (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ : Set _))
      σ S := ⟨hS, fun v hv => hK k r ε lam H σ hlam hσ v ⟨S, hS, hv, hSK⟩, hSK⟩
  have hws := hT.sm w hwS
  obtain ⟨T, C, hT', hC, hW⟩ := hT.words hG hrep inter_subset_left hwS m
  haveI := hT'.fin
  obtain ⟨C', hC', hb⟩ := coef_bound_uniform (G := B.GV k r) (σ := σ) (T := T)
    (ρ := fun g => B.gN g ^ (-A)) (fun g _ => Real.rpow_nonneg (Real.sqrt_nonneg _) _)
    (fun a ha b hb => by
      obtain ⟨C, hd⟩ := hdec a (hT'.sm a ha) b (hT'.sm b hb)
      refine ⟨C, fun g hg => ?_⟩
      have hg0 : 0 < B.gN g := lt_of_lt_of_le one_pos (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one hg)
      rw [Real.rpow_neg hg0.le, ← div_eq_mul_inv, le_div_iff₀ (Real.rpow_pos_of_pos hg0 _), mul_comm]
      exact hd g hg)
  refine ⟨C' * C * C * ‖x₀‖, fun g₀ hg₀ => ?_, fun u v hu hv huv g hg => ?_⟩
  · obtain ⟨U, F, hU, hgU, hF, hfF⟩ :=
      SmOn.clm hws (((innerSL ℂ w).smulRight x₀).restrictScalars ℝ) g₀ hg₀
    exact ⟨U, F, hU, hgU, hF.of_le (by exact_mod_cast le_top), hfF⟩
  · have hlie : ∀ W : List (B.Mat k r), (∀ X ∈ W, B.unitLie k r X) →
        LieW (B.GV k r) W ∧ ∀ X ∈ W, ‖X‖ ≤ 1 := fun W hW =>
      ⟨fun X hX t => ex_mem_of_lie (hW X hX).1 t,
        fun X hX => (Matrix.norm_le_iff zero_le_one).2 (hW X hX).2⟩
    obtain ⟨hu1, hu2⟩ := hW u (hlie u hu).1 (hlie u hu).2 (by omega)
    obtain ⟨hv1, hv2⟩ := hW v (hlie v hv).1 (hlie v hv).2 (by omega)
    rw [dLR_cf hrep hiso' x₀ hws hws (hlie u hu).1 (hlie v hv).1 hg, cf, norm_smul]
    have hg1 : 1 ≤ B.gN g := Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one hg
    have h2 := hb _ hu1 _ hv1 g hg
    have h3 : B.gN g ^ A * B.gN g ^ (-A) ≤ 1 := by
      rw [← Real.rpow_add (by linarith)]
      simp
    have h4 : 0 ≤ B.gN g ^ A := Real.rpow_nonneg (by linarith) _
    have h5 : 0 ≤ B.gN g ^ (-A) := Real.rpow_nonneg (by linarith) _
    calc _ ≤ B.gN g ^ A * (C' * C * C * B.gN g ^ (-A) * ‖x₀‖) := by
          gcongr
          exact h2.trans (by gcongr)
      _ = (B.gN g ^ A * B.gN g ^ (-A)) * (C' * C * C * ‖x₀‖) := by ring
      _ ≤ _ := mul_le_of_le_one_left (by positivity) h3

theorem coef_eq_cf {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (μG : Measure (Formalism.QuantumDeterminants.Mt k r))
    (A : JDat k r Wp Wq) : A.coef μG = cf A.σ (((A.scal μG : ℝ) : ℂ) •
      (innerSL ℂ (A.l' A.w0)).smulRight (A.l A.w0)) A.w0 A.w0 := by
  ext g x
  simp only [JDat.coef, cf, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply,
    smul_smul]
  congr 1
  ring

end CompanionTheory.D.Upq.Coef

end
