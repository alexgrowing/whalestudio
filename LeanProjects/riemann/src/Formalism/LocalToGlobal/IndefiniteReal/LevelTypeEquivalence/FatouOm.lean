import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.ShiftedBound

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField Filter Topology
open scoped TensorProduct ContDiff ENNReal

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {S T : HSp D} {k : ℕ}

theorem fatou_om {ψ : AddChar (AF D.host.F) ℂ} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hω : IsWeilDatumO ψ S T χS χT om)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) {L : (Fin k → ℝ) →+ WO S T} {P : WO S T →+ (Fin k → ℝ)}
    (hL : IsRealFrame L) (hPc : Continuous P) (hLP : ∀ w, L (P w) = eInf D • w) (g : GA D S) (h : GA D T)
    {μ : Measure (WO S T)} {𝓕 : Set (WO S T)} (hμ : μ.IsAddHaarMeasure)
    (h𝓕 : IsAddFundamentalDomain (ratL T S) 𝓕 μ) {n : ℕ} (l : Fin n → Fin k) :
    ∫⁻ x in 𝓕, ‖dH ψ L l (om (g, h) f) x‖ₑ ^ 2 ∂μ ≤
      ∫⁻ x in 𝓕, ‖dH ψ ((actOAdd g⁻¹ h⁻¹).comp L) l f x‖ₑ ^ 2 ∂μ := by
  have hψ := hω.std
  obtain ⟨Λ, hΛ, hψΛ⟩ := psi_real ψ hψ
  obtain ⟨hM, hPMc, hMP⟩ := transported_frame hL hPc hLP g h
  set M := (actOAdd g⁻¹ h⁻¹).comp L
  set v : Fin n → (Fin k → ℝ) := fun i => ev (l i)
  set hj : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1)
  have hjpos : ∀ j, 0 < hj j := fun j => by positivity
  have hjle : ∀ j, hj j ≤ 1 := fun j => by
    simp only [hj]; rw [div_le_one (by positivity)]; linarith [(j.cast_nonneg : (0 : ℝ) ≤ j)]
  set Tf : ℕ → WO S T → ℂ := fun j y => md (Gf ψ M f y) n v (hj j) 0
  have hT : ∀ j, IsThetaFunO ψ S T (Tf j) := fun j => md_theta hψ hf hM n v (hj j) 0
  have hom : ∀ j, om (g, h) (Tf j) = fun x => md (Gf ψ L (om (g, h) f) x) n v (hj j) 0 := fun j =>
    om_md hω hf L hL g h n v (hj j) 0
  have hf' : IsThetaFunO ψ S T (om (g, h) f) := hω.om_pres (g, h) f hf
  have hlimL : ∀ x, Tendsto (fun j => om (g, h) (Tf j) x) atTop (𝓝 (dH ψ L l (om (g, h) f) x)) := by
    intro x
    have e : (fun j => om (g, h) (Tf j) x) = fun j => md (Gf ψ L (om (g, h) f) x) n v (hj j) 0 :=
      funext fun j => congrFun (hom j) x
    rw [e]
    exact md_tendsto_seq (Gf_smooth hΛ hψΛ hL hf' x) v
  have hlimM : ∀ y, Tendsto (fun j => Tf j y) atTop (𝓝 (dH ψ M l f y)) := fun y =>
    md_tendsto_seq (Gf_smooth hΛ hψΛ hM hf y) v
  obtain ⟨B, hB⟩ := shifted_bound hψ hf hM hPMc hMP n (n : ℝ) (Nat.cast_nonneg n)
  have hTb : ∀ j y, ‖Tf j y‖ ≤ B := by
    intro j y
    have := md_bound n (Gf ψ M f y) (Gf_smooth hΛ hψΛ hM hf y) v (hj j) (hjpos j) 0 B (fun t ht => hB y t (by
      have hsum : ∑ i, ‖v i‖ = n := by simp [v, norm_ev]
      rw [sub_zero, hsum] at ht
      calc ‖t‖ ≤ hj j * n := ht
        _ ≤ 1 * n := mul_le_mul_of_nonneg_right (hjle j) (Nat.cast_nonneg n)
        _ = n := one_mul _))
    simpa [v, norm_ev] using this

  have hF : ∀ x, Tendsto (fun j => ‖om (g, h) (Tf j) x‖ₑ ^ 2) atTop (𝓝 (‖dH ψ L l (om (g, h) f) x‖ₑ ^ 2)) :=
    fun x => ((ENNReal.continuous_pow 2).comp continuous_enorm).continuousAt.tendsto.comp (hlimL x)
  have hmeas : ∀ j, Measurable fun x => ‖om (g, h) (Tf j) x‖ₑ ^ 2 := fun j =>
    (hω.om_pres (g, h) _ (hT j)).cont.enorm.measurable.pow_const 2
  have step1 : ∫⁻ x in 𝓕, ‖dH ψ L l (om (g, h) f) x‖ₑ ^ 2 ∂μ ≤
      liminf (fun j => ∫⁻ x in 𝓕, ‖om (g, h) (Tf j) x‖ₑ ^ 2 ∂μ) atTop := by
    calc ∫⁻ x in 𝓕, ‖dH ψ L l (om (g, h) f) x‖ₑ ^ 2 ∂μ
        = ∫⁻ x in 𝓕, liminf (fun j => ‖om (g, h) (Tf j) x‖ₑ ^ 2) atTop ∂μ :=
          lintegral_congr fun x => ((hF x).liminf_eq).symm
      _ ≤ _ := lintegral_liminf_le (u := atTop) (f := fun j x => ‖om (g, h) (Tf j) x‖ₑ ^ 2) hmeas
  have step2 : ∀ j, ∫⁻ x in 𝓕, ‖om (g, h) (Tf j) x‖ₑ ^ 2 ∂μ = ∫⁻ x in 𝓕, ‖Tf j x‖ₑ ^ 2 ∂μ := fun j =>
    hω.om_unit μ 𝓕 hμ h𝓕 (g, h) (Tf j) (hT j)
  have hfin : μ 𝓕 < ⊤ := (PHeisFC.finCovol T S).2 μ 𝓕 hμ h𝓕
  have step3 : Tendsto (fun j => ∫⁻ x in 𝓕, ‖Tf j x‖ₑ ^ 2 ∂μ) atTop (𝓝 (∫⁻ x in 𝓕, ‖dH ψ M l f x‖ₑ ^ 2 ∂μ)) := by
    refine tendsto_lintegral_of_dominated_convergence (fun _ => ‖(B : ℂ)‖ₑ ^ 2)
      (fun j => (hT j).cont.enorm.measurable.pow_const 2) (fun j => Eventually.of_forall fun y => ?_) ?_
      (Eventually.of_forall fun y => ((ENNReal.continuous_pow 2).comp continuous_enorm).continuousAt.tendsto.comp
        (hlimM y))
    · show ‖Tf j y‖ₑ ^ 2 ≤ ‖(B : ℂ)‖ₑ ^ 2
      gcongr
      rw [← ofReal_norm, ← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal ((hTb j y).trans (by rw [Complex.norm_real]; exact le_abs_self B))
    · rw [setLIntegral_const]
      exact ENNReal.mul_ne_top (ENNReal.pow_ne_top enorm_ne_top) hfin.ne
  calc ∫⁻ x in 𝓕, ‖dH ψ L l (om (g, h) f) x‖ₑ ^ 2 ∂μ
      ≤ liminf (fun j => ∫⁻ x in 𝓕, ‖om (g, h) (Tf j) x‖ₑ ^ 2 ∂μ) atTop := step1
    _ = liminf (fun j => ∫⁻ x in 𝓕, ‖Tf j x‖ₑ ^ 2 ∂μ) atTop := by simp_rw [step2]
    _ = _ := step3.liminf_eq

end Formalism.IndefR.Eqv

end
