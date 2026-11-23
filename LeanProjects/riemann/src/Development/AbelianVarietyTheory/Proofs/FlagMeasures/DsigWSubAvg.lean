import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsCompactKH
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsHaarProbabilityMaxCompactHermitianStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryRealTraceBumpPowFiniteTranslationStablePoStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralTranslateFamilyIsKFiniteHermitianStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HasDerivAtDerivedActionMaxCompactAverageStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryRealTraceBumpPeakPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TendstoIntegralNormalisedPowPeakStatement

open MeasureTheory Matrix Filter Topology

noncomputable section

namespace GlobalTheory.KFinAvg

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)}

theorem dsigW_sub_avg {μ : Measure (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)}
    {φ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → ℂ} {v : H}
    (hU : Formalism.MainNotions.S.IsURepOn (Formalism.QuantumDeterminants.UH (PI.UpqRep.Hpk k r)) σ) (hv : Formalism.MainNotions.S.IsSmoothVec (k := k) (r := r) σ v)
    (hD' : ∀ (D : List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ))
      (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ),
      (∀ Y ∈ D, Formalism.MainNotions.S.InLieHpk k r Y) → Formalism.MainNotions.S.InLieHpk k r X →
      HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) (∫ g, φ g • Formalism.MainNotions.S.dsigW (k := k) (r := r) σ D (σ g v) ∂μ))
        (∫ g, φ g • Formalism.MainNotions.S.dsigW (k := k) (r := r) σ (X :: D) (σ g v) ∂μ) 0) :
    ∀ D : List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ), (∀ Y ∈ D, Formalism.MainNotions.S.InLieHpk k r Y) →
      Formalism.MainNotions.S.dsigW (k := k) (r := r) σ D (v - ∫ g, φ g • σ g v ∂μ) =
        Formalism.MainNotions.S.dsigW (k := k) (r := r) σ D v - ∫ g, φ g • Formalism.MainNotions.S.dsigW (k := k) (r := r) σ D (σ g v) ∂μ := by
  intro D
  induction D with
  | nil => intro _; rfl
  | cons X D ih =>
    intro hD
    have hX : Formalism.MainNotions.S.InLieHpk k r X := hD X List.mem_cons_self
    have hD1 : ∀ Y ∈ D, Formalism.MainNotions.S.InLieHpk k r Y := fun Y hY => hD Y (List.mem_cons_of_mem _ hY)
    show deriv (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) (Formalism.MainNotions.S.dsigW (k := k) (r := r) σ D _)) 0 = _
    rw [ih hD1]
    simp only [map_sub]
    exact ((Formalism.MainNotions.LowestKTypeMultiplicity.dsigW_hasDeriv hU hv D hD1 hX).sub (hD' D X hD1 hX)).deriv

theorem kDense : Formalism.MainNotions.S.Pv.AmpDD.KDense := by
  intro k r ε lam H _ _ _ σ _ hDS v hv Ws hWs e he
  obtain ⟨-, hU, -⟩ := GlobalTheory.BesselMapOne.rep_of_isDSHpk hDS
  obtain ⟨μ, hμ⟩ := GlobalTheory.T.exists_isHaarProbabilityMaxCompactHermitian k r
  have hv' : Formalism.MainNotions.S.IsSmoothVec (k := k) (r := r) σ v := hv
  obtain ⟨hpc, hp1, hp01, hpδ⟩ := GlobalTheory.T.unitaryRealTraceBump_peak_properties (2 * r + k + 1) (Nat.succ_pos _)
  have hKc : IsCompact (GlobalTheory.ThA.KH k r) := isCompact_KH k r
  have hK1 : (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) ∈ GlobalTheory.ThA.KH k r :=
    ⟨by show (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)ᴴ * _ * 1 = _; simp,
      one_mem _⟩
  have hpK : ∀ x ∈ GlobalTheory.ThA.KH k r, 0 ≤ peak (2 * r + k + 1) x ∧ peak (2 * r + k + 1) x ≤ 1 :=
    fun x hx => hp01 x hx.2
  have hpU : ∀ U ∈ 𝓝 (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ), ∃ δ < 1,
      ∀ x ∈ GlobalTheory.ThA.KH k r, x ∉ U → peak (2 * r + k + 1) x ≤ δ := fun U hU' => by
    obtain ⟨δ, hδ, h⟩ := hpδ U hU'
    exact ⟨δ, hδ, fun x hx hxU => h x hx.2 hxU⟩
  have hσ1 : σ 1 = 1 := hU.1.1
  have hconv : ∀ w ∈ Ws, Tendsto (fun m : ℕ => ∫ g, peakN μ m g • Formalism.MainNotions.S.dsigW (k := k) (r := r) σ w (σ g v) ∂μ)
      atTop (𝓝 (Formalism.MainNotions.S.dsigW (k := k) (r := r) σ w v)) := by
    intro w hw
    have hc := (Formalism.MainNotions.LowestKTypeMultiplicity.orbit_cont hU hv' w (hWs w hw)).mono
      (Set.inter_subset_left : GlobalTheory.ThA.KH k r ⊆ _)
    have := GlobalTheory.T.tendsto_integral_normalised_pow_smul_of_unique_peak _ μ hμ.1 _ 1 _ hKc hμ.2.1 hK1 hμ.2.2.2 hpc hp1 hpK hpU H _ hc
    rw [hσ1, ContinuousLinearMap.one_apply] at this
    exact this
  set L := Ws.length
  have hε : 0 < e / (L + 1) := by positivity
  have hev : ∀ᶠ m : ℕ in atTop, ∀ w ∈ {w | w ∈ Ws},
      dist (∫ g, peakN μ m g • Formalism.MainNotions.S.dsigW (k := k) (r := r) σ w (σ g v) ∂μ)
        (Formalism.MainNotions.S.dsigW (k := k) (r := r) σ w v) < e / (L + 1) :=
    (Filter.eventually_all_finite Ws.finite_toSet).2 fun w hw => Metric.tendsto_nhds.1 (hconv w hw) _ hε
  obtain ⟨m, hm⟩ := hev.exists
  obtain ⟨N, b, c, hbc, hpoly, htr⟩ := GlobalTheory.T.unitaryRealTraceBump_pow_finite_translation_stable_polys (2 * r + k + 1) m
  set Z : ℝ := ∫ h, peak (2 * r + k + 1) h ^ m ∂μ
  have e1 : ∀ g, peakN μ m g = ∑ j, (c j / (Z : ℂ)) * b j g := fun g => by
    show ((peak (2 * r + k + 1) g ^ m / Z : ℝ) : ℂ) = _
    rw [Complex.ofReal_div, hpoly g, Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  refine ⟨∫ g, peakN μ m g • σ g v ∂μ, ?_, ?_⟩
  · have := GlobalTheory.T.integral_translate_family_isKFinite_hermitian k r H σ μ hU hμ N b hbc htr (fun j => c j / (Z : ℂ)) v
    simpa only [← e1] using this
  · have hD' := fun D X hD hX => GlobalTheory.T.hasDerivAt_derived_action_max_compact_average k r H σ μ (peakN μ m) v D X hU hμ
      (by rw [show peakN μ m = fun g => ∑ j, (c j / (Z : ℂ)) * b j g from funext e1]
          exact continuous_finset_sum _ fun j _ => continuous_const.mul (hbc j)) hv' hD hX
    have hterm : ∀ w ∈ Ws, ‖PI.UpqRep.dsigW (k := k) (r := r) σ w (v - ∫ g, peakN μ m g • σ g v ∂μ)‖ ≤ e / (L + 1) := by
      intro w hw
      rw [Formalism.MainNotions.BridgeCS3d.dsigW_eq, dsigW_sub_avg hU hv' hD' w (hWs w hw), norm_sub_rev, ← dist_eq_norm]
      exact (hm w hw).le
    calc (Ws.map fun w => ‖PI.UpqRep.dsigW (k := k) (r := r) σ w (v - ∫ g, peakN μ m g • σ g v ∂μ)‖).sum
        ≤ (Ws.map fun _ => e / (L + 1)).sum := List.sum_le_sum (fun w hw => hterm w hw)
      _ = L * (e / (L + 1)) := by simp [L, List.map_const', List.sum_replicate, nsmul_eq_mul]
      _ < e := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith

end GlobalTheory.KFinAvg
