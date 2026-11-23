import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.KleimanSt
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagDegreeWeightFormula
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Top

namespace LimitVolumeRatio

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ}

theorem linRoot_sub_smul (lam nu : Wt Ψ N) (s : ℝ) :
    linRoot (lam - s • nu) = linRoot lam - C s * linRoot nu := by
  simp only [linRoot, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub, map_mul, sub_mul,
    Finset.sum_sub_distrib, Finset.mul_sum, mul_neg, mul_assoc]
  ring

theorem linA_lamS (T : RootTower Ψ N) (u : Wt Ψ N) (s : ℝ) :
    linA (T.lamS u s) s = toA (linRoot u) + C s * (X none - toA (linRoot T.nu)) := by
  simp only [linA, RootTower.lamS, linRoot_sub_smul, toA, map_sub, map_mul, rename_C]
  ring

theorem cont_pow (Φ : RPA Ψ N →ₗ[ℝ] ℝ) (P0 P1 : RPA Ψ N) (d : ℕ) :
    Continuous fun s : ℝ => Φ ((P0 + C s * P1) ^ d) := by
  have h : ∀ s : ℝ, Φ ((P0 + C s * P1) ^ d) =
      ∑ m ∈ Finset.range (d + 1), s ^ (d - m) * Φ (P0 ^ m * P1 ^ (d - m) * (d.choose m : RPA Ψ N)) := by
    intro s
    rw [add_pow, map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [show s ^ (d - m) * Φ (P0 ^ m * P1 ^ (d - m) * (d.choose m : RPA Ψ N)) =
      Φ (s ^ (d - m) • (P0 ^ m * P1 ^ (d - m) * (d.choose m : RPA Ψ N))) by rw [map_smul, smul_eq_mul]]
    congr 1
    rw [MvPolynomial.smul_eq_C_mul, mul_pow, ← map_pow]
    ring
  rw [show (fun s : ℝ => Φ ((P0 + C s * P1) ^ d)) = fun s : ℝ => ∑ m ∈ Finset.range (d + 1),
      s ^ (d - m) * Φ (P0 ^ m * P1 ^ (d - m) * (d.choose m : RPA Ψ N)) from funext h]
  exact continuous_finset_sum _ fun m _ => (continuous_pow _).mul continuous_const

theorem tendsto_lin (Φ : RPA Ψ N →ₗ[ℝ] ℝ) (T : RootTower Ψ N) (u : Wt Ψ N) (d : ℕ) :
    Tendsto (fun s => Φ (linA (T.lamS u s) s ^ d)) (𝓝[>] 0) (𝓝 (Φ (toA (linRoot u ^ d)))) := by
  have hc := (cont_pow Φ (toA (linRoot u)) (X none - toA (linRoot T.nu)) d).tendsto 0
  simp only [map_zero, zero_mul, add_zero] at hc
  rw [show toA (linRoot u ^ d) = toA (linRoot u) ^ d by simp [toA, map_pow]]
  exact (hc.mono_left nhdsWithin_le_nhds).congr fun s => by rw [linA_lamS]

theorem gap_sub_smul (j : ℕ) (lam nu : Wt Ψ N) (s : ℝ) (τ : Ψ) :
    gap j (lam - s • nu) τ = gap j lam τ - s * gap j nu τ := by
  simp only [gap, ent]
  split_ifs <;> simp <;> ring

end LimitVolumeRatio

end GlobalTheory.CompanionTheory.Ar.Top

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Top

namespace LimitVolumeRatio

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ}

theorem eventually_dominant (T : RootTower Ψ N) (u : Wt Ψ N) (hu : RegDominant u) :
    ∀ᶠ s in 𝓝 (0 : ℝ), Dominant (T.lamS u s) := by
  have key : ∀ τ (a b : Fin N), ∀ᶠ s in 𝓝 (0 : ℝ), a ≤ b → (T.lamS u s) τ b ≤ (T.lamS u s) τ a := by
    intro τ a b
    by_cases hab : a < b
    · have h1 : Tendsto (fun s : ℝ => u τ b - s * T.nu τ b) (𝓝 0) (𝓝 (u τ b - 0 * T.nu τ b)) :=
        (continuous_const.sub (continuous_id.mul continuous_const)).tendsto 0
      have h2 : Tendsto (fun s : ℝ => u τ a - s * T.nu τ a) (𝓝 0) (𝓝 (u τ a - 0 * T.nu τ a)) :=
        (continuous_const.sub (continuous_id.mul continuous_const)).tendsto 0
      filter_upwards [h1.eventually_lt h2 (by simpa using hu τ a b hab)] with s hs _
      simpa [RootTower.lamS] using hs.le
    · exact Eventually.of_forall fun s h => by
        have : a = b := le_antisymm h (not_lt.mp hab)
        subst this
        exact le_rfl
  exact eventually_all.2 fun τ => eventually_all.2 fun a => eventually_all.2 fun b => key τ a b

theorem eventually_threshold [Nonempty Ψ] (T : RootTower Ψ N) (u : Wt Ψ N) (g : ℝ) (hw : WeightHyp T.j u g)
    (B : ℕ) (hB : bigB0 u g < B + 1) :
    ∀ᶠ s in 𝓝 (0 : ℝ), NefThreshold T.j B (T.lamS u s) := by
  have hF : (1 : ℝ) ≤ Fintype.card Ψ := by exact_mod_cast Fintype.card_pos
  have hN : (2 : ℝ) ≤ N := by exact_mod_cast (show 2 ≤ N by have := T.j_pos; have := T.j_lt; omega)
  have hg : 0 < g := hw.1
  have hx : 0 ≤ ‖u‖ := norm_nonneg _
  set F : ℝ := (Fintype.card Ψ : ℝ)
  set x : ℝ := ‖u‖
  have hn2 : (4 : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
  have hB' : 4 * F * (N : ℝ) ^ 2 + 4 * F * (N : ℝ) ^ 2 * (x / g) - 3 < (B : ℝ) - 2 := by
    simp only [bigB0] at hB
    nlinarith
  have hxg : x / g * g = x := div_mul_cancel₀ x hg.ne'
  have hFN : (4 : ℝ) ≤ F * (N : ℝ) ^ 2 := by
    have := mul_le_mul hF hn2 (by norm_num) (by linarith)
    linarith
  have hpos : 0 < 4 * F * (N : ℝ) ^ 2 + 4 * F * (N : ℝ) ^ 2 * (x / g) - 3 := by
    have : 0 ≤ x / g := div_nonneg hx hg.le
    have h' : 0 ≤ 4 * F * (N : ℝ) ^ 2 * (x / g) := mul_nonneg (by positivity) this
    linarith
  have hB2 : 0 ≤ (B : ℝ) - 2 := by linarith
  have at0 : ∀ τ, 4 * F * x < ((B : ℝ) - 2) * gap T.j u τ := by
    intro τ
    have h1 : ((B : ℝ) - 2) * g ≤ ((B : ℝ) - 2) * gap T.j u τ :=
      mul_le_mul_of_nonneg_left (hw.2.2.1 τ) hB2
    have h2 := mul_lt_mul_of_pos_right hB' hg
    have h3 : (4 * F * (N : ℝ) ^ 2 + 4 * F * (N : ℝ) ^ 2 * (x / g) - 3) * g =
        4 * F * (N : ℝ) ^ 2 * g + 4 * F * (N : ℝ) ^ 2 * x - 3 * g := by
      rw [sub_mul, add_mul, mul_assoc (4 * F * (N : ℝ) ^ 2), hxg]
    have h4 : 4 * F * x ≤ 4 * F * (N : ℝ) ^ 2 * x := by
      have e : 4 * F * (N : ℝ) ^ 2 * x - 4 * F * x = (4 * F * x) * ((N : ℝ) ^ 2 - 1) := by ring
      have := mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ 4 * F) hx) (by linarith : (0 : ℝ) ≤ (N : ℝ) ^ 2 - 1)
      linarith
    have h5 : 0 < 4 * F * (N : ℝ) ^ 2 * g - 3 * g := by
      have e : 4 * F * (N : ℝ) ^ 2 * g - 3 * g = g * (4 * (F * (N : ℝ) ^ 2) - 3) := by ring
      rw [e]
      exact mul_pos hg (by linarith)
    linarith
  have key : ∀ τ, ∀ᶠ s in 𝓝 (0 : ℝ), 4 * F * ‖T.lamS u s‖ ≤ ((B : ℝ) - 2) * gap T.j (T.lamS u s) τ := by
    intro τ
    have h1 : Tendsto (fun s : ℝ => 4 * F * ‖T.lamS u s‖) (𝓝 0) (𝓝 (4 * F * ‖T.lamS u 0‖)) :=
      ((continuous_const.mul (continuous_const.sub (continuous_id.smul continuous_const)).norm)).tendsto 0
    have h2 : Tendsto (fun s : ℝ => ((B : ℝ) - 2) * (gap T.j u τ - s * gap T.j T.nu τ)) (𝓝 0)
        (𝓝 (((B : ℝ) - 2) * (gap T.j u τ - 0 * gap T.j T.nu τ))) :=
      (continuous_const.mul (continuous_const.sub (continuous_id.mul continuous_const))).tendsto 0
    have h0 : 4 * F * ‖T.lamS u 0‖ < ((B : ℝ) - 2) * (gap T.j u τ - 0 * gap T.j T.nu τ) := by
      simpa [RootTower.lamS] using at0 τ
    filter_upwards [h1.eventually_lt h2 h0] with s hs
    rw [RootTower.lamS, gap_sub_smul]
    exact hs.le
  exact eventually_all.2 key

theorem tower_T1_limit_of_inputs : ∀ II : IntersectionSystem, ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) [Nonempty Ψ]
    (T : RootTower Ψ N), T.Proportional → T.I2 II → T.I3 → T.T1 II := by
  intro II Ψ _ _ N _ T hProp hI2 hI3 u g hw B hB c
  have hF : (1 : ℝ) ≤ Fintype.card Ψ := by exact_mod_cast Fintype.card_pos
  have hN : (2 : ℝ) ≤ N := by exact_mod_cast (show 2 ≤ N by have := T.j_pos; have := T.j_lt; omega)
  have hB2 : 2 ≤ B := by
    have hq : 0 ≤ ‖u‖ / g := div_nonneg (norm_nonneg _) hw.1.le
    have : (16 : ℝ) ≤ bigB0 u g := by
      simp only [bigB0]
      have hn2 : (4 : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
      have hFN : (4 : ℝ) ≤ (Fintype.card Ψ : ℝ) * (N : ℝ) ^ 2 := by nlinarith
      have h1q : (1 : ℝ) ≤ 1 + ‖u‖ / g := by linarith
      have := mul_le_mul hFN h1q zero_le_one (by positivity)
      nlinarith
    have : (15 : ℝ) < B := by linarith
    exact_mod_cast (show (2 : ℝ) ≤ B by linarith)
  have hdom := eventually_dominant T u hw.2.1
  have hthr := eventually_threshold T u g hw B hB
  have hpos : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < s := eventually_mem_nhdsWithin

  obtain ⟨s₁, hs₁, C₂, hag⟩ := hI2 (l1 u)
  have hdiff : Tendsto (fun s => T.mbarTop II B c u s - T.PBs II B c (T.lamS u s) s) (𝓝[>] 0) (𝓝 0) := by
    have hlin : Tendsto (fun s : ℝ => C₂ * s) (𝓝[>] 0) (𝓝 0) :=
      ((continuous_const.mul continuous_id).tendsto' 0 0 (by simp)).mono_left nhdsWithin_le_nhds
    refine squeeze_zero_norm' ?_ hlin
    filter_upwards [hpos, (eventually_le_nhds hs₁).filter_mono nhdsWithin_le_nhds,
      hdom.filter_mono nhdsWithin_le_nhds] with s h0 h1 h2
    exact hag B hB2 c u s le_rfl h0 h1 h2
  have hPB : Tendsto (fun s => T.PBs II B c (T.lamS u s) s) (𝓝[>] 0)
      (𝓝 (T.PPc II B c (linRoot u ^ (dimFl Ψ N + 1)))) :=
    LimitVolumeRatio.tendsto_lin ((T.M B c).PP II) T u (dimFl Ψ N + 1)
  have hbar : Tendsto (fun s => T.mbarTop II B c u s) (𝓝[>] 0)
      (𝓝 (T.PPc II B c (linRoot u ^ (dimFl Ψ N + 1)))) := by
    have h := hPB.add hdiff
    rw [add_zero] at h
    exact h.congr fun s => by ring
  have hdeg : Tendsto (fun s => T.mDeg B c u s) (𝓝[>] 0) (𝓝 (T.vol c * flagDeg u)) := by
    have h := LimitVolumeRatio.tendsto_lin (T.M B c).geoFun T u (dimFl Ψ N)
    rwa [hProp.2.1 B c] at h
  have hvpos : 0 < T.vol c * flagDeg u :=
    mul_pos (hProp.1 c) ((flagDeg_eq_weyl Ψ N u).2.1 hw.2.1)
  refine ⟨?_, hbar, hdeg, hvpos, ?_⟩
  · obtain ⟨s₀, hs₀, h3⟩ := hI3 (l1 u)
    filter_upwards [hpos, (eventually_le_nhds hs₀).filter_mono nhdsWithin_le_nhds,
      hdom.filter_mono nhdsWithin_le_nhds, hthr.filter_mono nhdsWithin_le_nhds] with s h0 h1 h2 h4
    exact h3 B hB2 c u s le_rfl h0 h1 h2 h4
  · have hne : ((dimFl Ψ N : ℝ) + 1) * (T.vol c * flagDeg u) ≠ 0 :=
      (mul_pos (by positivity) hvpos).ne'
    exact hbar.div (hdeg.const_mul _) hne

end LimitVolumeRatio

end GlobalTheory.CompanionTheory.Ar.Top
