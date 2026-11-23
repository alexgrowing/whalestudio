import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.KleimanSt

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace RootFieldNumerics

theorem dominant_of_gaps {Ψ : Type} {N : ℕ} (mu : Wt Ψ N)
    (h : ∀ τ (i : ℕ), i + 1 < N → 0 ≤ ent mu τ i - ent mu τ (i + 1)) : Dominant mu := by
  intro τ a b hab
  have hab' : (a : ℕ) ≤ b := hab
  have key : ∀ k : ℕ, (a : ℕ) + k < N → ent mu τ ((a : ℕ) + k) ≤ ent mu τ a := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have h1 := h τ ((a : ℕ) + k) (by omega)
      have h2 := ih (by omega)
      show ent mu τ ((a : ℕ) + k + 1) ≤ ent mu τ a
      linarith
  have h3 := key ((b : ℕ) - a) (by omega)
  rw [Nat.add_sub_cancel' hab'] at h3
  simpa [ent, a.isLt, b.isLt] using h3

theorem abs_ent_le {Ψ : Type} [Fintype Ψ] {N : ℕ} (mu : Wt Ψ N) (τ : Ψ) (i : ℕ) : |ent mu τ i| ≤ ‖mu‖ := by
  unfold ent
  split_ifs with h
  · exact (norm_le_pi_norm (mu τ) _).trans (norm_le_pi_norm mu τ)
  · simp

theorem perturbed_weight_wall_bounds : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) (c₀ θ₀ : ℝ), 0 < c₀ → 0 < θ₀ → ∃ B₁ : ℕ, ∀ B : ℕ, B₁ ≤ B → ∀ (τ₀ : Ψ) (lam₀ : Wt Ψ N), InWall T.j τ₀ c₀ lam₀ → let θ : ℝ := 5 * Fintype.card Ψ / B; let lam : Wt Ψ N := fun τ i => lam₀ τ i + (if τ = τ₀ ∧ (i : ℕ) < T.j then 2 * θ else 0); 3 ≤ B ∧ 0 < θ ∧ θ ≤ θ₀ ∧ θ ≤ 1 ∧ ‖lam‖ ≤ 1 ∧ ‖T.lamS lam (θ ^ 2)‖ ≤ 1 ∧ (∀ τ, θ ≤ gap T.j lam τ) ∧ gap T.j lam τ₀ = 2 * θ ∧ CompactGapsGE T.j c₀ lam ∧ Dominant lam ∧ Dominant (T.lamS lam (θ ^ 2)) ∧ NefThreshold T.j B (T.lamS lam (θ ^ 2)) ∧ ‖T.lamS lam (θ ^ 2) - lam₀‖ ≤ 2 * θ + ‖T.nu‖ * θ ^ 2 := by
  intro Ψ _ _ N T c₀ θ₀ hc₀ hθ₀
  set R := ‖T.nu‖ with hR
  have hR0 : 0 ≤ R := norm_nonneg _
  set δ : ℝ := min (min θ₀ (1 / 8)) (min (c₀ / 2) (1 / (4 * (R + 1)))) with hδ
  have hδpos : 0 < δ :=
    lt_min (lt_min hθ₀ (by norm_num)) (lt_min (by linarith) (by positivity))
  refine ⟨max 10 ⌈5 * (Fintype.card Ψ : ℝ) / δ⌉₊, ?_⟩
  intro B hB τ₀ lam₀ hW
  intro θ lam
  obtain ⟨hn0, hg0, hgo, hcg⟩ := hW
  have hcard : (1 : ℝ) ≤ Fintype.card Ψ := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨τ₀⟩
  have hB10 : (10 : ℝ) ≤ B := by exact_mod_cast (le_max_left _ _).trans hB
  have hBpos : (0 : ℝ) < B := by linarith
  have hBc : 5 * (Fintype.card Ψ : ℝ) / δ ≤ B :=
    (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right _ _).trans hB)
  have hθdef : θ = 5 * (Fintype.card Ψ : ℝ) / B := rfl
  have hθpos : 0 < θ := by rw [hθdef]; exact div_pos (by linarith) hBpos
  have hθδ : θ ≤ δ := by
    rw [hθdef, div_le_iff₀ hBpos]
    have := (div_le_iff₀ hδpos).mp hBc
    linarith [mul_comm (B : ℝ) δ]
  have hθθ₀ : θ ≤ θ₀ := hθδ.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hθ8 : θ ≤ 1 / 8 := hθδ.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hθc : θ ≤ c₀ / 2 := hθδ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hθR' : θ ≤ 1 / (4 * (R + 1)) := hθδ.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hθR : θ * R ≤ 1 / 4 := by
    rw [le_div_iff₀ (by positivity)] at hθR'
    nlinarith
  have hθB : θ * B = 5 * (Fintype.card Ψ : ℝ) := by
    rw [hθdef]; field_simp
  let D : Wt Ψ N := fun τ i => if τ = τ₀ ∧ (i : ℕ) < T.j then 2 * θ else 0
  have hD : ‖D‖ ≤ 2 * θ := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr (fun τ => ?_)
    refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr (fun i => ?_)
    simp only [D]
    split_ifs
    · rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
    · simp; positivity
  have hlamD : lam = lam₀ + D := by funext τ i; rfl
  have hnlam : ‖lam‖ ≤ 1 / 2 + 2 * θ := by
    rw [hlamD]; exact (norm_add_le _ _).trans (by linarith)
  have hnmu : ‖T.lamS lam (θ ^ 2)‖ ≤ 1 / 2 + 2 * θ + θ ^ 2 * R := by
    show ‖lam - θ ^ 2 • T.nu‖ ≤ _
    refine (norm_sub_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    linarith
  have hθ2R : θ ^ 2 * R ≤ θ / 4 := by
    have : θ ^ 2 * R = θ * (θ * R) := by ring
    rw [this]
    have := mul_le_mul_of_nonneg_left hθR hθpos.le
    linarith
  have hnmu1 : ‖T.lamS lam (θ ^ 2)‖ ≤ 1 := by linarith
  have hent : ∀ τ i, ent lam τ i = ent lam₀ τ i + (if τ = τ₀ ∧ i < T.j then 2 * θ else 0) := by
    intro τ i
    by_cases hi : i < N
    · simp [ent, hi, lam]
    · have : ¬ (i < T.j) := by have := T.j_lt; omega
      simp [ent, hi, this]
  have hentS : ∀ (mu : Wt Ψ N) (s : ℝ) τ i,
      ent (T.lamS mu s) τ i = ent mu τ i - s * ent T.nu τ i := by
    intro mu s τ i
    by_cases hi : i < N <;> simp [ent, hi, RootTower.lamS]
  have hnuD : ∀ τ i, ent T.nu τ i - ent T.nu τ (i + 1) ≤ 2 * R := by
    intro τ i
    have h1 := abs_ent_le T.nu τ i
    have h2 := abs_ent_le T.nu τ (i + 1)
    have h3 := le_abs_self (ent T.nu τ i)
    have h4 := neg_abs_le (ent T.nu τ (i + 1))
    linarith
  have hgapLam : ∀ τ i, i + 1 < N → 2 * θ ≤ ent lam τ i - ent lam τ (i + 1) := by
    intro τ i hi
    rw [hent, hent]
    rcases lt_trichotomy (i + 1) T.j with hlt | heq | hgt
    · have hc := hcg τ i hi hlt.ne
      have h1 : i < T.j := by omega
      by_cases hτ : τ = τ₀
      · subst hτ
        simp [h1, hlt]
        linarith
      · simp [hτ]
        linarith
    · have h1 : i < T.j := by omega
      have h2 : ¬ i + 1 < T.j := by omega
      have hg : gap T.j lam₀ τ = ent lam₀ τ i - ent lam₀ τ (i + 1) := by
        simp only [gap]; rw [← heq]; simp
      by_cases hτ : τ = τ₀
      · subst hτ
        simp [h1, h2]
        linarith [hg0, hg]
      · have := hgo τ hτ
        simp [hτ]
        linarith
    · have hc := hcg τ i hi hgt.ne'
      have h1 : ¬ i < T.j := by omega
      have h2 : ¬ i + 1 < T.j := by omega
      simp [h1, h2]
      linarith
  have hj1 : T.j - 1 + 1 = T.j := by have := T.j_pos; omega
  have hj2 : T.j - 1 + 1 < N := by have := T.j_pos; have := T.j_lt; omega
  have hgapj : ∀ τ, 2 * θ ≤ gap T.j lam τ := by
    intro τ
    have h := hgapLam τ (T.j - 1) hj2
    rw [hj1] at h
    exact h
  have hgapmu : ∀ τ, θ ≤ gap T.j (T.lamS lam (θ ^ 2)) τ := by
    intro τ
    have h := hgapj τ
    have hn := hnuD τ (T.j - 1)
    rw [hj1] at hn
    simp only [gap] at h ⊢
    rw [hentS, hentS]
    have : θ ^ 2 * (ent T.nu τ (T.j - 1) - ent T.nu τ T.j) ≤ θ ^ 2 * (2 * R) :=
      mul_le_mul_of_nonneg_left hn (by positivity)
    linarith
  refine ⟨?_, hθpos, hθθ₀, by linarith, by linarith, hnmu1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := (le_max_left 10 _).trans hB
    omega
  · intro τ; have := hgapj τ; linarith
  · have h1 : T.j - 1 < T.j := by have := T.j_pos; omega
    simp only [gap]
    rw [hent, hent]
    have := hg0
    simp only [gap] at this
    simp [h1]
    linarith
  · intro τ i hi hij
    rw [hent, hent]
    have hc := hcg τ i hi hij
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · have h1 : i < T.j := by omega
      by_cases hτ : τ = τ₀
      · subst hτ
        simp [h1, hlt]
        linarith
      · simp [hτ]
        linarith
    · have h1 : ¬ i < T.j := by omega
      have h2 : ¬ i + 1 < T.j := by omega
      simp [h1, h2]
      linarith
  · exact dominant_of_gaps lam (fun τ i hi => by have := hgapLam τ i hi; linarith)
  · refine dominant_of_gaps _ (fun τ i hi => ?_)
    rw [hentS, hentS]
    have h := hgapLam τ i hi
    have hn := hnuD τ i
    have : θ ^ 2 * (ent T.nu τ i - ent T.nu τ (i + 1)) ≤ θ ^ 2 * (2 * R) :=
      mul_le_mul_of_nonneg_left hn (by positivity)
    linarith
  · intro τ
    have hg := hgapmu τ
    have hB2 : (0 : ℝ) ≤ (B : ℝ) - 2 := by linarith
    have h1 : ((B : ℝ) - 2) * θ ≤ ((B : ℝ) - 2) * gap T.j (T.lamS lam (θ ^ 2)) τ :=
      mul_le_mul_of_nonneg_left hg hB2
    have he : ((B : ℝ) - 2) * θ = θ * B - 2 * θ := by ring
    have h3 : 4 * (Fintype.card Ψ : ℝ) * ‖T.lamS lam (θ ^ 2)‖ ≤ 4 * (Fintype.card Ψ : ℝ) :=
      mul_le_of_le_one_right (by positivity) hnmu1
    linarith
  · have hsub : T.lamS lam (θ ^ 2) - lam₀ = D - θ ^ 2 • T.nu := by
      funext τ i
      simp [RootTower.lamS, lam, D]
      ring
    rw [hsub]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    linarith

end RootFieldNumerics
