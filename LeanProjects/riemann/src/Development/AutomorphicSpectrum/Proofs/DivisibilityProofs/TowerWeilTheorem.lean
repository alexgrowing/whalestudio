import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.KleimanSt
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ArithFunctionalLipschitzWeightsStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.TowerComponentHeightBoundStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.TowerGapHeightUniformBoundStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.PerturbedWeightGapBoundsStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagDegreeLeGapStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ContinuousWallBoundExtendStatement

noncomputable section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

namespace WallBound

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ}

theorem l1_le_card_mul_of_norm_le_one' (lam : Wt Ψ N) (h : ‖lam‖ ≤ 1) : l1 lam ≤ (Fintype.card Ψ : ℝ) * N := by
  have hb : ∀ τ i, |lam τ i| ≤ 1 := fun τ i => by
    have h1 : ‖lam τ‖ ≤ ‖lam‖ := norm_le_pi_norm lam τ
    have h2 : ‖lam τ i‖ ≤ ‖lam τ‖ := norm_le_pi_norm (lam τ) i
    rw [Real.norm_eq_abs] at h2
    linarith
  unfold l1
  calc ∑ τ, ∑ i, |lam τ i| ≤ ∑ _τ : Ψ, ∑ _i : Fin N, (1 : ℝ) :=
        Finset.sum_le_sum fun τ _ => Finset.sum_le_sum fun i _ => hb τ i
    _ = (Fintype.card Ψ : ℝ) * N := by simp

theorem toA_linRoot_pow (lam : Wt Ψ N) (d : ℕ) : toA (linRoot lam ^ d) = linA lam 0 ^ d := by
  simp [toA, linA, map_pow]

theorem continuous_lin_zero (Φ : RPA Ψ N →ₗ[ℝ] ℝ) (d : ℕ)
    (h : Continuous fun z : Wt Ψ N × ℝ => Φ (linA z.1 z.2 ^ d)) :
    Continuous fun lam : Wt Ψ N => Φ (linA lam 0 ^ d) := by
  have hz : Continuous fun lam : Wt Ψ N => ((lam, (0 : ℝ)) : Wt Ψ N × ℝ) :=
    Continuous.prodMk continuous_id continuous_const
  have h2 := h.comp hz
  simp only [Function.comp_def] at h2
  exact h2

theorem continuous_PB (T : RootTower Ψ N) (II : IntersectionSystem) (B : ℕ) :
    Continuous fun lam : Wt Ψ N => T.PB II B lam := by
  obtain ⟨hcont, -, -⟩ := GlobalTheory.T.arith_functional_lipschitz_weights Ψ N (dimFl Ψ N + 1)
  have h : (fun lam : Wt Ψ N => T.PB II B lam) =
      fun lam => ∑ c, (T.M B c).PP II (linA lam 0 ^ (dimFl Ψ N + 1)) := by
    funext lam
    simp only [RootTower.PB, RootTower.PPt, RootTower.PPc, toA_linRoot_pow]
  rw [h]
  exact continuous_finset_sum _ fun c _ => continuous_lin_zero _ _ (hcont _)

theorem one_le_log {B : ℕ} (h : 3 ≤ B) : 1 ≤ Real.log B := by
  have hB : (3 : ℝ) ≤ B := by exact_mod_cast h
  rw [Real.le_log_iff_exp_le (by linarith)]
  have := Real.exp_one_lt_d9
  linarith

theorem log_div_le {B : ℕ} (h : 3 ≤ B) (a : ℝ) (ha : 1 ≤ a) :
    Real.log (B / (a / B) ^ 2) ≤ 3 * Real.log B := by
  have hB : (0 : ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  have ha0 : 0 < a := by linarith
  have h1 : (B : ℝ) / (a / B) ^ 2 ≤ (B : ℝ) ^ 3 := by
    rw [div_pow, div_div_eq_mul_div, div_le_iff₀ (by positivity)]
    have : (1 : ℝ) ≤ a ^ 2 := by nlinarith
    nlinarith [pow_pos hB 3]
  have h2 : 0 < (B : ℝ) / (a / B) ^ 2 := by positivity
  calc Real.log (B / (a / B) ^ 2) ≤ Real.log ((B : ℝ) ^ 3) := Real.log_le_log h2 h1
    _ = 3 * Real.log B := by rw [Real.log_pow]; norm_num

theorem three_terms {q a p cs c3 c2 cp c8 v n θ L Ls md dist s : ℝ} (hcs : 0 ≤ cs) (hc8 : 0 ≤ c8) (hcp : 0 ≤ cp)
    (hv : 0 ≤ v) (hn : 0 ≤ n) (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hL : 1 ≤ L) (hs : s = θ ^ 2)
    (hLs : Ls ≤ 3 * L) (hLs0 : 0 ≤ Ls) (hmd0 : 0 ≤ md) (hmd : md ≤ v * (c8 * (2 * θ)))
    (hsq : |a| ≤ cs * Ls * md) (hap : |a - p| ≤ c3 * s)
    (hpq : |p - q| ≤ cp * (|c2| * L) * (dist + |s - 0|)) (hdist : dist ≤ 2 * θ + n * θ ^ 2) :
    |q| ≤ (|c3| + 6 * cs * c8 * v + cp * |c2| * (3 + n)) * (θ * L) := by
  have hθ2 : θ ^ 2 ≤ θ := by nlinarith
  have hL0 : 0 ≤ L := by linarith
  have hθL : 0 ≤ θ * L := by positivity
  have t1 : |a| ≤ 6 * cs * c8 * v * (θ * L) := by
    have e1 : Ls * md ≤ (3 * L) * (v * (c8 * (2 * θ))) :=
      mul_le_mul hLs hmd hmd0 (by linarith)
    calc |a| ≤ cs * Ls * md := hsq
      _ = cs * (Ls * md) := by ring
      _ ≤ cs * ((3 * L) * (v * (c8 * (2 * θ)))) := mul_le_mul_of_nonneg_left e1 hcs
      _ = 6 * cs * c8 * v * (θ * L) := by ring
  have t2 : |a - p| ≤ |c3| * (θ * L) := by
    have e : s ≤ θ * L := by
      rw [hs]
      nlinarith
    have hs0 : 0 ≤ s := by rw [hs]; positivity
    calc |a - p| ≤ c3 * s := hap
      _ ≤ |c3| * s := mul_le_mul_of_nonneg_right (le_abs_self _) hs0
      _ ≤ |c3| * (θ * L) := mul_le_mul_of_nonneg_left e (abs_nonneg _)
  have t3 : |p - q| ≤ cp * |c2| * (3 + n) * (θ * L) := by
    have hs0 : 0 ≤ s := by rw [hs]; positivity
    have e : dist + |s - 0| ≤ (3 + n) * θ := by
      rw [sub_zero, abs_of_nonneg hs0, hs]
      nlinarith [mul_le_mul_of_nonneg_left hθ2 hn]
    have hk : 0 ≤ cp * (|c2| * L) := by positivity
    calc |p - q| ≤ cp * (|c2| * L) * (dist + |s - 0|) := hpq
      _ ≤ cp * (|c2| * L) * ((3 + n) * θ) := mul_le_mul_of_nonneg_left e hk
      _ = cp * |c2| * (3 + n) * (θ * L) := by ring
  have tri : |q| ≤ |a| + |a - p| + |p - q| := by
    have h1 : q = a - (a - p) - (p - q) := by ring
    calc |q| = |a - (a - p) - (p - q)| := by rw [← h1]
      _ ≤ |a - (a - p)| + |p - q| := abs_sub _ _
      _ ≤ |a| + |a - p| + |p - q| := by gcongr; exact abs_sub _ _
  linarith

end WallBound

open WallBound in

theorem thmW_tower : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.KleimanNefFStatement →
    (∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)], ReciprocityTheory.ChartRestriction.G.AI.I1.ExistsUniqueStatement ℚ ι) →
    ReciprocityTheory.ChartRestriction.G.Geo.DivSuppArithStatement → SuccessiveMinimaLowerBound → SuccessiveMinimaUpperBound → ∀ II : IntersectionSystem,
    IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N),
    T.Proportional → T.I1 II → T.I2 II → T.I3 → T.I5 II → T.I6 II → T.I7 → T.ThmW II := by
  intro hKl hEx hDs hZ1 hZ2 II hII Ψ _ _ N T hP h1 h2 h3 h5 h6 h7 c₀ hc₀
  have hc₁ : 0 < c₀ / 2 := by positivity
  obtain ⟨θ₀, hθ₀, Cs, hCs, hsq⟩ := GlobalTheory.T.tower_gap_height_uniform_bound hZ1 hZ2 II hII Ψ N T h3 h5 h6 (c₀ / 2) hc₁
  obtain ⟨s₀, hs₀, C3, hI2⟩ := h2 ((Fintype.card Ψ : ℝ) * N)
  obtain ⟨C2, hI1⟩ := h1
  obtain ⟨C8, hC8, hdeg⟩ := GlobalTheory.T.flag_degree_le_gap Ψ N T.j T.j_pos T.j_lt
  obtain ⟨-, hlin, Cp, hCp, hLip⟩ := GlobalTheory.T.arith_functional_lipschitz_weights Ψ N (dimFl Ψ N + 1)
  obtain ⟨B₁, hB₁⟩ := GlobalTheory.T.perturbed_weight_gap_bounds Ψ N T (c₀ / 2) (min θ₀ s₀) hc₁ (lt_min hθ₀ hs₀)
  refine ⟨(∑ c, (|C3| + 6 * Cs * C8 * T.vol c + Cp * |C2| * (3 + ‖T.nu‖))) * (5 * Fintype.card Ψ), B₁,
    fun B hB τ₀ lam₀ hlam₀ => ?_⟩
  refine GlobalTheory.T.continuous_wall_bound_extend Ψ N T.j c₀ _ τ₀ (fun l => T.PB II B l) T.j_pos T.j_lt hc₀ (continuous_PB T II B) ?_ lam₀ hlam₀
  intro l hlr hlw
  obtain ⟨hB3, hθ, hθle, hθ1, hnl, hnl2, hgaps, hgap0, hcg, hdom, hdom2, hnef, hdist⟩ := hB₁ B hB τ₀ l hlw
  have hf : (1 : ℝ) ≤ Fintype.card Ψ := by
    have : 0 < Fintype.card Ψ := Fintype.card_pos_iff.mpr ⟨τ₀⟩
    exact_mod_cast this
  have hBpos : (0 : ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  set θ : ℝ := 5 * (Fintype.card Ψ : ℝ) / B with hθdef
  set lam : Wt Ψ N := fun τ i => l τ i + (if τ = τ₀ ∧ (i : ℕ) < T.j then 2 * θ else 0) with hlamdef
  let s : ℚ := (5 * (Fintype.card Ψ : ℚ) / B) ^ 2
  have hs : (s : ℝ) = θ ^ 2 := by simp [s, hθdef]
  have hdist' : ‖T.lamS lam s - l‖ ≤ 2 * θ + ‖T.nu‖ * θ ^ 2 := by rw [hs]; exact hdist
  rw [← hs] at hnl2 hdom2 hnef
  have hrat : IsRatWt lam := by
    intro τ i
    obtain ⟨q, hq⟩ := hlr τ i
    by_cases h : τ = τ₀ ∧ (i : ℕ) < T.j
    · exact ⟨q + 2 * (5 * (Fintype.card Ψ : ℚ) / B), by
        show l τ i + (if τ = τ₀ ∧ (i : ℕ) < T.j then 2 * θ else 0) = _
        rw [if_pos h, hq, hθdef]
        push_cast
        ring⟩
    · exact ⟨q, by
        show l τ i + (if τ = τ₀ ∧ (i : ℕ) < T.j then 2 * θ else 0) = _
        rw [if_neg h, hq, add_zero]⟩
  have hs0 : (0 : ℝ) < s := by rw [hs]; positivity
  have hsQ : (0 : ℚ) ≤ s := by exact_mod_cast hs0.le
  have hθ2 : θ ^ 2 ≤ θ := by nlinarith
  have hsle : (s : ℝ) ≤ s₀ := by
    rw [hs]
    exact hθ2.trans (hθle.trans (min_le_right _ _))
  have hs1 : |(s : ℝ)| ≤ 1 := by
    rw [abs_of_pos hs0, hs]
    linarith
  have hnl0 : ‖l‖ ≤ 1 := hlw.1.trans (by norm_num)
  have hL := one_le_log hB3
  have hper : ∀ c, |T.PPc II B c (linRoot l ^ (dimFl Ψ N + 1))| ≤
      (|C3| + 6 * Cs * C8 * T.vol c + Cp * |C2| * (3 + ‖T.nu‖)) * (θ * Real.log B) := by
    intro c
    obtain ⟨hm0, hm1⟩ := GlobalTheory.T.tower_component_height_bound hKl hEx hDs II hII Ψ N T hP h7 B c lam s hrat hsQ hdom hdom2
    have hsqc := hsq B (by omega) c lam θ s hrat hnl hθ (hθle.trans (min_le_left _ _)) hs hgaps hcg hdom2 hnef hm0
    have hI2c := hI2 B (by omega) c lam s (l1_le_card_mul_of_norm_le_one' lam hnl) hs0 hsle hdom2
    have hmono : ∀ m, |(T.M B c).PP II (monomial m 1)| ≤ |C2| * Real.log B := fun m =>
      (hI1 B (by omega) c m).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith))
    have hLipc := hLip ((T.M B c).PP II) (|C2| * Real.log B) hmono (T.lamS lam s) l s 0 hnl2 hnl0 hs1 (by simp)
    have hv : 0 < T.vol c := hP.1 c
    have hmd : T.mDeg B c lam s ≤ T.vol c * (C8 * (2 * θ)) := by
      refine hm1.trans (mul_le_mul_of_nonneg_left ?_ hv.le)
      rw [← hgap0]
      exact hdeg lam τ₀ hnl hdom
    have hLs : Real.log (B / (s : ℝ)) ≤ 3 * Real.log B := by
      rw [hs]
      exact log_div_le hB3 (5 * (Fintype.card Ψ : ℝ)) (by linarith)
    have hLs0 : 0 ≤ Real.log (B / (s : ℝ)) := by
      refine Real.log_nonneg ?_
      rw [le_div_iff₀ hs0, hs]
      have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast (by omega : 1 ≤ B)
      nlinarith
    have hq : T.PPc II B c (linRoot l ^ (dimFl Ψ N + 1)) = (T.M B c).PP II (linA l 0 ^ (dimFl Ψ N + 1)) := by
      simp only [RootTower.PPc, toA_linRoot_pow]
    rw [hq]
    exact three_terms hCs hC8 hCp hv.le (norm_nonneg _) hθ hθ1 hL hs hLs hLs0 hm0 hmd hsqc hI2c hLipc hdist'
  have hsum : |T.PB II B l| ≤
      (∑ c, (|C3| + 6 * Cs * C8 * T.vol c + Cp * |C2| * (3 + ‖T.nu‖))) * (θ * Real.log B) := by
    rw [Finset.sum_mul]
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun c _ => hper c)
  refine hsum.trans (le_of_eq ?_)
  rw [hθdef]
  ring

end GlobalTheory.CompanionTheory.Ar.Top
