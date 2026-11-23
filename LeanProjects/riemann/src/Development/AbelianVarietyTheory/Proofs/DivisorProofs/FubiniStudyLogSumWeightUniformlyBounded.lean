import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousHermSectionValueMulConjAndNormBounded
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularNonvanishingLocusSectionProperties
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp

theorem abs_log_sum_pow_le {D : ℕ} (v : Fin (D + 1) → ℝ) (hv : ∀ l, 0 ≤ v l) {m M : ℝ} (hm : 0 < m) (hM : 1 ≤ M)
    (hvM : ∀ l, v l ≤ M) (hvm : ∃ l, m ≤ v l) {e n : ℕ} (he : 0 < e) (hn : 1 ≤ n) :
    |((e : ℝ) * n)⁻¹ * Real.log (∑ l, v l ^ (2 * n))| ≤ Real.log (D + 1) + 2 * Real.log M + 2 * |Real.log m| := by
  obtain ⟨l₀, hl₀⟩ := hvm
  have hD : 0 ≤ Real.log (D + 1 : ℝ) := Real.log_nonneg (by linarith [(Nat.cast_nonneg D : (0 : ℝ) ≤ D)])
  have hM' : 0 ≤ Real.log M := Real.log_nonneg hM
  have hlo : m ^ (2 * n) ≤ ∑ l, v l ^ (2 * n) :=
    (pow_le_pow_left₀ hm.le hl₀ _).trans
      (Finset.single_le_sum (f := fun l => v l ^ (2 * n)) (fun l _ => pow_nonneg (hv l) _) (Finset.mem_univ l₀))
  have hhi : ∑ l, v l ^ (2 * n) ≤ (D + 1 : ℝ) * M ^ (2 * n) := by
    refine (Finset.sum_le_sum (g := fun _ => M ^ (2 * n)) fun l _ => pow_le_pow_left₀ (hv l) (hvM l) _).trans ?_
    simp
  have hp : 0 < m ^ (2 * n) := pow_pos hm _
  have h1 := Real.log_le_log hp hlo
  have h2 := Real.log_le_log (hp.trans_le hlo) hhi
  rw [Real.log_pow] at h1
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow] at h2
  push_cast at h1 h2
  have he' : (1 : ℝ) ≤ e := by exact_mod_cast he
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hen : (n : ℝ) ≤ e * n := le_mul_of_one_le_left (by linarith) he'
  have ha := abs_nonneg (Real.log m)
  have hb := neg_abs_le (Real.log m)
  rw [abs_mul, abs_of_nonneg (by positivity), inv_mul_le_iff₀ (by positivity)]
  refine le_trans ?_ (mul_le_mul_of_nonneg_right hen (by positivity))
  rw [abs_le]
  constructor <;> nlinarith [mul_nonneg (sub_nonneg.2 hn') hD, mul_nonneg (sub_nonneg.2 hn') hM',
    mul_nonneg (sub_nonneg.2 hn') ha, mul_nonneg (zero_le_one.trans hn') (sub_nonneg.2 hb)]

theorem can_bound : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p) (e : ℕ) (x : Fin (D + 1) → X.functionField), Gens P D e x → ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ, 1 ≤ n → ∀ (σ : k →+* ℂ) (y : CxPts p σ), |((e : ℝ) * n)⁻¹ * Real.log (∑ l, P.nu e 0 σ y (x l) ^ (2 * n))| ≤ B := by
  intro k _ X _ p D hX P e x hx
  have hnn : ∀ (σ : k →+* ℂ) (y : CxPts p σ) l, 0 ≤ P.nu e 0 σ y (x l) := fun σ y l => by
    rw [← norm_val]; exact norm_nonneg _
  have hc := fun l => (GlobalTheory.HSAmp.continuous_val_and_bounded k X p D hX P e 0).2 (x l) (hx.mem l)
  choose C hC using fun l => (hc l).2
  have hlow : ∀ σ : k →+* ℂ, ∃ κ : ℝ, 0 < κ ∧ ∀ y : CxPts p σ, κ ≤ ∑ l, P.nu e 0 σ y (x l) := fun σ => by
    haveI := hX.compactSpace σ
    have hcont : Continuous fun y : CxPts p σ => ∑ l, P.nu e 0 σ y (x l) :=
      continuous_finsetSum _ fun l _ => (hc l).1 σ
    have hpos : ∀ y : CxPts p σ, 0 < ∑ l, P.nu e 0 σ y (x l) := fun y => by
      obtain ⟨l, hl⟩ := hx.cover (under y)
      exact Finset.sum_pos' (fun l _ => hnn σ y l) ⟨l, Finset.mem_univ _,
        ((GlobalTheory.HSAmp.nv_rules k X p P e 0 (x l) (hx.mem l)).2.2.2.2 (x l) (hx.mem l) σ y hl).2⟩
    rcases isEmpty_or_nonempty (CxPts p σ) with h | h
    · exact ⟨1, one_pos, fun y => h.elim y⟩
    · obtain ⟨y₀, -, hy₀⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty hcont.continuousOn
      exact ⟨_, hpos y₀, fun y => hy₀ (Set.mem_univ y)⟩
  choose κ hκ hκ' using hlow
  haveI := hX.finite_emb
  haveI := Fintype.ofFinite (k →+* ℂ)
  have hs : 0 ≤ ∑ σ, (κ σ)⁻¹ := Finset.sum_nonneg fun σ _ => (inv_pos.2 (hκ σ)).le
  have hκ₀ : ∀ σ, (1 + ∑ σ, (κ σ)⁻¹)⁻¹ ≤ κ σ := fun σ => by
    refine inv_le_of_inv_le₀ (hκ σ) ?_
    have := Finset.single_le_sum (f := fun σ => (κ σ)⁻¹) (fun σ _ => (inv_pos.2 (hκ σ)).le) (Finset.mem_univ σ)
    linarith
  have hs' : 0 ≤ ∑ l, |C l| := Finset.sum_nonneg fun l _ => abs_nonneg _
  have hM : 1 ≤ 1 + ∑ l, |C l| := by linarith
  refine ⟨Real.log (D + 1) + 2 * Real.log (1 + ∑ l, |C l|) + 2 * |Real.log ((1 + ∑ σ, (κ σ)⁻¹)⁻¹ / (D + 1))|, ?_,
    fun n hn σ y => abs_log_sum_pow_le _ (hnn σ y) (by positivity) hM (fun l => ?_) ?_ hx.pos hn⟩
  · have h1 : 0 ≤ Real.log (D + 1 : ℝ) := Real.log_nonneg (by linarith [(Nat.cast_nonneg D : (0 : ℝ) ≤ D)])
    have h2 := Real.log_nonneg hM
    positivity
  · have := Finset.single_le_sum (f := fun l => |C l|) (fun l _ => abs_nonneg _) (Finset.mem_univ l)
    linarith [hC l σ y, le_abs_self (C l)]
  · obtain ⟨l, -, hl⟩ := Finset.exists_le_of_sum_le (s := Finset.univ) Finset.univ_nonempty
      (f := fun _ : Fin (D + 1) => (1 + ∑ σ, (κ σ)⁻¹)⁻¹ / (D + 1 : ℝ)) (g := fun l => P.nu e 0 σ y (x l)) (by
        refine le_trans (le_of_eq ?_) ((hκ₀ σ).trans (hκ' σ y))
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        field_simp)
    exact ⟨l, hl⟩

end GlobalTheory.HSAmp
