import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
import Development.WeilBound.CoreStatements.FlagImmersions.MapProdLinear

open MvPolynomial Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace RootFieldNumerics.Pc

theorem abs_prod_sub_prod_le {ι : Type} (s : Finset ι) (a b : ι → ℝ) (δ : ℝ)
    (ha : ∀ i, |a i| ≤ 1) (hb : ∀ i, |b i| ≤ 1) (h : ∀ i, |a i - b i| ≤ δ) :
    |∏ i ∈ s, a i - ∏ i ∈ s, b i| ≤ s.card * δ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.card_insert_of_notMem hi]
    have hB : |∏ i ∈ s, b i| ≤ 1 := by
      rw [Finset.abs_prod]
      exact Finset.prod_le_one (fun _ _ => abs_nonneg _) (fun i _ => hb i)
    have e : a i * ∏ i ∈ s, a i - b i * ∏ i ∈ s, b i =
        a i * (∏ i ∈ s, a i - ∏ i ∈ s, b i) + (a i - b i) * ∏ i ∈ s, b i := by ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    have h1 : |a i| * |∏ i ∈ s, a i - ∏ i ∈ s, b i| ≤ 1 * (s.card * δ) :=
      mul_le_mul (ha i) ih (abs_nonneg _) zero_le_one
    have h2 : |a i - b i| * |∏ i ∈ s, b i| ≤ δ * 1 :=
      mul_le_mul (h i) hB (abs_nonneg _) ((abs_nonneg _).trans (h i))
    push_cast
    linarith

def linCoef {Ψ : Type} {N : ℕ} (lam : Wt Ψ N) (s : ℝ) : Option (Ψ × Fin N) → ℝ
  | none => s
  | some x => -lam x.1 x.2

theorem linA_eq {Ψ : Type} [Fintype Ψ] {N : ℕ} (lam : Wt Ψ N) (s : ℝ) :
    linA lam s = ∑ j, C (linCoef lam s j) * X j := by
  rw [Fintype.sum_option]
  simp [linA, toA, linRoot, linCoef, add_comm]

theorem map_linA_pow {Ψ : Type} [Fintype Ψ] {N : ℕ} (d : ℕ) (Φ : RPA Ψ N →ₗ[ℝ] ℝ)
    (lam : Wt Ψ N) (s : ℝ) [Fintype (Fin d → Option (Ψ × Fin N))] :
    Φ (linA lam s ^ d) = ∑ w : Fin d → Option (Ψ × Fin N), (∏ k, linCoef lam s (w k)) *
      Φ (monomial (∑ k, Finsupp.single (w k) 1) 1) := by
  have := RootFieldNumerics.map_prod_linear (Option (Ψ × Fin N)) d Φ (fun _ => linCoef lam s)
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← linA_eq] at this
  convert this

end RootFieldNumerics.Pc

theorem RootFieldNumerics.linear_root_power_lipschitz : ∀ (Ψ : Type) [Fintype Ψ] (N d : ℕ), (∀ Φ : RPA Ψ N →ₗ[ℝ] ℝ, Continuous fun z : Wt Ψ N × ℝ => Φ (linA z.1 z.2 ^ d)) ∧ (∀ lam : Wt Ψ N, linA lam 0 = toA (linRoot lam)) ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ (Φ : RPA Ψ N →ₗ[ℝ] ℝ) (b : ℝ), (∀ m, |Φ (monomial m 1)| ≤ b) → ∀ (lam mu : Wt Ψ N) (s s' : ℝ), ‖lam‖ ≤ 1 → ‖mu‖ ≤ 1 → |s| ≤ 1 → |s'| ≤ 1 → |Φ (linA lam s ^ d) - Φ (linA mu s' ^ d)| ≤ C * b * (‖lam - mu‖ + |s - s'|) := by
  intro Ψ _ N d
  classical
  refine ⟨fun Φ => ?_, fun lam => by simp [linA], ?_⟩
  · simp only [RootFieldNumerics.Pc.map_linA_pow]
    refine continuous_finsetSum _ fun w _ => Continuous.mul
      (continuous_finsetProd _ fun k _ => ?_) continuous_const
    cases w k with
    | none => exact continuous_snd
    | some x =>
      simp only [RootFieldNumerics.Pc.linCoef]
      fun_prop
  · refine ⟨(Fintype.card (Fin d → Option (Ψ × Fin N)) : ℝ) * d, by positivity, ?_⟩
    intro Φ b hb lam mu s s' hl hm hs hs'
    have hb0 : 0 ≤ b := (abs_nonneg _).trans (hb 0)
    have hent : ∀ (l : Wt Ψ N) τ i, |l τ i| ≤ ‖l‖ := fun l τ i =>
      (norm_le_pi_norm (l τ) i).trans (norm_le_pi_norm l τ)
    have hc : ∀ (l : Wt Ψ N) (t : ℝ), ‖l‖ ≤ 1 → |t| ≤ 1 → ∀ j, |RootFieldNumerics.Pc.linCoef l t j| ≤ 1 := by
      intro l t h1 h2 j
      cases j with
      | none => exact h2
      | some x => simpa [RootFieldNumerics.Pc.linCoef] using (hent l x.1 x.2).trans h1
    have hd : ∀ j, |RootFieldNumerics.Pc.linCoef lam s j - RootFieldNumerics.Pc.linCoef mu s' j| ≤ ‖lam - mu‖ + |s - s'| := by
      intro j
      cases j with
      | none => exact le_add_of_nonneg_left (norm_nonneg _)
      | some x =>
        have h1 := hent (lam - mu) x.1 x.2
        have e : RootFieldNumerics.Pc.linCoef lam s (some x) - RootFieldNumerics.Pc.linCoef mu s' (some x) =
            -((lam - mu) x.1 x.2) := by
          simp only [RootFieldNumerics.Pc.linCoef, Pi.sub_apply]; ring
        rw [e, abs_neg]
        exact h1.trans (le_add_of_nonneg_right (abs_nonneg _))
    rw [RootFieldNumerics.Pc.map_linA_pow, RootFieldNumerics.Pc.map_linA_pow, ← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_card_nsmul _ _ (d * (‖lam - mu‖ + |s - s'|) * b) fun w _ => ?_).trans ?_
    · rw [← sub_mul, abs_mul]
      refine mul_le_mul ?_ (hb _) (abs_nonneg _) (by positivity)
      simpa using RootFieldNumerics.Pc.abs_prod_sub_prod_le Finset.univ _ _ _
        (fun k => hc lam s hl hs (w k)) (fun k => hc mu s' hm hs' (w k)) (fun k => hd (w k))
    · rw [Finset.card_univ, nsmul_eq_mul]
      exact le_of_eq (by ring)
