import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.DegreeHermitianFormula
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.HomOmZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.BdCompact
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.BdGrowth
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.QhtFacts
open UpperTheory.V.Lit.Geo
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af

private theorem le_exp_self' (x : ℝ) : x ≤ Real.exp x := by
  have := Real.add_one_le_exp x
  linarith

theorem UpperTheory.V.Lit.Geo.prim :
    Prim := by
  intro E _ _ _ a U hU Ξ f Y C c f₀ hS q η hη hM
  have hc := hS.c_pos
  have hC : 0 ≤ C := (abs_nonneg _).trans (hS.near 1 0 1 (by simp) (by simp))
  have hq := (qhtFacts E a).1
  have hqf : ∀ (g : GA E a) (x : ℝ), f g ≤ x → qht g ≤ Real.exp (C * (1 + x)) := fun g x hx =>
    (Real.le_exp_log _).trans (Real.exp_le_exp.2 ((hS.le_f g).trans (mul_le_mul_of_nonneg_left (by linarith) hC)))
  obtain ⟨B, hB, hstep⟩ := oneStep E a U Ξ (-Y) C hS.fld.neg q
  obtain ⟨N, C', hC', hgr⟩ := (bdGrowth E a Ξ (q + 1) _).1 hM
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = |f₀| + C := ⟨_, rfl⟩
  have hf0 := le_abs_self f₀
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  obtain ⟨M₀, hM₀, hcp⟩ := bdCompact E a U hU Ξ q η hη (Real.exp (C * (1 + K)))
  have p1 : 0 ≤ (N : ℝ) * C * (1 + K + C) := by positivity
  have p2 : 0 ≤ (N : ℝ) * C * c := by positivity
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = M₀ + 2 * B + C' + N * C * (1 + K + C) + N * C * c := ⟨_, rfl⟩
  have hD0 : 0 ≤ D := by rw [hD]; positivity
  have hneg : ∀ (g : GA E a) (t : ℝ), (1 : Matrix (Fin a) (Fin a) (Cinf E)) + t • ((-Y) g).1 = 1 + (-t) • (Y g).1 :=
    fun g t => by
      rw [neg_smul]
      exact congrArg (1 + ·) (smul_neg t (Y g).1)
  have hnear : ∀ (g : GA E a) (t : ℝ), t ∈ Set.Icc (0 : ℝ) 1 → ∀ h : GL (Fin a) (Cinf E),
      h.val * star h.val = 1 + t • ((-Y) g).1 → f (g * infGL E a h) ≤ f g + C := fun g t ht h hh => by
    have := (abs_le.1 (hS.near g (-t) h (by rw [abs_neg, abs_of_nonneg ht.1]; exact ht.2) (hh.trans (hneg g t)))).2
    linarith
  have main : ∀ n : ℕ, ∃ η' : Co Ξ q, IsLev U Ξ η' ∧ dCo (smLie Ξ) η' = dCo (smLie Ξ) η ∧
      ∀ g : GA E a, f g ≤ K + n * c → Bd η' g (Real.exp (D * (n + 1))) := by
    intro n
    induction n with
    | zero =>
      refine ⟨η, hη, rfl, fun g hg => (hcp g (hqf g K (by simpa using hg))).mono ?_⟩
      refine (le_exp_self' M₀).trans (Real.exp_le_exp.2 ?_)
      simp only [Nat.cast_zero, zero_add, mul_one]
      linarith
    | succ n ih =>
      obtain ⟨ζ, hζ, hd, hb⟩ := ih
      obtain ⟨ζ', hζ', hd', hb'⟩ := hstep ζ hζ
      refine ⟨ζ', hζ', hd'.trans hd, fun g hg => ?_⟩
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have hnc : 0 ≤ (n : ℝ) * c := by positivity
      push_cast at hg ⊢
      refine (hb' g (Real.exp (D * (n + 1))) (Real.exp (D * (n + 1))) (Real.exp_pos _).le (Real.exp_pos _).le
        (fun h hh => hb _ ?_) (fun t ht h hh => ?_)).mono ?_
      · by_cases hf : f₀ ≤ f g
        · have := hS.down g h hf (hh.trans (sub_eq_add_neg _ _).symm)
          linarith
        · have := hnear g 1 ⟨zero_le_one, le_rfl⟩ h (by rw [one_smul]; exact hh)
          have := not_le.1 hf
          linarith
      · rw [hd]
        refine (hgr _).mono ?_
        have h1 := hqf (g * infGL E a h) (K + (n + 1) * c + C) (by have := hnear g t ht h hh; linarith)
        have h2 := pow_le_pow_left₀ (zero_le_one.trans (hq _)) h1 N
        rw [← Real.exp_nat_mul] at h2
        refine (mul_le_mul (le_exp_self' C') h2 (pow_nonneg (zero_le_one.trans (hq _)) _) (Real.exp_pos _).le).trans ?_
        rw [← Real.exp_add]
        refine Real.exp_le_exp.2 ?_
        have e : D * (n + 1) = C' + N * (C * (1 + (K + (n + 1) * c + C))) +
            ((M₀ + 2 * B) * (n + 1) + (C' + N * C * (1 + K + C)) * n) := by rw [hD]; ring
        rw [e]
        exact le_add_of_nonneg_right (by positivity)
      · have e : Real.exp (D * (n + 1 + 1)) = Real.exp D * Real.exp (D * (n + 1)) := by
          rw [← Real.exp_add]; congr 1; ring
        have h2 : 2 * B ≤ Real.exp D := le_trans (by linarith) (le_exp_self' D)
        rw [e]
        have := mul_le_mul_of_nonneg_right h2 (Real.exp_pos (D * (n + 1))).le
        linarith
  refine ⟨D, hD0, fun n => ?_⟩
  obtain ⟨ζ, h1, h2, h3⟩ := main n
  exact ⟨ζ, h1, h2, fun g hg => h3 g (by linarith)⟩
