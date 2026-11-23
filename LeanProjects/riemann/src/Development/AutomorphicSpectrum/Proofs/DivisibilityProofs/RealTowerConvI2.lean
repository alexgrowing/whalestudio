import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.AgreementPos
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.RefLinked
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RealTowerArithAgreementStatement

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Top.ConvergenceI2

theorem sum_shift_le {N : ℕ} (l : Fin N → ℝ) :
    ∑ i : Fin N, (if h : (i : ℕ) + 1 < N then |l ⟨(i : ℕ) + 1, h⟩| else 0) ≤ ∑ i, |l i| := by
  let F : ℕ → ℝ := fun i => if h : i < N then |l ⟨i, h⟩| else 0
  have hF : ∀ i, 0 ≤ F i := by
    intro i
    simp only [F]
    split_ifs
    · exact abs_nonneg _
    · exact le_rfl
  have e1 : ∑ i : Fin N, (if h : (i : ℕ) + 1 < N then |l ⟨(i : ℕ) + 1, h⟩| else 0) =
      ∑ i ∈ Finset.range N, F (i + 1) := by
    rw [Finset.sum_range]
  have e2 : ∑ i : Fin N, |l i| = ∑ i ∈ Finset.range N, F i := by
    rw [Finset.sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [F]
  have e3 : ∑ i ∈ Finset.range (N + 1), F i = ∑ i ∈ Finset.range N, F (i + 1) + F 0 :=
    Finset.sum_range_succ' F N
  have e4 : ∑ i ∈ Finset.range (N + 1), F i = ∑ i ∈ Finset.range N, F i + F N :=
    Finset.sum_range_succ F N
  have e5 : F N = 0 := by simp [F]
  rw [e1, e2]
  linarith [hF 0]

variable {Ψ : Type} [Fintype Ψ] {N : ℕ}

theorem abs_gap_le (lam : Wt Ψ N) (τ : Ψ) (i : Fin N) :
    |PB.gap (fun x : Ψ × Fin N => lam x.1 x.2) (τ, i)| ≤
      |lam τ i| + (if h : (i : ℕ) + 1 < N then |lam τ ⟨(i : ℕ) + 1, h⟩| else 0) := by
  by_cases h : (i : ℕ) + 1 < N
  · simp only [PB.gap, PB.gapX, dif_pos h, map_sub, eval_X]
    exact abs_sub _ _
  · simp [PB.gap, PB.gapX, dif_neg h]

theorem sum_abs_gapS_le (lam : Wt Ψ N) (u : ℝ) :
    ∑ o, |PB.gapS (fun x : Ψ × Fin N => lam x.1 x.2) u o| ≤ 2 * l1 lam + |u| := by
  rw [Fintype.sum_option, Fintype.sum_prod_type]
  have h1 : ∀ τ : Ψ, ∑ i : Fin N, |PB.gapS (fun x : Ψ × Fin N => lam x.1 x.2) u (some (τ, i))| ≤
      2 * ∑ i, |lam τ i| := by
    intro τ
    calc ∑ i : Fin N, |PB.gapS (fun x : Ψ × Fin N => lam x.1 x.2) u (some (τ, i))|
        ≤ ∑ i : Fin N, (|lam τ i| + (if h : (i : ℕ) + 1 < N then |lam τ ⟨(i : ℕ) + 1, h⟩| else 0)) :=
          Finset.sum_le_sum fun i _ => abs_gap_le lam τ i
      _ ≤ 2 * ∑ i, |lam τ i| := by
          rw [Finset.sum_add_distrib]
          linarith [sum_shift_le (lam τ)]
  have h2 := Finset.sum_le_sum fun τ (_ : τ ∈ (Finset.univ : Finset Ψ)) => h1 τ
  rw [← Finset.mul_sum] at h2
  have h3 : PB.gapS (fun x : Ψ × Fin N => lam x.1 x.2) u none = u := rfl
  rw [h3]
  unfold l1
  linarith

theorem l1_sub_smul_le (lam nu : Wt Ψ N) (s : ℝ) (h0 : 0 ≤ s) (h1 : s ≤ 1) :
    l1 (lam - s • nu) ≤ l1 lam + l1 nu := by
  unfold l1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun τ _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have e : (lam - s • nu) τ i = lam τ i - s * nu τ i := rfl
  rw [e]
  have h2 : |s * nu τ i| ≤ |nu τ i| := by
    rw [abs_mul, abs_of_nonneg h0]
    exact mul_le_of_le_one_left (abs_nonneg _) h1
  linarith [abs_sub (lam τ i) (s * nu τ i)]

end GlobalTheory.CompanionTheory.Ar.Top.ConvergenceI2

namespace GlobalTheory.CompanionTheory.Ar.Top

open ConvergenceI2 in

theorem real_tower_convergence_I2 : PB.AgreementPos → PB.Inputs → ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) (R : RealTower T), T.Conv II ∧ T.I2 II := by
  intro hAg hIn II hII Ψ _ _ N T R
  have hpos : ∀ c, 0 < (R.Sys c).t₀ := fun c => ((R.Sys c).reg none).1
  refine ⟨fun B c => ?_, fun abelian₂ => ?_⟩
  · obtain ⟨C₃, s₀, -, h⟩ := hAg hIn (dimFl Ψ N) (Option (Ψ × Fin N)) (R.Sys c) 0 (hpos c)
    have hc := (h II hII (T.M B c).K (T.M B c).ι (T.M B c).P (R.tie B c).Re).1
    exact ((GlobalTheory.T.real_tower_arith_agreement hIn II hII Ψ N (T.M B c) (R.Sys c) (R.n c) (R.tie B c) 0 0).2.2 hc (hpos c)).1
  · have hex := fun c => hAg hIn (dimFl Ψ N) (Option (Ψ × Fin N)) (R.Sys c) (2 * (abelian₂ + l1 T.nu) + 1) (hpos c)
    choose C₃ s₀ hs₀ h using hex
    have hne : (Finset.univ : Finset T.Comp).Nonempty := Finset.univ_nonempty
    have hinf : 0 < Finset.univ.inf' hne s₀ := (Finset.lt_inf'_iff hne).2 fun c _ => hs₀ c
    refine ⟨min 1 (Finset.univ.inf' hne s₀), lt_min one_pos hinf, ∑ c, |C₃ c|, ?_⟩
    intro B _ c lam s hl hs hs1 _
    have hs_one : s ≤ 1 := hs1.trans (min_le_left _ _)
    have hs_c : s ≤ s₀ c := (hs1.trans (min_le_right _ _)).trans (Finset.inf'_le _ (Finset.mem_univ c))
    have hA := h c II hII (T.M B c).K (T.M B c).ι (T.M B c).P (R.tie B c).Re
    obtain ⟨ht, hb⟩ := hA.2 s hs hs_c
    have key := GlobalTheory.T.real_tower_arith_agreement hIn II hII Ψ N (T.M B c) (R.Sys c) (R.n c) (R.tie B c) (T.lamS lam s) s
    have e1 := key.2.1 _ (Real.exp_pos _) ht
    have e2 := (key.2.2 hA.1 (hpos c)).2
    have hk : (1 : ℝ) ≤ ((T.M B c).kA : ℝ) := by exact_mod_cast (T.M B c).kA_pos
    have hu : |s / ((T.M B c).kA : ℝ)| ≤ 1 := by
      rw [abs_of_nonneg (div_nonneg hs.le (by linarith))]
      exact (div_le_one (by linarith)).2 (hs_one.trans hk)
    have hsum : ∑ o, |PB.gapS (fun x : Ψ × Fin N => T.lamS lam s x.1 x.2) (s / ((T.M B c).kA : ℝ)) o| ≤
        2 * (abelian₂ + l1 T.nu) + 1 := by
      have h1 := sum_abs_gapS_le (T.lamS lam s) (s / ((T.M B c).kA : ℝ))
      have h2 : l1 (T.lamS lam s) ≤ l1 lam + l1 T.nu := l1_sub_smul_le lam T.nu s hs.le hs_one
      linarith
    have hfin := hb _ hsum
    rw [← e1, ← e2] at hfin
    have hn : (1 : ℝ) ≤ (R.n c : ℝ) := by exact_mod_cast key.1
    have hC : C₃ c ≤ ∑ c, |C₃ c| :=
      (le_abs_self _).trans (Finset.single_le_sum (f := fun c => |C₃ c|) (fun _ _ => abs_nonneg _) (Finset.mem_univ c))
    set a := (T.M B c).arFun II (Real.exp (-(s ^ 2)⁻¹)) (linA (T.lamS lam s) s ^ (dimFl Ψ N + 1)) with ha
    set p := (T.M B c).PP II (linA (T.lamS lam s) s ^ (dimFl Ψ N + 1)) with hp
    have h3 : |a - p| ≤ (R.n c : ℝ) * |a - p| := le_mul_of_one_le_left (abs_nonneg _) hn
    have h4 : (R.n c : ℝ) * |a - p| = |(R.n c : ℝ) * a - (R.n c : ℝ) * p| := by
      rw [← mul_sub, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ (R.n c : ℝ))]
    have h5 : C₃ c * s ≤ (∑ c, |C₃ c|) * s := mul_le_mul_of_nonneg_right hC hs.le
    show |a - p| ≤ _
    linarith

end GlobalTheory.CompanionTheory.Ar.Top
