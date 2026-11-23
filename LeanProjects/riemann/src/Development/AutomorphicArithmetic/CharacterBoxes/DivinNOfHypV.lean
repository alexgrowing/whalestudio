import Formalism.SharpRestriction.GlobalTheoremInputs
import Development.AutomorphicArithmetic.CharacterBoxes.ExistsPageN

noncomputable section

namespace UpperTheory.Top

open Formalism.BasicNotions Formalism.MainNotions

def HypV {eps : ℝ} (Fm : FamCore eps) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, VVle (Fm.D x i).host.E (Fm.D x i).R.t (Real.sqrt (Fm.L x i).sc.b)

def FamilyClassConnected (ℰ : FamClass) : Prop :=
  ∃ eD eL ε₁ : ℝ, 0 < ε₁ ∧ ∀ eps : ℝ, 0 < eps → eps < ε₁ →
    ∃ Fm : FamP eps, ℰ Fm ∧ ∃ K cHH eK CL x0 : ℝ, ∀ x ≥ x0, x ∈ Fm.Win → ChainTied Fm eD eL K cHH eK CL x

theorem vvRecord (D : D7) (B : ℝ) (h : VVle D.host.E D.R.t B) :
    ShaFinOdd D ∧ Summable (vvTerm D) ∧ ∑' l, vvTerm D l ≤ B := by
  letI := D.nd.instOm
  letI := D.nd.algOm
  haveI := D.nd.acOm
  obtain ⟨h1, h2⟩ := h D.nd.Om D.nd.ldat
  have key : ∀ (p : ℕ) [Fact p.Prime], ((∑ e ∈ Finset.Ico 1 D.R.t, D.what₂.shaLen p e : ℚ) : ℝ) =
      ∑ e ∈ Finset.Ico 1 D.R.t, ((Formalism.GaloisCohomology.shaLen (D.nd.ldat p) (e : ℤ)).toNat : ℝ) := by
    intro p _
    push_cast
    refine Finset.sum_congr rfl fun e he => ?_
    obtain ⟨a, b⟩ := Finset.mem_Ico.1 he
    rw [D.nd.sha_eq p e a b _ (ENat.coe_toNat (h1 p e a b)).symm]
    norm_cast
  have bd : ∀ l : ℕ, 0 ≤ vvTerm D l ∧ ∀ hl : l.Prime, vvTerm D l ≤ Real.log l *
      ∑ e ∈ Finset.Ico 1 D.R.t, ((@Formalism.GaloisCohomology.shaLen _ D.nd.Om _ _ _ _ _ l ⟨hl⟩ (@Formalism.BasicNotions.NData.ldat _ _ _ D.nd l ⟨hl⟩) (e : ℤ)).toNat : ℝ) := by
    intro l
    by_cases hl : l.Prime
    · haveI : Fact l.Prime := ⟨hl⟩
      have hk := key l
      have hn : 0 ≤ Real.log l * ∑ e ∈ Finset.Ico 1 D.R.t, ((Formalism.GaloisCohomology.shaLen (D.nd.ldat l) (e : ℤ)).toNat : ℝ) :=
        mul_nonneg (Real.log_natCast_nonneg _) (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _)
      unfold vvTerm
      split_ifs
      all_goals first
        | exact ⟨le_rfl, fun _ => hn⟩
        | (rw [hk, mul_comm]; exact ⟨hn, fun _ => le_rfl⟩)
    · have : vvTerm D l = 0 := by unfold vvTerm; simp [hl]
      exact ⟨this.ge, fun h => absurd h hl⟩
  have part : ∀ s : Finset ℕ, ∑ l ∈ s, vvTerm D l ≤ B := by
    intro s
    classical
    refine le_trans ?_ (h2 (s.subtype Nat.Prime))
    rw [← Finset.sum_filter_of_ne (p := Nat.Prime) (fun l _ hne => by
      by_contra hl
      exact hne (by unfold vvTerm; simp [hl])), ← Finset.sum_subtype_eq_sum_filter]
    exact Finset.sum_le_sum fun l _ => (bd l).2 l.2
  refine ⟨?_, summable_of_sum_le (fun l => (bd l).1) part, Real.tsum_le_of_sum_le (fun l => (bd l).1) part⟩
  intro p _ e
  intros
  exact h1 p e ‹_› ‹_›

theorem log_sq_le_rpow {eps : ℝ} (h : 0 < eps) :
    ∃ x0 : ℝ, ∀ x ≥ x0, Real.log x ^ 2 ≤ x ^ eps := by
  have h1 := (isLittleO_log_rpow_atTop (half_pos h)).bound one_pos
  obtain ⟨x0, hx0⟩ := Filter.eventually_atTop.1 h1
  refine ⟨max x0 1, fun x hx => ?_⟩
  have hx1 : 1 ≤ x := le_trans (le_max_right _ _) hx
  have h2 := hx0 x (le_trans (le_max_left _ _) hx)
  have hp : 0 ≤ x ^ (eps / 2) := Real.rpow_nonneg (by linarith) _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hx1), abs_of_nonneg hp,
    one_mul] at h2
  have h3 : x ^ eps = (x ^ (eps / 2)) ^ 2 := by
    rw [sq, ← Real.rpow_add (by linarith)]
    congr 1
    ring
  rw [h3]
  exact pow_le_pow_left₀ (Real.log_nonneg hx1) h2 2

theorem divinN_at {D : D7} (L : SizeData₂ D) (j : ℕ) (C : ℝ) (hj : j ∈ SizeData₂.lifts D)
    (hN : LinkN_at L j C) (hs : Summable (vvTerm D)) (hb : ∑' l, vvTerm D l ≤ L.sc.b)
    (hd : L.dZ0 j = D.what₂.D0) (hlog : Real.log L.sc.x ^ 2 ≤ L.sc.x ^ L.sc.eps) :
    DIVinN_at L j (|C| + 1) := by
  have hx : 0 < L.sc.x := lt_trans one_pos L.sc.one_lt_alt
  have hy : 1 ≤ L.sc.x ^ L.sc.eps := Real.one_le_rpow L.sc.one_lt_alt.le L.sc.eps_pos.le
  have hf : (1 : ℝ) ≤ D.R.f := by
    have : 0 < D.R.f := by unfold Ranks.f Ranks.n; positivity
    exact_mod_cast this
  have hm : (1 : ℝ) ≤ D.R.m := by
    have h := Finset.mem_Icc.1 hj
    exact_mod_cast le_trans h.1 h.2
  have hbpos : 0 < L.sc.b := Real.exp_pos _
  have hNc : 0 ≤ L.Nc := by
    simp only [SizeData₂.Nc, budgetNc, rankBudget, bSize]
    positivity
  have hB : L.B0 = (D.R.f : ℝ) * D.R.m * L.sc.b * L.sc.x ^ L.sc.eps := rfl
  have hL : L.sc.L = L.sc.x ^ L.sc.eps := rfl
  have hE := hN hs
  rw [hd, hL] at hE
  unfold DIVinN_at
  refine le_trans hE (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))
  set y := L.sc.x ^ L.sc.eps with hydef
  have hfm : 1 ≤ (D.R.f : ℝ) * D.R.m := one_le_mul_of_one_le_of_one_le hf hm
  have hbB : L.sc.b ≤ L.B0 := by
    rw [hB]
    have h1 : 1 ≤ (D.R.f : ℝ) * D.R.m * y := one_le_mul_of_one_le_of_one_le hfm hy
    nlinarith
  have hB0 : 0 ≤ L.B0 := le_trans hbpos.le hbB
  have hP1 : (D.R.f : ℝ) * D.R.m * L.sc.b * y ^ 2 = y * L.B0 := by rw [hB]; ring
  have hP2 : Real.log L.sc.x ^ 2 * L.Nc ≤ y * L.Nc := mul_le_mul_of_nonneg_right hlog hNc
  have hP0 : 0 ≤ y * L.B0 + Real.log L.sc.x ^ 2 * L.Nc := by positivity
  rw [hP1]
  have h1 : C * (y * L.B0 + Real.log L.sc.x ^ 2 * L.Nc) ≤ |C| * (y * (L.B0 + L.Nc)) :=
    le_trans (mul_le_mul_of_nonneg_right (le_abs_self C) hP0)
      (mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg C))
  have h2 : L.B0 ≤ y * (L.B0 + L.Nc) := by nlinarith
  have h3 : (|C| + 1) * y * (L.B0 + L.Nc) = |C| * (y * (L.B0 + L.Nc)) + y * (L.B0 + L.Nc) := by ring
  rw [h3]
  linarith

theorem divinN_of_hypV {eps : ℝ} (Fm : FamP eps) (heps : 0 < eps) (hV : HypV Fm.toFamCore) (hN : LinkN Fm) (hR : SmallLevelRankEq Fm) :
    DIVinN Fm := by
  obtain ⟨x1, h1⟩ := hV
  obtain ⟨C, x3, h3⟩ := hN
  obtain ⟨x4, h4⟩ := hR
  obtain ⟨x6, h6⟩ := log_sq_le_rpow heps
  refine ⟨|C| + 1, max (max x1 (max x3 x4)) (max x6 (Fm.x1 + 1)), fun x hx i j hj => ?_⟩
  simp only [ge_iff_le, max_le_iff] at hx
  obtain ⟨⟨g1, g3, g4⟩, g6, g7⟩ := hx
  obtain ⟨hf, hs, hle⟩ := vvRecord _ _ (h1 x g1 i)
  have hb : 1 ≤ (Fm.L x i).sc.b := Real.one_le_exp (Real.rpow_nonneg (by linarith [(Fm.L x i).sc.one_lt_alt]) _)
  refine divinN_at _ j C hj (h3 x g3 i hf j hj) hs (hle.trans (Real.sqrt_le_self_iff.2 (Or.inr hb))) (h4 x g4 i j hj) ?_
  rw [Fm.L_x x i (by linarith), Fm.L_eps x i]
  exact h6 x g6

end UpperTheory.Top

end
