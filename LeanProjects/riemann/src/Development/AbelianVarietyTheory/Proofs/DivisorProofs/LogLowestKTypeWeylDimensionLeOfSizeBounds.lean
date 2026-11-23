import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasAtOf
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open Formalism.MainNotions
open MeasureTheory Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Mult Formalism.BasicNotions.TH Formalism.L2.Theta

namespace GlobalTheory.OneMeasDim

theorem two_mul_card_pairs_le (p : ℕ) :
    2 * ∑ i : Fin p, (Finset.univ.filter (fun j : Fin p => i < j)).card ≤ p ^ 2 := by
  have e : ∑ i : Fin p, (Finset.univ.filter (fun j : Fin p => i < j)).card = ∑ i ∈ Finset.range p, i := by
    rw [← Finset.sum_range_reflect]
    rw [Fin.sum_univ_eq_sum_range (fun i => p - 1 - i) p |>.symm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.filter_lt_eq_Ioi, Fin.card_Ioi]
  rw [e, mul_comm, Finset.sum_range_id_mul_two]
  rw [sq]; exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)

theorem abs_factor_le (d : ℤ) (i j : ℕ) (hij : i < j) :
    |((((d : ℚ) + (j : ℚ) - (i : ℚ)) / ((j : ℚ) - (i : ℚ)) : ℚ) : ℝ)| ≤ 1 + |(d : ℝ)| := by
  have hs : (1 : ℝ) ≤ (j : ℝ) - (i : ℝ) := by
    have : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast hij
    linarith
  have hs0 : (0 : ℝ) < (j : ℝ) - (i : ℝ) := by linarith
  push_cast
  rw [abs_div, abs_of_pos hs0, div_le_iff₀ hs0]
  have h1 : |(d : ℝ) + (j : ℝ) - (i : ℝ)| ≤ |(d : ℝ)| + ((j : ℝ) - (i : ℝ)) := by
    have := abs_add_le (d : ℝ) ((j : ℝ) - (i : ℝ))
    rw [abs_of_pos hs0] at this
    rw [show (d : ℝ) + (j : ℝ) - (i : ℝ) = (d : ℝ) + ((j : ℝ) - (i : ℝ)) by ring]
    exact this
  nlinarith [abs_nonneg (d : ℝ)]

theorem abs_weylDimU_le {p : ℕ} (lam : Fin p → ℤ) (B : ℝ) (hB : ∀ a b, |((lam a - lam b : ℤ) : ℝ)| ≤ B) :
    |((Formalism.IndefR.Mult.weylDimU lam : ℚ) : ℝ)| ≤
      (1 + B) ^ (∑ i : Fin p, (Finset.univ.filter (fun j : Fin p => i < j)).card) := by
  unfold Formalism.IndefR.Mult.weylDimU
  rw [Rat.cast_prod, Finset.abs_prod, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun i _ => ?_
  rw [Rat.cast_prod, Finset.abs_prod, ← Finset.prod_const]
  refine Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun j hj => ?_
  have hij : (i : ℕ) < (j : ℕ) := (Finset.mem_filter.1 hj).2
  have := abs_factor_le (lam i - lam j) i j hij
  exact this.trans (by linarith [hB i j])

end GlobalTheory.OneMeasDim

namespace GlobalTheory.OneMeasDim

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem abs_wt_sub_le (D : D7) (i : Fin D.R.m) (τ : D.what₂.Tau) (a b : Fin ((Wc D i).sig (tauE D τ)).1 ⊕ Fin ((Wc D i).sig (tauE D τ)).2) :
    |((Formalism.L2.NTheta.wtOf D (Wc D i) τ a - Formalism.L2.NTheta.wtOf D (Wc D i) τ b : ℤ) : ℝ)| ≤ GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.wtSize D i := by
  have hw : 0 ≤ GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.wtSize D i :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  by_cases hab : a = b
  · subst hab; simpa using hw
  set c : ℝ := (((D.hc τ).e i : ℚ) : ℝ)
  set g : (Fin ((Wc D i).sig (tauE D τ)).1 ⊕ Fin ((Wc D i).sig (tauE D τ)).2) → ℝ :=
    fun x => |((Formalism.L2.NTheta.wtOf D (Wc D i) τ x : ℤ) : ℝ) + c| with hg
  have h1 : |((Formalism.L2.NTheta.wtOf D (Wc D i) τ a - Formalism.L2.NTheta.wtOf D (Wc D i) τ b : ℤ) : ℝ)| ≤ g a + g b := by
    rw [hg]; push_cast
    have := abs_sub (((Formalism.L2.NTheta.wtOf D (Wc D i) τ a : ℤ) : ℝ) + c) (((Formalism.L2.NTheta.wtOf D (Wc D i) τ b : ℤ) : ℝ) + c)
    rw [show (((Formalism.L2.NTheta.wtOf D (Wc D i) τ a : ℤ) : ℝ) + c) - (((Formalism.L2.NTheta.wtOf D (Wc D i) τ b : ℤ) : ℝ) + c) =
      ((Formalism.L2.NTheta.wtOf D (Wc D i) τ a : ℤ) : ℝ) - ((Formalism.L2.NTheta.wtOf D (Wc D i) τ b : ℤ) : ℝ) by ring] at this
    exact this
  have h2 : g a + g b ≤ ∑ x, g x := by
    rw [← Finset.sum_pair hab]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => abs_nonneg _
  have h3 : ∑ x, g x ≤ GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.wtSize D i := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.wtSize
    exact Finset.single_le_sum (f := fun τ' => ∑ x, |((Formalism.L2.NTheta.wtOf D (Wc D i) τ' x : ℤ) : ℝ) + (((D.hc τ').e i : ℚ) : ℝ)|)
      (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ τ)
  linarith

theorem log_dimAt_le : ∀ (D : D7) (i : Fin D.R.m) (L : ℝ) (hL : GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.Sizes D L) (τ : D.what₂.Tau),
    Real.log (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.dimAt D i τ) ≤ 3 / 2 * (D.R.r : ℝ) ^ 2 * L := by
  intro D i L hL τ
  obtain ⟨hf, hs, -, -⟩ := hL

  have hb2 : (2 : ℝ) ≤ Real.exp L := by
    have hr : 1 ≤ D.R.r := by
      have := D.R.two_le_m; have := D.R.m_add_three_le_k; unfold Formalism.BasicNotions.Ranks.r; omega
    have hfn : 2 ≤ D.R.f := by
      unfold Formalism.BasicNotions.Ranks.f Formalism.BasicNotions.Ranks.n; have := And.intro (Nat.one_le_two_pow (n := D.R.e)) (show 0 < D.R.ord by positivity); omega
    have hn : 1 ≤ D.R.nV := by unfold Formalism.BasicNotions.Ranks.nV; omega
    have : (2 : ℝ) ≤ (D.R.f : ℝ) * D.R.r * D.R.nV := by
      have : 2 ≤ D.R.f * D.R.r * D.R.nV := by
        calc 2 ≤ D.R.f := hfn
          _ = D.R.f * 1 * 1 := by ring
          _ ≤ D.R.f * D.R.r * D.R.nV := by gcongr
      exact_mod_cast this
    linarith
  have hL0 : 0 ≤ L := by
    by_contra h; push_neg at h
    have := Real.exp_lt_exp.2 h; rw [Real.exp_zero] at this; linarith
  set b := Real.exp L with hbdef
  set B := b ^ 2
  have h1B : 1 + B ≤ Real.exp (3 * L) := by
    rw [show 3 * L = L + L + L by ring, Real.exp_add, Real.exp_add, ← hbdef]
    nlinarith
  have hlog1B : Real.log (1 + B) ≤ 3 * L := by
    have := Real.log_le_log (by positivity) h1B
    rwa [Real.log_exp] at this

  set p := ((Wc D i).sig (tauE D τ)).1
  set q := ((Wc D i).sig (tauE D τ)).2
  have hpq : p + q = D.R.r := by
    have hr := D.sp.W_rank ((i:ℕ)+1) (by omega) (by have := i.2; omega)
    rw [← hr]; obtain ⟨e, -⟩ := (D.sp.W_sig ((i:ℕ)+1)) (tauE D τ); simpa using (Fintype.card_congr e).symm
  set κ := Formalism.L2.NTheta.wtOf D (Wc D i) τ
  have hent : ∀ a b, |((κ a - κ b : ℤ) : ℝ)| ≤ B := fun a b => (abs_wt_sub_le D i τ a b).trans (hs i)
  set N1 := ∑ a : Fin p, (Finset.univ.filter (fun j : Fin p => a < j)).card
  set N2 := ∑ a : Fin q, (Finset.univ.filter (fun j : Fin q => a < j)).card
  have w1 := abs_weylDimU_le (fun a => κ (Sum.inl a)) B (fun a b => hent _ _)
  have w2 := abs_weylDimU_le (fun a => κ (Sum.inr a)) B (fun a b => hent _ _)
  have hdim : GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.dimAt D i τ =
      ((Formalism.IndefR.Mult.weylDimU (fun a => κ (Sum.inl a)) : ℚ) : ℝ) *
        ((Formalism.IndefR.Mult.weylDimU (fun a => κ (Sum.inr a)) : ℚ) : ℝ) := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.dimAt Formalism.IndefR.Mult.dimK; push_cast; rfl
  have habs : |GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.dimAt D i τ| ≤ (1 + B) ^ (N1 + N2) := by
    rw [hdim, abs_mul, pow_add]
    exact mul_le_mul w1 w2 (abs_nonneg _) (by positivity)
  have hlog : Real.log (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.dimAt D i τ) ≤ ((N1 + N2 : ℕ) : ℝ) * Real.log (1 + B) := by
    rw [← Real.log_abs]
    rcases eq_or_ne (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.dimAt D i τ) 0 with h0 | h0
    · rw [h0, abs_zero, Real.log_zero]
      have hB0 : (0 : ℝ) ≤ B := sq_nonneg b
      exact mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by linarith))
    · have := Real.log_le_log (abs_pos.2 h0) habs
      rwa [Real.log_pow] at this
  have hN : 2 * (N1 + N2) ≤ D.R.r ^ 2 := by
    have a1 : 2 * N1 ≤ p ^ 2 := two_mul_card_pairs_le p
    have a2 : 2 * N2 ≤ q ^ 2 := two_mul_card_pairs_le q
    have a3 : p ^ 2 + q ^ 2 ≤ (p + q) ^ 2 := by ring_nf; omega
    rw [← hpq]; omega
  have hN' : 2 * ((N1 + N2 : ℕ) : ℝ) ≤ (D.R.r : ℝ) ^ 2 := by exact_mod_cast hN
  have hN0 : (0 : ℝ) ≤ ((N1 + N2 : ℕ) : ℝ) := Nat.cast_nonneg _
  calc Real.log (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.dimAt D i τ) ≤ ((N1 + N2 : ℕ) : ℝ) * Real.log (1 + B) := hlog
    _ ≤ ((N1 + N2 : ℕ) : ℝ) * (3 * L) := mul_le_mul_of_nonneg_left hlog1B hN0
    _ = 3 / 2 * (2 * ((N1 + N2 : ℕ) : ℝ)) * L := by ring
    _ ≤ 3 / 2 * (D.R.r : ℝ) ^ 2 * L := by gcongr

end GlobalTheory.OneMeasDim
