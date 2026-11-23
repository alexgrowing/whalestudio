import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.AnalyticSeries.NeZeroOne
import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.OrderAsym

noncomputable section

open scoped ComplexConjugate

namespace UpperTheory.ConvolutionTheory.R.Ac2

open PositivityTheory.RgJS UpperTheory.ConvolutionTheory.Rs

theorem ps {ι M : Type} [Fintype ι] [AddCommMonoid M] {d : ι → ℕ} {m : ℕ} {g : ∀ i, Fin (d i) → ℂ} {h : Fin m → ℂ}
    (e : ∑ i, Finset.univ.val.map (g i) = Finset.univ.val.map h) (φ : ℂ → M) : ∑ i, ∑ a, φ (g i a) = ∑ a, φ (h a) := by
  have := congrArg (Multiset.sumAddMonoidHom.comp (Multiset.mapAddMonoidHom φ)) e
  rw [map_sum] at this
  have e1 : ∀ {n : ℕ} (k : Fin n → ℂ), (Multiset.sumAddMonoidHom.comp (Multiset.mapAddMonoidHom φ)) (Finset.univ.val.map k) =
      ∑ a, φ (k a) := fun k => congrArg Multiset.sum (Multiset.map_map φ k Finset.univ.val)
  simpa only [e1] using this

theorem logsum {m : ℕ} {a : Fin m → ℂ} (h : ‖∏ i, a i‖ = 1) (q f : ℕ) (hq : 2 ≤ q) (t : ℝ) :
    ∑ i, Real.log ‖(a i * (q : ℂ) ^ (-(t : ℂ))) ^ f‖ = f * m * (-t * Real.log q) := by
  have h0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hne : ∀ i, ‖a i‖ ≠ 0 := fun i hi => by
    rw [norm_prod, Finset.prod_eq_zero (Finset.mem_univ i) hi] at h
    exact zero_ne_one h
  have hs : ∑ i, Real.log ‖a i‖ = 0 := by
    rw [← Real.log_prod fun i _ => hne i, ← norm_prod, h, Real.log_one]
  have e : ∀ i, Real.log ‖(a i * (q : ℂ) ^ (-(t : ℂ))) ^ f‖ = f * (Real.log ‖a i‖ + -t * Real.log q) := fun i => by
    rw [norm_pow, Real.log_pow, norm_mul, Common0Aux.cpow_real, Complex.norm_real,
      Real.norm_of_nonneg (Real.rpow_pos_of_pos h0 _).le, Real.log_mul (hne i) (Real.rpow_pos_of_pos h0 _).ne',
      Real.log_rpow h0]
  simp only [e, ← Finset.mul_sum, Finset.sum_add_distrib, hs, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  ring

theorem shift (q : ℕ) (hq : 2 ≤ q) (s t : ℝ) :
    (q : ℂ) ^ (-(s : ℂ)) * (q : ℂ) ^ (-((-t : ℝ) : ℂ)) = (q : ℂ) ^ (-((s - t : ℝ) : ℂ)) := by
  rw [← Complex.cpow_add _ _ (by exact_mod_cast (by omega : q ≠ 0))]
  congr 1
  push_cast
  ring

theorem cancel (q f : ℕ) (hq : 2 ≤ q) (t : ℝ) :
    ((q : ℂ) ^ (-(t : ℂ))) ^ f * ((q ^ f : ℕ) : ℂ) ^ (-((-t : ℝ) : ℂ)) = 1 := by
  have h0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  rw [Common0Aux.cpow_real, Common0Aux.cpow_real, ← Complex.ofReal_pow, ← Complex.ofReal_mul, Nat.cast_pow,
    ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul h0.le, ← Real.rpow_mul h0.le, ← Real.rpow_add h0]
  simp [mul_comm]

theorem eq_of_bdd (N N' : ℕ) (C : ℝ) (h : ∀ σ : ℝ, 1 < σ → σ ≤ 2 → |((N : ℝ) - N') * (-Real.log (σ - 1))| ≤ C) : N = N' := by
  have hC : 0 ≤ C := (abs_nonneg _).trans (h 2 one_lt_two le_rfl)
  have h1 := h (1 + Real.exp (-(C + 1))) (by linarith [Real.exp_pos (-(C + 1))])
    (by linarith [Real.exp_le_one_iff.2 (show -(C + 1) ≤ 0 by linarith)])
  rw [add_sub_cancel_left, Real.log_exp, neg_neg, abs_mul, abs_of_nonneg (show 0 ≤ C + 1 by linarith)] at h1
  by_contra hne
  have h2 : (1 : ℤ) ≤ |(N : ℤ) - N'| := Int.one_le_abs (by omega)
  have h3 : (1 : ℝ) ≤ |(N : ℝ) - N'| := by exact_mod_cast h2
  nlinarith

theorem sum_bd {I : Type} (s : Finset I) (P : I → Prop) [DecidablePred P] (a M : I → ℝ) (L : ℝ)
    (h : ∀ i, |a i - (if P i then L else 0)| ≤ M i) : |∑ i ∈ s, a i - (s.filter P).card * L| ≤ ∑ i ∈ s, M i := by
  have e : ((s.filter P).card : ℝ) * L = ∑ i ∈ s, if P i then L else 0 := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  rw [e, ← Finset.sum_sub_distrib]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => h i)

end UpperTheory.ConvolutionTheory.R.Ac2

namespace UpperTheory.ConvolutionTheory.R

open PositivityTheory.RgJS UpperTheory.ConvolutionTheory.Rs Ac2

theorem absCount2 : BCSum → ZeroExp → LogAsym → AbsCount := by
  intro hB hZ hL l W W' q q' u f c hl hC X X' d d' A A' hS hS' ι _ x y z t t' hy h1 h2
  classical
  have hq := hS.primes.two
  have hq' := hS'.primes.two
  have hq1 : ∀ v, 1 ≤ q v := fun v => le_trans one_le_two (hq v)
  obtain ⟨w₀⟩ : Nonempty W' := by
    by_contra hn
    have := not_nonempty_iff.1 hn
    exact hS'.primes.div Summable.of_finite
  have key : ∀ (x : X) (t : ℝ), (∀ w, ∑ i, Finset.univ.val.map (fun a => A' (z i).1 w a * (q' w : ℂ) ^ (-((z i).2 : ℂ))) =
      Finset.univ.val.map fun a => (A x (u w) a * (q (u w) : ℂ) ^ (-(t : ℂ))) ^ f w) →
      ∑ i, (d' (z i).1 : ℝ) = d x ∧ ∑ i, (d' (z i).1 : ℝ) * (z i).2 = d x * t ∧ ∀ w (k : ℕ),
        ∑ a : Σ i, Fin (d' (z i).1), (A' (z a.1).1 w a.2 * (q' w : ℂ) ^ (-(((z a.1).2 - t : ℝ) : ℂ))) ^ k =
          ∑ a, A x (u w) a ^ (f w * k) := fun x t h => by
    refine ⟨by simpa using ps (h w₀) fun _ => (1 : ℝ), ?_, fun w k => ?_⟩
    · have e := ps (h w₀) fun ζ => Real.log ‖ζ‖
      rw [logsum (hS.det x _) _ _ (hq _)] at e
      have e' : ∀ i, ∑ a, Real.log ‖A' (z i).1 w₀ a * (q' w₀ : ℂ) ^ (-((z i).2 : ℂ))‖ =
          -Real.log (q' w₀) * ((d' (z i).1 : ℝ) * (z i).2) := fun i => by
        have := logsum (hS'.det (z i).1 w₀) _ 1 (hq' w₀) (z i).2
        simp only [pow_one] at this
        rw [this]
        push_cast
        ring
      have hlog : Real.log (q' w₀) = f w₀ * Real.log (q (u w₀)) := by rw [hC.norm, Nat.cast_pow, Real.log_pow]
      have hpos : 0 < Real.log (q' w₀) := Real.log_pos (by exact_mod_cast hq' w₀)
      simp only [e', ← Finset.mul_sum] at e
      refine mul_left_cancel₀ (neg_ne_zero.2 hpos.ne') (e.trans ?_)
      rw [hlog]
      ring
    · have e := ps (h w) fun ζ => (ζ * (q' w : ℂ) ^ (-((-t : ℝ) : ℂ))) ^ k
      rw [Fintype.sum_sigma]
      simp only [mul_assoc, shift _ (hq' w)] at e
      rw [e]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [mul_pow (A x (u w) a), mul_assoc, hC.norm w, cancel _ _ (hq _), mul_one, pow_mul]
  obtain ⟨c1, s1, p1⟩ := key x t h1
  obtain ⟨c2, s2, p2⟩ := key (y 0) t' h2
  have htt : t = t' := by
    have hd : (0 : ℝ) < d x := by exact_mod_cast hS.pos x
    refine mul_left_cancel₀ hd.ne' ?_
    rw [← s1, s2, ← c2, c1]
  subst htt
  have hs : ∀ i, (z i).2 = t := fun i => sub_eq_zero.1 (hZ W' q' X' d' A' hS' ι (fun i => ((z i).1, (z i).2 - t))
    (by simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, c1, s1, sub_self])
    (fun σ hσ => (hB l W W' q q' u f c hl hq1 hC _ _ _ _ (A x) (A x) _ _ σ p1 p1 ((conv1 W q X d A hS x x).1 σ hσ)).1) i)
  refine ⟨rfl, hs, ?_⟩
  simp only [hs, sub_self, Complex.ofReal_zero, neg_zero, Complex.cpow_zero, mul_one] at p1 p2
  choose M hM using fun j => hL W q X d A hS x (y j)
  choose M' hM' using fun p : ι × ι => hL W' q' X' d' A' hS' (z p.1).1 (z p.2).1
  refine eq_of_bdd _ _ (∑ j ∈ Finset.range l, M j + ∑ p, M' p) fun σ a b => ?_
  have e := (hB l W W' q q' u f c hl hq1 hC _ _ _ _ (A x) (A (y 0)) _ _ σ p1 p2 ((conv1 W q X d A hS x (y 0)).1 σ a)).2
  have eR : ∀ j p, lterm q (A x) (fun v b => A (y 0) v b * c v ^ j) σ p = lterm q (A x) (A (y j)) σ p := fun j p => by
    have := congrArg (fun m : Multiset ℂ => (m.map (· ^ (p.2 + 1))).sum) (hy j p.1)
    simp only [Multiset.map_map, Function.comp_def, ← Finset.sum_eq_multiset_sum] at this
    simp only [lterm, this]
  have eL : ∀ p, lterm q' (fun w (a : Σ i, Fin (d' (z i).1)) => A' (z a.1).1 w a.2)
      (fun w (a : Σ i, Fin (d' (z i).1)) => A' (z a.1).1 w a.2) σ p =
        ∑ r : ι × ι, lterm q' (A' (z r.1).1) (A' (z r.2).1) σ p := fun p => by
    simp only [lterm, Fintype.sum_sigma, Fintype.sum_prod_type]
    rw [map_sum, Finset.sum_mul_sum]
    simp only [Finset.sum_mul, Finset.sum_div]
  simp only [eR, eL] at e
  rw [Summable.tsum_finsetSum fun r _ => ((conv1 W' q' X' d' A' hS' _ _).1 σ a).of_norm] at e
  have e2 : ∑ r : ι × ι, dre q' (A' (z r.1).1) (A' (z r.2).1) σ = ∑ j ∈ Finset.range l, dre q (A x) (A (y j)) σ := by
    simpa only [Complex.re_sum, dre] using congrArg Complex.re e
  have b1 := abs_le.1 (sum_bd (Finset.range l) (fun j => x = y j) _ M _ fun j => by convert hM j σ a b)
  have b2 := abs_le.1 (sum_bd Finset.univ (fun p : ι × ι => (z p.1).1 = (z p.2).1) _ M' _ fun p => by convert hM' p σ a b)
  rw [e2] at b2
  rw [sub_mul]
  exact abs_le.2 ⟨by linarith [b1.1, b1.2, b2.1, b2.2], by linarith [b1.1, b1.2, b2.1, b2.2]⟩

end UpperTheory.ConvolutionTheory.R
