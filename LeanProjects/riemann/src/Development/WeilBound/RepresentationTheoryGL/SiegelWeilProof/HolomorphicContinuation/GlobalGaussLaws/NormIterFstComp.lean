import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.AwayFact
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.BoundMulTranslate
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSchwartzPolyMulGauss
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasDerivAtEvalCurveOfDerivation

noncomputable section

open Filter Topology MvPolynomial Set
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.Glob.SchDH

section general

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_iter_snd (q : ℝ × E) (l : ℕ) :
    ‖iteratedFDeriv ℝ l (fun q : ℝ × E => q.2) q‖ ≤ 1 + ‖q.2‖ := by
  have e : (fun q : ℝ × E => q.2) = ⇑(ContinuousLinearMap.snd ℝ ℝ E) := rfl
  rcases l with _ | l
  · rw [norm_iteratedFDeriv_zero]; linarith
  · rw [← norm_iteratedFDeriv_fderiv]
    have hf : fderiv ℝ (fun q : ℝ × E => q.2) = fun _ => ContinuousLinearMap.snd ℝ ℝ E := by
      funext y; rw [e]; exact (ContinuousLinearMap.snd ℝ ℝ E).fderiv
    rw [hf]
    rcases l with _ | l
    · rw [norm_iteratedFDeriv_zero]
      linarith [ContinuousLinearMap.norm_snd_le ℝ ℝ E, norm_nonneg q.2]
    · rw [iteratedFDeriv_const_of_ne (by omega)]
      simp only [Pi.zero_apply, norm_zero]
      positivity

theorem norm_iter_fst_comp {A : ℝ → E →L[ℝ] E} (hA : ContDiff ℝ ∞ A) (q : ℝ × E) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (fun q : ℝ × E => A q.1) q‖ ≤ ‖iteratedFDeriv ℝ j A q.1‖ := by
  have e : (fun q : ℝ × E => A q.1) = A ∘ ⇑(ContinuousLinearMap.fst ℝ ℝ E) := rfl
  rw [e, ContinuousLinearMap.iteratedFDeriv_comp_right _ hA _ (by exact_mod_cast le_top)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  refine mul_le_of_le_one_right (norm_nonneg _) ?_
  exact Finset.prod_le_one (fun _ _ => norm_nonneg _) fun _ _ => ContinuousLinearMap.norm_fst_le ℝ ℝ E

theorem bound_comp (φ : SchwartzMap E ℂ) (A : ℝ → E →L[ℝ] E) (hA : ContDiff ℝ ∞ A)
    (hinv : ∀ t y, A (-t) (A t y) = y) (k N : ℕ) :
    ∃ C, ∀ p : ℝ, ‖p - 0‖ ≤ 1 → ∀ x : E,
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ N (fun q : ℝ × E => φ (A q.1 q.2)) (p, x)‖ ≤ C := by
  obtain ⟨KA, hKA⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    (f := fun s => ∑ j ∈ Finset.range (N + 1), ‖iteratedFDeriv ℝ j A s‖)
    (continuous_finsetSum _ (fun j _ => (hA.continuous_iteratedFDeriv (by exact_mod_cast le_top)).norm)).continuousOn
  have hj : ∀ s ∈ Icc (-1 : ℝ) 1, ∀ j ≤ N, ‖iteratedFDeriv ℝ j A s‖ ≤ KA := by
    intro s hs j hjN
    have h1 := hKA s hs
    rw [Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)] at h1
    exact (Finset.single_le_sum (f := fun j => ‖iteratedFDeriv ℝ j A s‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_range.2 (Nat.lt_succ_of_le hjN))).trans h1
  have hKA0 : 0 ≤ KA := (norm_nonneg _).trans (hj 0 (by norm_num) 0 (Nat.zero_le _))
  have hAn : ∀ s ∈ Icc (-1 : ℝ) 1, ‖A s‖ ≤ KA := fun s hs => by
    have := hj s hs 0 (Nat.zero_le _); rwa [norm_iteratedFDeriv_zero] at this
  set f : ℝ × E → E := fun q => A q.1 q.2 with hfdef
  have hf : ContDiff ℝ ∞ f := (hA.comp contDiff_fst).clm_apply contDiff_snd
  have hDf : ∀ q : ℝ × E, q.1 ∈ Icc (-1 : ℝ) 1 → ∀ i ≤ N,
      ‖iteratedFDeriv ℝ i f q‖ ≤ 2 ^ i * KA * (1 + ‖q.2‖) := by
    intro q hq i hi
    have hb := (ContinuousLinearMap.id ℝ (E →L[ℝ] E)).norm_iteratedFDeriv_le_of_bilinear
      (f := fun q : ℝ × E => A q.1) (g := fun q : ℝ × E => q.2) (hA.comp contDiff_fst) contDiff_snd q
      (n := i) (by exact_mod_cast le_top)
    have e : (fun y : ℝ × E => (ContinuousLinearMap.id ℝ (E →L[ℝ] E)) (A y.1) y.2) = f := rfl
    rw [e] at hb
    refine hb.trans ?_
    have hterm : ∀ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * ‖iteratedFDeriv ℝ j (fun q : ℝ × E => A q.1) q‖ *
        ‖iteratedFDeriv ℝ (i - j) (fun q : ℝ × E => q.2) q‖ ≤ (i.choose j : ℝ) * (KA * (1 + ‖q.2‖)) := by
      intro j hjm
      have hjN : j ≤ N := (Nat.lt_succ_iff.1 (Finset.mem_range.1 hjm)).trans hi
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul ((norm_iter_fst_comp hA q j).trans (hj q.1 hq j hjN))
        (norm_iter_snd q _) (norm_nonneg _) hKA0) (by positivity)
    calc ‖ContinuousLinearMap.id ℝ (E →L[ℝ] E)‖ * ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) *
          ‖iteratedFDeriv ℝ j (fun q : ℝ × E => A q.1) q‖ * ‖iteratedFDeriv ℝ (i - j) (fun q : ℝ × E => q.2) q‖
        ≤ 1 * ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * (KA * (1 + ‖q.2‖)) :=
          mul_le_mul ContinuousLinearMap.norm_id_le (Finset.sum_le_sum hterm)
            (Finset.sum_nonneg fun j _ => by positivity) zero_le_one
      _ = 2 ^ i * KA * (1 + ‖q.2‖) := by
          rw [one_mul, ← Finset.sum_mul]
          have := Nat.sum_range_choose i
          have h2 : (∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ)) = 2 ^ i := by exact_mod_cast this
          rw [h2]; ring
  set S := 2 ^ (k + N) * ((Finset.Iic (k + N, N)).sup fun m => SchwartzMap.seminorm ℂ m.1 m.2) φ with hSdef
  have hS : ∀ y, ∀ i ≤ N, (1 + ‖y‖) ^ (k + N) * ‖iteratedFDeriv ℝ i φ y‖ ≤ S := fun y i hi =>
    SchwartzMap.one_add_le_sup_seminorm_apply (m := (k + N, N)) le_rfl hi φ y
  have hS0 : 0 ≤ S := le_trans (by positivity) (hS 0 0 (Nat.zero_le _))
  set KD := max 1 (2 ^ N * KA) with hKD
  set K' := max 1 KA with hK'
  have hKD1 : 1 ≤ KD := le_max_left _ _
  have hK'1 : 1 ≤ K' := le_max_left _ _
  refine ⟨N.factorial * S * KD ^ N * K' ^ (k + N), fun p hp x => ?_⟩
  have hp' : p ∈ Icc (-1 : ℝ) 1 := by
    rw [sub_zero, Real.norm_eq_abs] at hp; exact ⟨by linarith [neg_abs_le p], (le_abs_self p).trans hp⟩
  have hmp : -p ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [hp'.2], by linarith [hp'.1]⟩
  set y := f (p, x) with hy
  have hxy : ‖x‖ ≤ KA * ‖y‖ := by
    have e1 : x = A (-p) y := (hinv p x).symm
    calc ‖x‖ = ‖A (-p) y‖ := by rw [← e1]
      _ ≤ ‖A (-p)‖ * ‖y‖ := (A (-p)).le_opNorm y
      _ ≤ KA * ‖y‖ := by gcongr; exact hAn _ hmp
  have h1x : 1 + ‖x‖ ≤ K' * (1 + ‖y‖) := by
    have h2 : KA * ‖y‖ ≤ K' * ‖y‖ := by gcongr; exact le_max_right _ _
    nlinarith [norm_nonneg y]
  have hyp : 0 < (1 + ‖y‖) ^ (k + N) := by positivity
  have hC : ∀ i ≤ N, ‖iteratedFDeriv ℝ i φ (f (p, x))‖ ≤ S / (1 + ‖y‖) ^ (k + N) := by
    intro i hi
    rw [le_div_iff₀ hyp, mul_comm]
    exact hS y i hi
  have hD : ∀ i, 1 ≤ i → i ≤ N → ‖iteratedFDeriv ℝ i f (p, x)‖ ≤ (KD * (1 + ‖x‖)) ^ i := by
    intro i hi1 hiN
    have hb1 : 1 ≤ KD * (1 + ‖x‖) := by nlinarith [norm_nonneg x]
    refine (hDf (p, x) hp' i hiN).trans ?_
    have h3 : 2 ^ i * KA ≤ KD := by
      refine le_trans ?_ (le_max_right _ _)
      gcongr
      · norm_num
    calc 2 ^ i * KA * (1 + ‖(p, x).2‖) ≤ KD * (1 + ‖x‖) := by gcongr
      _ ≤ (KD * (1 + ‖x‖)) ^ i := le_self_pow₀ hb1 (by omega)
  have hcomp := norm_iteratedFDeriv_comp_le (g := ⇑φ) (f := f) (φ.smooth ⊤) hf (n := N)
    (by exact_mod_cast le_top) (p, x) hC hD
  have e2 : (fun q : ℝ × E => φ (A q.1 q.2)) = ⇑φ ∘ f := rfl
  rw [e2]
  have hxk : ‖x‖ ^ k ≤ (1 + ‖x‖) ^ k := by gcongr; linarith
  have hpow : (1 + ‖x‖) ^ (k + N) ≤ K' ^ (k + N) * (1 + ‖y‖) ^ (k + N) := by
    rw [← mul_pow]; gcongr
  calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ N (⇑φ ∘ f) (p, x)‖
      ≤ (1 + ‖x‖) ^ k * (N.factorial * (S / (1 + ‖y‖) ^ (k + N)) * (KD * (1 + ‖x‖)) ^ N) := by
        gcongr
    _ = N.factorial * S * KD ^ N * ((1 + ‖x‖) ^ (k + N) / (1 + ‖y‖) ^ (k + N)) := by
        rw [mul_pow, pow_add]; field_simp; ring
    _ ≤ N.factorial * S * KD ^ N * K' ^ (k + N) := by
        gcongr
        rw [div_le_iff₀ hyp]; exact hpow

end general

end PositivityTheory.Rg.Sw.Glob.SchDH
