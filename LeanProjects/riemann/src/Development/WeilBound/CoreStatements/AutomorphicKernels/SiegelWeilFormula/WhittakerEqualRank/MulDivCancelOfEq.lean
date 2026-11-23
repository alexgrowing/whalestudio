import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerEqualRank.LamTendsto

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.Gen.WQ

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory GlobalTheory.Cont PositivityTheory.PfSWUS.Loc PositivityTheory.Rg.Sw Filter PositivityTheory.SiegelWeilFormula.Gen.W
open scoped TensorProduct Matrix Topology Classical

theorem pow_sub_of_sq (c : ℂ) (hc : c ^ 2 = 1) (N i : ℕ) (hi : i ≤ N) :
    c ^ (N + i) = c ^ (((N - i : ℕ) : ℤ)) := by
  rw [zpow_natCast]
  have : N + i = (N - i) + 2 * i := by omega
  rw [this, pow_add, pow_mul, hc, one_pow, mul_one]

theorem mul_div_cancel_of_eq (x y D : ℂ) (hD : D ≠ 0) (hy : y = D) : x * y / D = x := by
  subst hy; field_simp

theorem unrX_zero_split (m : ℕ) (c : ℂ) (hc : c ^ 2 = 1) (q : ℕ) (hne : 1 - c / q ≠ 0) :
    unrX (m + 1) (m + 1) c q 0 / (1 - c / q) =
      ∏ i : Fin m, (1 - c ^ (((m + 1 - (i : ℕ) : ℕ)) : ℤ) * (q : ℂ) ^ (-(((m + 1 - (i : ℕ) : ℕ)) : ℂ))) := by
  unfold unrX
  rw [Fin.prod_univ_castSucc, mul_div_cancel_of_eq _ _ _ hne]
  · refine Finset.prod_congr rfl fun i _ => ?_
    simp only [Fin.val_castSucc]
    rw [pow_sub_of_sq c hc (m + 1) i (by omega)]
    congr 3
    rw [Nat.cast_sub (by omega : (i : ℕ) ≤ m + 1)]
    push_cast
    ring
  · simp only [Fin.val_last]
    rw [pow_sub_of_sq c hc (m + 1) m (by omega)]
    have h1 : m + 1 - m = 1 := by omega
    rw [h1]
    push_cast
    rw [show -(2 * (0 : ℂ) + (m + 1) - m) = -1 by ring, Complex.cpow_neg_one, zpow_one, div_eq_mul_inv]

theorem lpack (hLO : LOrd) {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) (S : Finset (HeightOneSpectrum (𝓞 F))) (N : ℕ) (hN : 1 ≤ N) :
    ∃ K : ℂ → ℂ, MeromorphicOn K Set.univ ∧ AnalyticAt ℂ K 0 ∧
      (∀ z : ℂ, 0 < z.re →
        HasProd (fun v : {v // v ∉ S} => unrX N N (eSp E v.1) (Ideal.absNorm v.1.asIdeal) z) (K z)) ∧
      ∃ lam P : ℂ,
        Tendsto (fun s : ℝ => ∏' v : HeightOneSpectrum (𝓞 F),
          (1 - eSp E v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s : ℂ)))) (𝓝[>] 1) (𝓝 lam) ∧
        HasProd (fun v : {v // v ∉ S} => unrX N N (eSp E v.1) (Ideal.absNorm v.1.asIdeal) 0 /
          (1 - eSp E v.1 / (Ideal.absNorm v.1.asIdeal : ℂ))) P ∧
        K 0 * ∏ v ∈ S, (1 - eSp E v / (Ideal.absNorm v.asIdeal : ℂ)) = lam * P := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
  choose Z hZm hZp H hHa hHe using fun i : Fin (m + 1) => hLO F E σ hcm S (((m + 1 - i : ℕ)) : ℤ)
  have hj1 : ∀ i : Fin (m + 1), 1 ≤ m + 1 - (i : ℕ) := fun i => by omega
  have hHe' : ∀ i : Fin (m + 1), ∀ᶠ s in 𝓝[≠] (((m + 1 - i : ℕ) : ℂ)), H i s = Z i s := by
    intro i
    have h := hHe i
    rw [if_pos (by exact_mod_cast hj1 i)] at h
    simpa only [pow_zero, one_mul, Int.cast_natCast] using h
  have hHa' : ∀ i : Fin (m + 1), AnalyticAt ℂ (H i) ((m + 1 - i : ℕ) : ℂ) := fun i => by
    simpa only [Int.cast_natCast] using hHa i
  obtain ⟨Zc, hZc⟩ : ∃ Zc : Fin (m + 1) → ℂ → ℂ,
      Zc = fun i => Function.update (Z i) ((m + 1 - i : ℕ) : ℂ) (H i ((m + 1 - i : ℕ) : ℂ)) := ⟨_, rfl⟩
  have hfix : ∀ i : Fin (m + 1), MeromorphicOn (Zc i) Set.univ ∧ AnalyticAt ℂ (Zc i) ((m + 1 - i : ℕ) : ℂ) ∧
      Zc i ((m + 1 - i : ℕ) : ℂ) = H i ((m + 1 - i : ℕ) : ℂ) ∧
      ∀ s, s ≠ ((m + 1 - i : ℕ) : ℂ) → Zc i s = Z i s := fun i => by
    subst hZc
    exact fix_point (Z i) (H i) _ (hZm i) (hHa' i) (hHe' i)
  have h0 : ∀ i : Fin (m + 1), (2 * (0 : ℂ) + ((m + 1 : ℕ) : ℂ) - (i : ℕ)) = ((m + 1 - i : ℕ) : ℂ) := fun i => by
    rw [Nat.cast_sub (by omega : (i : ℕ) ≤ m + 1)]
    ring
  have hqne : ∀ v : HeightOneSpectrum (𝓞 F), (Ideal.absNorm v.asIdeal : ℂ) ≠ 0 := fun v => by
    have := NumberField.HeightOneSpectrum.one_lt_absNorm v
    exact_mod_cast (by omega : Ideal.absNorm v.asIdeal ≠ 0)
  have hnc : ∀ (v : HeightOneSpectrum (𝓞 F)) (k : ℤ), ‖eSp E v ^ k‖ ≤ 1 := fun v k => by
    rw [norm_zpow, norm_eSp, one_zpow]
  refine ⟨fun z => ∏ i : Fin (m + 1), Zc i (2 * z + ((m + 1 : ℕ) : ℂ) - (i : ℕ)), ?_, ?_, ?_, ?_⟩
  · intro z _
    exact MeromorphicAt.fun_prod fun i _ => ((hfix i).1 _ trivial).comp_analyticAt
      (g := fun z : ℂ => 2 * z + ((m + 1 : ℕ) : ℂ) - (i : ℕ)) (by fun_prop)
  · refine (Finset.analyticAt_prod (Finset.univ : Finset (Fin (m + 1))) fun i _ =>
      AnalyticAt.comp_of_eq (hfix i).2.1
      (f := fun z : ℂ => 2 * z + ((m + 1 : ℕ) : ℂ) - (i : ℕ)) (by fun_prop) (h0 i)).congr
      (Filter.Eventually.of_forall fun z => ?_)
    simp [Finset.prod_apply]
  · intro z hz
    unfold unrX
    refine hasProd_prod fun i _ => ?_
    have hi : (i : ℝ) + 1 ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast i.2
    have hre : 1 < (2 * z + ((m + 1 : ℕ) : ℂ) - (i : ℕ)).re := by
      simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.natCast_re,
        Complex.re_ofNat, Complex.im_ofNat]
      push_cast at hi ⊢
      nlinarith
    have hne : 2 * z + ((m + 1 : ℕ) : ℂ) - (i : ℕ) ≠ ((m + 1 - i : ℕ) : ℂ) := by
      intro h
      have h' := congrArg Complex.re h
      rw [Nat.cast_sub (by omega : (i : ℕ) ≤ m + 1)] at h'
      simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.natCast_re,
        Complex.re_ofNat, Complex.im_ofNat] at h'
      push_cast at h'
      nlinarith
    rw [(hfix i).2.2.2 _ hne]
    convert hZp i _ hre using 2 with v
    rw [pow_sub_of_sq _ (eSp_sq v.1) (m + 1) i (by omega)]
  ·
    have hlj : ((m + 1 - ((Fin.last m : Fin (m + 1)) : ℕ) : ℕ) : ℂ) = 1 := by simp
    have hZl : ∀ s : ℂ, 1 < s.re → HasProd (fun v : {v // v ∉ S} =>
        1 - eSp E v.1 * (Ideal.absNorm v.1.asIdeal : ℂ) ^ (-s)) (Z (Fin.last m) s) := fun s hs => by
      convert hZp (Fin.last m) s hs using 2 with v
      simp
    have hHl : AnalyticAt ℂ (H (Fin.last m)) 1 := hlj ▸ hHa' (Fin.last m)
    have hEl : ∀ᶠ s in 𝓝[≠] (1 : ℂ), H (Fin.last m) s = Z (Fin.last m) s := hlj ▸ hHe' (Fin.last m)
    refine ⟨(∏ v ∈ S, (1 - eSp E v / (Ideal.absNorm v.asIdeal : ℂ))) * H (Fin.last m) 1,
      ∏ i : Fin m, Z i.castSucc ((m + 1 - i : ℕ) : ℂ), lam_tendsto S _ _ hZl hHl hEl, ?_, ?_⟩
    · have hfun : (fun v : {v // v ∉ S} => unrX (m + 1) (m + 1) (eSp E v.1) (Ideal.absNorm v.1.asIdeal) 0 /
          (1 - eSp E v.1 / (Ideal.absNorm v.1.asIdeal : ℂ))) = fun v => ∏ i : Fin m,
            (1 - eSp E v.1 ^ (((m + 1 - (i : ℕ) : ℕ)) : ℤ) *
              (Ideal.absNorm v.1.asIdeal : ℂ) ^ (-(((m + 1 - (i : ℕ) : ℕ)) : ℂ))) := by
        funext v
        exact unrX_zero_split m _ (eSp_sq v.1) _ (one_sub_eSp_ne v.1)
      rw [hfun]
      refine hasProd_prod fun i _ => ?_
      have hre : 1 < (((m + 1 - (i : ℕ) : ℕ)) : ℂ).re := by
        rw [Complex.natCast_re]
        have : 2 ≤ m + 1 - (i : ℕ) := by omega
        exact_mod_cast this
      exact hZp i.castSucc _ hre
    · show (∏ i : Fin (m + 1), Zc i (2 * 0 + ((m + 1 : ℕ) : ℂ) - (i : ℕ))) * _ = _
      rw [show (∏ i : Fin (m + 1), Zc i (2 * 0 + ((m + 1 : ℕ) : ℂ) - (i : ℕ))) =
          ∏ i : Fin (m + 1), H i ((m + 1 - i : ℕ) : ℂ) from
        Finset.prod_congr rfl fun i _ => by rw [h0 i]; exact (hfix i).2.2.1]
      rw [Fin.prod_univ_castSucc, hlj]
      rw [show (∏ i : Fin m, H i.castSucc ((m + 1 - (i.castSucc : ℕ) : ℕ) : ℂ)) =
          ∏ i : Fin m, Z i.castSucc ((m + 1 - i : ℕ) : ℂ) from Finset.prod_congr rfl fun i _ => by
        have hre : 1 < (((m + 1 - (i : ℕ) : ℕ)) : ℂ).re := by
          rw [Complex.natCast_re]
          have : 2 ≤ m + 1 - (i : ℕ) := by omega
          exact_mod_cast this
        exact val_gt S _ (fun v => hnc v _) _ _ (hZp i.castSucc) _ hre (hHa' i.castSucc) (hHe' i.castSucc)]
      ring

end PositivityTheory.SiegelWeilFormula.Gen.WQ

end
