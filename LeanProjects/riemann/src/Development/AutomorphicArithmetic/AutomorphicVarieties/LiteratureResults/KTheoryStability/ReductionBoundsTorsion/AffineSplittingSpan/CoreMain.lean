import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.CoreRec

noncomputable section

namespace PositivityTheory.KB.SplitAffineSpectral.NormTraceLemmas

variable {P Q : Type} [Group P] [Group Q]

private theorem bi_apply_eq_apply_const_one_of_dv_eq_zero {a : ℕ} (F : Bi P Q a 1) (h : dv F = 0) (x : Fin a → Q) (z : Fin 1 → P) :
    F x z = F x (fun _ => 1) := by
  have h1 := congrFun (congrFun h x) ![1, z 0]
  simp [dv, dc, Fin.sum_univ_two] at h1
  have e1 : (fun _ : Fin 1 => z 0) = z := by
    funext j
    rw [Subsingleton.elim j 0]
  have e2 : (fun j : Fin 1 => (![1, z 0] : Fin 2 → P) (Fin.succAbove 1 j)) = fun _ => 1 := by
    funext j
    rw [Subsingleton.elim j 0]
    rfl
  rw [e1, e2] at h1
  linarith

private theorem exists_quasiCocycle_eq_dh_zz_of_pInv_dv_dh_zero (hB : SplitB) (pr : P →* Q) (s : Q →* P) (hs : ∀ g, pr (s g) = g) {N : ℕ}
    (F : Bi P Q (N + 2) 1) (hF : PInv pr F) (hv : dv F = 0) (hh : dh F = 0) :
    ∃ b : (Fin (N + 2) → Q) → ℝ, QC b ∧ F = ((-1 : ℝ) ^ (N + 1)) • dh (zz pr b (N + 1) 1) := by
  have hc := bi_apply_eq_apply_const_one_of_dv_eq_zero F hv
  unfold PInv at hF
  have hdc : dc (fun x => F x (fun _ => 1)) = 0 := by
    funext x
    exact congrFun (congrFun hh x) (fun _ => 1)
  refine ⟨fun x => F x (fun _ => 1), ?_, ?_⟩
  · unfold QC
    refine ⟨?_, hdc⟩
    intro g x
    show F (fun i => g * x i) (fun _ => 1) = F x (fun _ => 1)
    have h1 := hF (s g) x (fun _ => 1)
    simp only [hs, mul_one] at h1
    rw [← h1]
    exact (hc _ _).symm
  · rw [hB P Q pr N _ hdc, smul_smul, ← mul_pow]
    simp only [neg_one_mul, neg_neg, one_pow, one_smul]
    funext x z
    exact hc x z

theorem claimS (hB : SplitB) (hS : SplitS) (hZ : ZInv) (hE : E2VanishingOtherColumns) (pr : P →* Q) (s : Q →* P)
    (hs : ∀ g, pr (s g) = g) (u : Q) (hu : ∀ g, g * u = u * g) (m : ℕ) (hm : ColPoly pr s u m) :
    ∀ q : ℕ, q + 1 ≤ m → ∀ (p : ℕ) (x : Bi P Q (p + 2) (q + 2)), PInv pr x → dv x = 0 → dh x = 0 →
      GoodS pr x := by
  intro q
  induction q with
  | zero =>
    intro hq p x hx hv hh
    obtain ⟨w, e, hw, hwv, he, rfl⟩ := hE P Q pr s hs u hu m hm p 0 hq x hx hv hh
    have hyv : dv (dh e) = 0 := by
      rw [← dh_dv]
      rw [dh_add, dh_dh] at hh
      simpa using hh
    obtain ⟨b, hb, hyb⟩ := exists_quasiCocycle_eq_dh_zz_of_pInv_dv_dh_zero hB pr s hs (dh e) (PInv.dh pr he) hyv (dh_dh e)
    have hb' : QC b := hb
    unfold QC at hb
    have h2 : dh (zz pr b (p + 1) (0 + 2)) = (-1 : ℝ) ^ (p + 1) • dv (zz pr b (p + 1 + 1) 1) :=
      hS P Q pr p 0 b hb.2
    have hr : (-1 : ℝ) * (-1) ^ (p + 1) = (-1) ^ (p + 1 + 1) := by ring
    unfold GoodS
    refine ⟨p + 0 + 2, rfl, (-1 : ℝ) • b, hb'.smul _, w, e - (-1 : ℝ) ^ (p + 1 + 1) • zz pr b (p + 1 + 1) 1,
      hw, hwv, ?_, ?_, ?_⟩
    · exact PInv.sub pr he (PInv.smul pr _ (hZ P Q pr _ _ _ b (by omega) hb.1))
    · rw [dh_sub, dh_smul, ← hyb, sub_self]
    · rw [zz_smul, dh_smul, h2, smul_smul, hr, dv_sub, dv_smul]
      abel
  | succ q ih =>
    intro hq p x hx hv hh
    obtain ⟨w, e, hw, hwv, he, rfl⟩ := hE P Q pr s hs u hu m hm p (q + 1) hq x hx hv hh
    have hyv : dv (dh e) = 0 := by
      rw [← dh_dv]
      rw [dh_add, dh_dh] at hh
      simpa using hh
    have hg := ih (by omega) (p + 1) (dh e) (PInv.dh pr he) hyv (dh_dh e)
    unfold GoodS at hg
    obtain ⟨n, hn, b, hb, w', e', hw', hwv', he', hhe', hy⟩ := hg
    obtain rfl : n = p + (q + 1) + 2 := by omega
    obtain ⟨f, hf, hef⟩ := row_exact pr e' he' hhe'
    have hb' : QC b := hb
    unfold QC at hb
    have h2 : dh (zz pr b (p + 1) (q + 1 + 2)) = (-1 : ℝ) ^ (p + 1) • dv (zz pr b (p + 1 + 1) (q + 2)) :=
      hS P Q pr p (q + 1) b hb.2
    unfold GoodS
    refine ⟨p + (q + 1) + 2, rfl, (-1 : ℝ) ^ (p + 1) • b, hb'.smul _, w,
      e - zz pr b (p + 1 + 1) (q + 2) - w' - dv f, hw, hwv, ?_, ?_, ?_⟩
    · exact PInv.sub pr (PInv.sub pr (PInv.sub pr he (hZ P Q pr _ _ _ b (by omega) hb.1)) hw')
        (PInv.dv pr hf)
    · rw [dh_sub, dh_sub, dh_sub, hy, dh_dv f, ← hef]
      abel
    · rw [zz_smul, dh_smul, h2, smul_smul, ← mul_pow, dv_sub, dv_sub, dv_sub, hwv', dv_dv]
      simp only [neg_one_mul, neg_neg, one_pow, one_smul]
      abel

theorem claimT (hB : SplitB) (hA : SplitA) (hS : SplitS) (hZ : ZInv) (hEz : E2VanishingFirstColumn) (hEs : E2VanishingOtherColumns)
    (pr : P →* Q) (s : Q →* P) (hs : ∀ g, pr (s g) = g) (u : Q) (hu : ∀ g, g * u = u * g) (m : ℕ)
    (hm : ColPoly pr s u m) (q : ℕ) (hq : q + 1 ≤ m) (x : Bi P Q 1 (q + 2)) (hx : PInv pr x)
    (hv : dv x = 0) (hh : dh x = 0) : GoodT pr x := by
  obtain ⟨e, he, rfl⟩ := hEz P Q pr s hs u hu m hm q hq x hx hv hh
  have hyv : dv (dh e) = 0 := by
    rw [← dh_dv]
    exact hh
  unfold GoodT
  cases q with
  | zero =>
    obtain ⟨b, hb, hyb⟩ := exists_quasiCocycle_eq_dh_zz_of_pInv_dv_dh_zero hB pr s hs (dh e) (PInv.dh pr he) hyv (dh_dh e)
    have hb' : QC b := hb
    unfold QC at hb
    have h2 : Wtop pr b = dv (zz pr b (0 + 1) 1) := hA P Q pr 0 b hb.2
    refine ⟨(-1 : ℝ) ^ (0 + 1) • b, hb'.smul _, e - (-1 : ℝ) ^ (0 + 1) • zz pr b (0 + 1) 1, ?_, ?_, ?_⟩
    · exact PInv.sub pr he (PInv.smul pr _ (hZ P Q pr _ _ _ b (by omega) hb.1))
    · rw [dh_sub, dh_smul, ← hyb, sub_self]
    · rw [Wtop_smul, h2, dv_sub, dv_smul]
      abel
  | succ q =>
    have hg := claimS hB hS hZ hEs pr s hs u hu m hm q (by omega) 0 (dh e) (PInv.dh pr he) hyv (dh_dh e)
    unfold GoodS at hg
    obtain ⟨n, hn, b, hb, w', e', hw', hwv', he', hhe', hy⟩ := hg
    obtain rfl : n = q + 1 + 1 := by omega
    obtain ⟨f, hf, hef⟩ := row_exact pr e' he' hhe'
    have hb' : QC b := hb
    unfold QC at hb
    have h2 : Wtop pr b = dv (zz pr b (0 + 1) (q + 2)) := hA P Q pr (q + 1) b hb.2
    refine ⟨b, hb', e - zz pr b (0 + 1) (q + 2) - w' - dv f, ?_, ?_, ?_⟩
    · exact PInv.sub pr (PInv.sub pr (PInv.sub pr he (hZ P Q pr _ _ _ b (by omega) hb.1)) hw')
        (PInv.dv pr hf)
    · rw [dh_sub, dh_sub, dh_sub, hy, dh_dv f, ← hef]
      abel
    · rw [h2, dv_sub, dv_sub, dv_sub, hwv', dv_dv]
      abel

private theorem bi_fin_one_apply_eq_apply_one_of_dh_eq_zero {k : ℕ} (F : Bi P Q 1 k) (h : dh F = 0) (x : Fin 1 → Q) (y : Fin k → P) :
    F x y = F (fun _ => 1) y := by
  have h1 := congrFun (congrFun h ![1, x 0]) y
  simp [dh, dc, Fin.sum_univ_two] at h1
  have e1 : (fun _ : Fin 1 => x 0) = x := by
    funext j
    rw [Subsingleton.elim j 0]
  have e2 : (fun j : Fin 1 => (![1, x 0] : Fin 2 → Q) (Fin.succAbove 1 j)) = fun _ => 1 := by
    funext j
    rw [Subsingleton.elim j 0]
    rfl
  rw [e1, e2] at h1
  linarith

theorem core_of (hA : SplitA) (hS : SplitS) (hB : SplitB) (hZ : ZInv) (hEz : E2VanishingFirstColumn) (hEs : E2VanishingOtherColumns) : Core := by
  unfold Core
  intro P Q _ _ pr s hs u hu m hm j hj c hc hdc hvan
  unfold InvS at hc
  have hP : PInv pr (fun (_ : Fin 1 → Q) (y : Fin (j + 2) → P) => c y : Bi P Q 1 (j + 2)) := by
    unfold PInv
    intro g a y
    exact hc g (Set.mem_univ g) y
  have hV : dv (fun (_ : Fin 1 → Q) (y : Fin (j + 2) → P) => c y : Bi P Q 1 (j + 2)) = 0 := by
    funext a y
    exact congrFun hdc y
  have hH : dh (fun (_ : Fin 1 → Q) (y : Fin (j + 2) → P) => c y : Bi P Q 1 (j + 2)) = 0 := by
    funext a y
    simp [dh, dc, Fin.sum_univ_two]
  have hT := claimT hB hA hS hZ hEz hEs pr s hs u hu m hm j hj _ hP hV hH
  unfold GoodT at hT
  obtain ⟨b, hb, e, he, hhe, hxe⟩ := hT
  unfold PInv at he
  set e' : (Fin (j + 1) → P) → ℝ := fun z => e (fun _ => 1) z with he'
  have hinv : ∀ (g : P) (y : Fin (j + 1) → P), e' (fun i => g * y i) = e' y := by
    intro g y
    exact (bi_fin_one_apply_eq_apply_one_of_dh_eq_zero e hhe _ _).symm.trans (he g (fun _ => 1) y)
  have hpt : ∀ y, c y = b (fun i => pr (y i)) + dc e' y := fun y => congrFun (congrFun hxe (fun _ => 1)) y
  have hbv : ∀ y : Fin (j + 2) → Q, b y = - dc (fun z => e' (fun i => s (z i))) y := by
    intro y
    have h := hpt (fun i => s (y i))
    rw [hvan y] at h
    simp only [hs] at h
    have h3 : dc (fun z => e' (fun i => s (z i))) y = dc e' (fun i => s (y i)) := rfl
    linarith
  refine ⟨e' - fun z => e' (fun i => s (pr (z i))), ?_, ?_⟩
  · unfold InvS
    intro g _ y
    simp only [Pi.sub_apply, map_mul]
    rw [hinv g y]
    congr 1
    exact hinv (s (pr g)) (fun i => s (pr (y i)))
  · funext y
    rw [dc_sub, Pi.sub_apply, hpt y, hbv (fun i => pr (y i))]
    have h3 : dc (fun z => e' (fun i => s (z i))) (fun i => pr (y i))
        = dc (fun z => e' (fun i => s (pr (z i)))) y := rfl
    linarith

end PositivityTheory.KB.SplitAffineSpectral.NormTraceLemmas

end
