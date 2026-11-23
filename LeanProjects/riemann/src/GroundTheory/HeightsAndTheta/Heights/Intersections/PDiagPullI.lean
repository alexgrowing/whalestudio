import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsDiagPull
import GroundTheory.HeightsAndTheta.Heights.Intersections.PRFormula
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 DiagRAux

noncomputable section

set_option linter.unusedSectionVars false

namespace DiagonalPullback

theorem pullDeg_add (j : Fin 2) (a b : T.YBlk → ℤ) :
    I1.pullDeg (diagonalBlockIndex j) (a + b) = I1.pullDeg (diagonalBlockIndex j) a + I1.pullDeg (diagonalBlockIndex j) b := by
  funext k
  by_cases h : ∃ k', diagonalBlockIndex j k' = k
  · obtain ⟨k', rfl⟩ := h
    simp only [Pi.add_apply, pullDeg_segreBlockEmbedding]
  · simp only [I1.pullDeg, Pi.add_apply, Function.extend_apply' _ _ _ h, Pi.zero_apply, add_zero]

theorem pullDeg_eq_alt (j : Fin 2) (c : T.YBlk → ℤ) : I1.pullDeg (diagonalBlockIndex j) c = T.pullDeg j c := by
  funext k
  fin_cases j <;> cases k
  · exact pullDeg_segreBlockEmbedding 0 c .base
  · exact pullDeg_segreBlockEmbedding 0 c .det
  · exact pullDeg_segreBlockEmbedding 0 c .line
  · exact pullDeg_otherLine 0 c
  · exact pullDeg_segreBlockEmbedding 1 c .base
  · exact pullDeg_segreBlockEmbedding 1 c .det
  · exact pullDeg_otherLine 1 c
  · exact pullDeg_segreBlockEmbedding 1 c .line

variable {ι ν κ : Type} [Fintype ι] [Fintype ν] [Fintype κ]

theorem isPull_fs (j : Fin 2) (c : T.YBlk → ℤ) :
    IsPullHerm (diagonalBlockIndex j) (T.yyEmb (ι := ι) (ν := ν) (κ := κ) j)
      (HermLine.ofMetrics (fun k => fsMetric (T.yyIdx ι ν κ k)) c)
      (HermLine.ofMetrics (fun k => fsMetric (T.wwIdx ι ν κ k)) (I1.pullDeg (diagonalBlockIndex j) c)) := by
  refine ⟨rfl, fun z => ?_⟩
  rw [ofMetrics_fs_h, ofMetrics_fs_h, prod_WBlk, prod_YBlk, pullDeg_eq_alt]
  fin_cases j
  · simp [T.pullDeg, T.yyEmb]
    rfl
  · simp [T.pullDeg, T.yyEmb]
    rfl

theorem X_mem_diag_iff {Ω : Type} [Field Ω] {E : Type} [AddCommGroup E] [Module Ω E] {Φ : Type} [Field Φ]
    [Algebra Ω Φ] (x : ι → Ω) (δ : ν → Ω) (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω) (a₀ : Φ)
    (p : Σ k, T.wwIdx ι ν κ k) :
    (X p : MRing (T.wwIdx ι ν κ)) ∈ T.wwIdeal x δ e φ a₀ a₀ ↔ T.wwCoord x δ e φ a₀ a₀ p = 0 := by
  show X p ∈ RingHom.ker _ ↔ _
  rw [RingHom.mem_ker, T.multiConeMap, eval₂Hom_X', mul_eq_zero, C_eq_zero]
  simp [X_ne_zero]

theorem I_pull_eq {D : ℕ} (S : ProjectiveLineBundle D)
    (I : Ideal (MRing S.WIdx) → (n : ℕ) → (Fin n → HermLine S.WIdx) → ℝ) (hF : IsIntersectionFamily I)
    (hΔ : IsArithVar S.Diag (D + 1)) (hDP : T.DiagPullStatement (Φ := S.Φ) S.x S.δ S.e S.φ)
    (L : Fin D → HermLine S.WIdx) (hL : ∀ j, IsSmoothHerm (L j))
    (A : HermLine S.YIdx) (A₀ A₁ : HermLine S.WIdx) (d : T.YBlk → ℕ) (hd : ∀ k, A.a k = d k)
    (hA : IsSmoothHerm A) (hp0 : IsPullHerm (diagonalBlockIndex 0) (T.yyEmb 0) A A₀)
    (hp1 : IsPullHerm (diagonalBlockIndex 1) (T.yyEmb 1) A A₁) :
    I S.Diag (D + 1) (Fin.snoc L A₀) = I S.Diag (D + 1) (Fin.snoc L A₁) := by
  have hprime : S.Diag.IsPrime := hΔ.2.1.1
  have hrel : IsRelevant S.Diag := hΔ.2.1.2.2
  obtain ⟨ib, hib⟩ := hrel .base
  obtain ⟨il, hil⟩ := hrel .det
  obtain ⟨ik, hik⟩ := hrel .line0
  have hik' : (X ⟨T.WBlk.line1, (ik : S.κ)⟩ : MRing S.WIdx) ∉ S.Diag := by
    intro h
    apply hik
    rw [X_mem_diag_iff] at h ⊢
    exact h

  set s : MRing S.YIdx := X ⟨T.YBlk.base, (ib : S.ι)⟩ ^ d .base * X ⟨T.YBlk.det, (il : S.ν)⟩ ^ d .det *
    X ⟨T.YBlk.line, (ik : S.κ)⟩ ^ d .line with hs_def
  have hs : IsMultiHomog s d := by
    have h := exHomog_mul (exHomog_mul (exHomog_pow (exHomog_X (ι := S.YIdx) T.YBlk.base ib) (d .base))
      (exHomog_pow (exHomog_X (ι := S.YIdx) T.YBlk.det il) (d .det)))
      (exHomog_pow (exHomog_X (ι := S.YIdx) T.YBlk.line ik) (d .line))
    convert h using 1
    funext k
    cases k <;> simp
  have hs0 : rename (T.yyEmb 0) s = X ⟨T.WBlk.base, ib⟩ ^ d .base * X ⟨T.WBlk.det, il⟩ ^ d .det *
      X ⟨T.WBlk.line0, ik⟩ ^ d .line := by
    simp only [hs_def, map_mul, map_pow, rename_X]
    rfl
  have hs1 : rename (T.yyEmb 1) s = X ⟨T.WBlk.base, ib⟩ ^ d .base * X ⟨T.WBlk.det, il⟩ ^ d .det *
      X ⟨T.WBlk.line1, (ik : S.κ)⟩ ^ d .line := by
    simp only [hs_def, map_mul, map_pow, rename_X]
    rfl
  have hpow : ∀ {f : MRing S.WIdx} (n : ℕ), f ∉ S.Diag → f ^ n ∉ S.Diag :=
    fun n hf h => hf (hprime.mem_of_pow_mem n h)
  have hmul : ∀ {f g : MRing S.WIdx}, f ∉ S.Diag → g ∉ S.Diag → f * g ∉ S.Diag :=
    fun hf hg h => (hprime.mem_or_mem h).elim hf hg
  have hn0 : rename (T.yyEmb 0) s ∉ S.Diag := by
    rw [hs0]
    exact hmul (hmul (hpow _ hib) (hpow _ hil)) (hpow _ hik)
  have hn1 : rename (T.yyEmb 1) s ∉ S.Diag := by
    rw [hs1]
    exact hmul (hmul (hpow _ hib) (hpow _ hil)) (hpow _ hik')

  set a0 : T.WBlk → ℕ := d .base • Pi.single T.WBlk.base 1 + d .det • Pi.single T.WBlk.det 1 +
    d .line • Pi.single T.WBlk.line0 1 with ha0
  set a1 : T.WBlk → ℕ := d .base • Pi.single T.WBlk.base 1 + d .det • Pi.single T.WBlk.det 1 +
    d .line • Pi.single T.WBlk.line1 1 with ha1
  have hh0 : IsMultiHomog (rename (T.yyEmb 0) s) a0 := by
    rw [hs0]
    exact exHomog_mul (exHomog_mul (exHomog_pow (exHomog_X (ι := S.WIdx) T.WBlk.base ib) _)
      (exHomog_pow (exHomog_X (ι := S.WIdx) T.WBlk.det il) _)) (exHomog_pow (exHomog_X (ι := S.WIdx) T.WBlk.line0 ik) _)
  have hh1 : IsMultiHomog (rename (T.yyEmb 1) s) a1 := by
    rw [hs1]
    exact exHomog_mul (exHomog_mul (exHomog_pow (exHomog_X (ι := S.WIdx) T.WBlk.base ib) _)
      (exHomog_pow (exHomog_X (ι := S.WIdx) T.WBlk.det il) _))
      (exHomog_pow (exHomog_X (ι := S.WIdx) T.WBlk.line1 (ik : S.κ)) _)
  have hT0 : A₀.a = T.pullDeg 0 A.a := by rw [hp0.1, pullDeg_eq_alt]
  have hT1 : A₁.a = T.pullDeg 1 A.a := by rw [hp1.1, pullDeg_eq_alt]
  have hd0 : ∀ k, A₀.a k = a0 k := by
    intro k
    rw [hT0]
    cases k <;> simp [T.pullDeg, ha0, hd]
  have hd1 : ∀ k, A₁.a k = a1 k := by
    intro k
    rw [hT1]
    cases k <;> simp [T.pullDeg, ha1, hd]

  have e0 := hF.2.2 S.Diag D L A₀ _ a0 hΔ hL (isSmoothHerm_pull 0 hA hp0) hd0 hh0 hn0
  have e1 := hF.2.2 S.Diag D L A₁ _ a1 hΔ hL (isSmoothHerm_pull 1 hA hp1) hd1 hh1 hn1
  rw [e0, e1, recR_eq, recR_eq, cycR_eq_finsum, cycR_eq_finsum, (hDP (S.a 0)).1 s d hs]
  congr 1
  exact ptsIntegral_congr_mcPts _ (fun _ _ _ => rfl) fun z hz =>
    (hDP (S.a 0)).2.2 s d hs A A₀ A₁ hd ⟨hT0, hp0.2⟩ ⟨hT1, hp1.2⟩ z hz

end DiagonalPullback

open DiagonalPullback

theorem DiagPullI.proof (hDD : DiagDiv.Statement) (hDP : DiagPull.Statement) : DiagPullI.Statement := by
  intro I hI D S X X₀ X₁ L hX hp0 hp1 hL
  have hF : IsIntersectionFamily (I T.WBlk S.WIdx) := hI T.WBlk S.WIdx
  have hW : IsArithVar S.WW (D + 2) := S.arithWW

  have hgW : S.g ∉ S.WW := by
    have hh : aeval (T.wwCoord S.x S.δ S.e S.φ (S.a 0) (S.a 1)) S.h ≠ 0 :=
      (not_mem_ker_iff_aeval_ne _ S.h _ S.h_deg).1 S.h_nmem
    refine (not_mem_ker_iff_aeval_ne _ S.g _ S.g_deg).2 ?_
    rw [S.quot]
    refine mul_ne_zero ?_ hh
    exact sub_ne_zero.2 (S.indep.injective.ne (by decide))
  have hdiv := (hDD S.Ω S.ι S.ν S.κ S.E S.Φ S.x S.B S.e S.φ S.δ S.dualSec S.dualGen S.detGen S.chart S.a
    S.indep).2 S.n S.g S.h S.g_deg S.h_deg S.h_nmem S.quot
  have hΔhor : IsHorizontal S.Diag := by
    have h := hW.2.2.1
    unfold IsHorizontal at h ⊢
    rw [← h]
    exact comap_C_ker_multiConeMap _ _
  have hΔmem : S.Diag ∈ divSupp S.WW S.g := by
    refine mem_divSupp_of_divCycle_ne_zero fun h0 => ?_
    have := congrArg (fun z => z S.Diag) hdiv
    simp only [Finsupp.coe_sub, Pi.sub_apply, T.toZCycle, Finsupp.mapRange_apply, h0,
      Finsupp.single_eq_same] at this
    omega
  have hΔ : IsArithVar S.Diag (D + 1) :=
    (divSuppArith T.WBlk S.WIdx S.WW (D + 1)
      (HermLine.ofMetrics (fun k => maxMetric ℂ (S.WIdx k)) (fun k => (T.wwDeg S.n 1 k : ℤ))) S.g S.Diag hW
      ⟨T.wwDeg S.n 1, fun _ => rfl, S.g_deg, hgW⟩ hΔmem).1 hΔhor
  have hDP' := hDP S.Ω S.ι S.ν S.κ S.E S.Φ S.x S.e S.φ S.δ

  set b : T.YBlk → ℤ := fun k => ((X.a k).natAbs : ℤ) with hb
  set B : HermLine S.YIdx := HermLine.ofMetrics (fun k => fsMetric (S.YIdx k)) b with hB
  set B₀ : HermLine S.WIdx := HermLine.ofMetrics (fun k => fsMetric (S.WIdx k)) (I1.pullDeg (diagonalBlockIndex 0) b)
    with hB₀
  set B₁ : HermLine S.WIdx := HermLine.ofMetrics (fun k => fsMetric (S.WIdx k)) (I1.pullDeg (diagonalBlockIndex 1) b)
    with hB₁
  have hsB : IsSmoothHerm B := isSmoothHerm_ofMetrics_fs b
  have hpB0 : IsPullHerm (diagonalBlockIndex 0) (T.yyEmb 0) B B₀ := isPull_fs 0 b
  have hpB1 : IsPullHerm (diagonalBlockIndex 1) (T.yyEmb 1) B B₁ := isPull_fs 1 b
  have hsX0 : IsSmoothHerm X₀ := isSmoothHerm_pull 0 hX hp0
  have hsX1 : IsSmoothHerm X₁ := isSmoothHerm_pull 1 hX hp1
  have hsB0 : IsSmoothHerm B₀ := isSmoothHerm_ofMetrics_fs _
  have hsB1 : IsSmoothHerm B₁ := isSmoothHerm_ofMetrics_fs _
  have hpXB : ∀ (j : Fin 2) {Xj Bj : HermLine S.WIdx}, IsPullHerm (diagonalBlockIndex j) (T.yyEmb j) X Xj →
      IsPullHerm (diagonalBlockIndex j) (T.yyEmb j) B Bj → IsPullHerm (diagonalBlockIndex j) (T.yyEmb j) (X.tensor B) (Xj.tensor Bj) := by
    intro j Xj Bj hXj hBj
    refine ⟨?_, fun z => ?_⟩
    · show Xj.a + Bj.a = I1.pullDeg (diagonalBlockIndex j) (X.a + B.a)
      rw [pullDeg_add, hXj.1, hBj.1]
    · show Xj.h z * Bj.h z = X.h _ * B.h _
      rw [hXj.2, hBj.2]
  have c1 := I_pull_eq S (I T.WBlk S.WIdx) hF hΔ hDP' L hL (X.tensor B) (X₀.tensor B₀) (X₁.tensor B₁)
    (fun k => (X.a k + (X.a k).natAbs).toNat)
    (fun k => by
      show X.a k + ((X.a k).natAbs : ℤ) = _
      rw [Int.toNat_of_nonneg (by omega)])
    (isSmoothHerm_tensor hX hsB) (hpXB 0 hp0 hpB0) (hpXB 1 hp1 hpB1)
  have c2 := I_pull_eq S (I T.WBlk S.WIdx) hF hΔ hDP' L hL B B₀ B₁ (fun k => (X.a k).natAbs) (fun _ => rfl)
    hsB hpB0 hpB1
  have a0 := hF.2.1 S.Diag D L X₀ B₀ hΔ hL hsX0 hsB0
  have a1 := hF.2.1 S.Diag D L X₁ B₁ hΔ hL hsX1 hsB1
  linarith

end

end GroundTheory.Heights₂.Heights.Inter
