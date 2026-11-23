import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsStokesStep
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ATeleSt
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

namespace StokesTelescope

set_option linter.unusedSectionVars false

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem ptsIntegral_congr_g (P : Ideal (MRing ι)) {e : ℕ} (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ)
    {g g' : ((Σ k, ι k) → ℂ) → ℝ} (hg : ∀ z ∈ mcPts P, g z = g' z) :
    ptsIntegral P φ g = ptsIntegral P φ g' := by
  classical
  unfold ptsIntegral ptsIntegralAt
  split_ifs with hΨ
  · congr 1
    funext y
    refine finsum_congr fun w => finsum_congr fun _ => ?_
    unfold sheetDensity
    split_ifs with hγ
    · rw [hg _ hγ.choose_spec.2.self_of_nhds.2.1]
    · rfl
  · rfl

theorem ptsIntegral_zero_g (P : Ideal (MRing ι)) {e : ℕ} (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ) :
    ptsIntegral P φ (fun _ => (0 : ℝ)) = 0 := by
  classical
  unfold ptsIntegral ptsIntegralAt sheetDensity
  split_ifs <;> simp

theorem cxHessian_const_mul {D : ℕ} (c : ℝ) (f : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) :
    cxHessian (fun y => c * f y) z = (c : ℂ) • cxHessian f z := by
  have h1 : fderiv ℝ (fun y => c * f y) = c • fderiv ℝ f := fderiv_const_smul_field (f := f) c
  have h2 : fderiv ℝ (c • fderiv ℝ f) = c • fderiv ℝ (fderiv ℝ f) := fderiv_const_smul_field (f := fderiv ℝ f) c
  ext i j
  simp only [cxHessian, h1, h2, Pi.smul_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, Matrix.smul_apply]
  push_cast
  ring

theorem mixedDisc_smul {D : ℕ} (c : ℂ) (A : Fin D → Matrix (Fin D) (Fin D) ℂ) :
    mixedDisc (fun k => c • A k) = c ^ D * mixedDisc A := by
  unfold mixedDisc
  simp only [← Finset.smul_sum, Matrix.det_smul, Fintype.card_fin, Finset.mul_sum]
  refine Finset.sum_congr rfl fun S _ => by ring

theorem maDensity_const_mul {D : ℕ} (c : ℝ) (φ : Fin D → (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) :
    maDensity (fun k y => c * φ k y) z = c ^ D * maDensity φ z := by
  simp only [maDensity, cxHessian_const_mul, mixedDisc_smul]
  rw [← Complex.ofReal_pow, Complex.re_ofReal_mul]
  ring

theorem sheetDensity_scale (P : Ideal (MRing ι)) {e : ℕ}
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ)
    (g : ((Σ k, ι k) → ℂ) → ℝ) (c c' : ℝ) (y : Fin e → ℂ) (w : ((k : K) → ι k) → ℂ) :
    sheetDensity P Ψ (fun j z => c * φ j z) (fun z => c' * g z) y w = c' * c ^ e * sheetDensity P Ψ φ g y w := by
  unfold sheetDensity
  split_ifs with hγ
  · simp only [maDensity_const_mul]
    ring
  · ring

theorem ptsIntegral_scale (P : Ideal (MRing ι)) {e : ℕ} (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ)
    (g : ((Σ k, ι k) → ℂ) → ℝ) (c c' : ℝ) :
    ptsIntegral P (fun j z => c * φ j z) (fun z => c' * g z) = c' * c ^ e * ptsIntegral P φ g := by
  classical
  unfold ptsIntegral
  split_ifs with hΨ
  · unfold ptsIntegralAt
    rw [← MeasureTheory.integral_const_mul]
    congr 1
    funext y
    rw [mul_finsum_mem]
    simp only [sheetDensity_scale]
  · simp

def blockInd : HermLine ι where
  a := 0
  h z := if ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0 then 1 else 0
  pos z hz := by simp [hz]
  smul c z hc := by
    have e : (∀ k, ∃ i, c k * z ⟨k, i⟩ ≠ 0) ↔ ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0 := by
      simp [hc]
    simp only [e, Pi.zero_apply, zpow_zero, Finset.prod_const_one, one_mul]

theorem blockInd_smooth : IsSmoothHerm (blockInd (ι := ι)) := by
  refine (contDiffOn_const (c := (1 : ℝ))).congr fun z hz => ?_
  simp only [Set.mem_setOf_eq] at hz
  show (if ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0 then (1 : ℝ) else 0) = 1
  rw [if_pos hz]

def ratio (A A' : HermLine ι) (ha : A'.a = A.a) : HermLine ι where
  a := 0
  h z := A'.h z / A.h z
  pos z hz := div_pos (A'.pos z hz) (A.pos z hz)
  smul c z hc := by
    rw [A'.smul c z hc, A.smul c z hc, ha]
    have hne : (∏ k, ‖c k‖ ^ A.a k) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.mpr (hc k))
    rw [mul_div_mul_left _ _ hne]
    simp

theorem ratio_smooth {A A' : HermLine ι} (ha : A'.a = A.a) (hA : IsSmoothHerm A) (hA' : IsSmoothHerm A') :
    IsSmoothHerm (ratio A A' ha) :=
  hA'.div hA fun z hz => (A.pos z hz).ne'

variable {I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ}

theorem fam_degZero (hI : IsIntersectionFamily I) {P : Ideal (MRing ι)} {n : ℕ} (hP : IsArithVar P (n + 1))
    (L : Fin n → HermLine ι) (hL : ∀ j, IsSmoothHerm (L j)) (B : HermLine ι) (hB : IsSmoothHerm B)
    (hB0 : B.a = 0) :
    I P (n + 1) (Fin.snoc L B) =
      ptsIntegral P (fun j z => Real.log ((L j).h z)) fun z => Real.log (B.h z) := by
  classical
  have hR := hI.2.2 P n L B 1 0 hP hL hB (fun k => by simp [hB0]) tele_one_homog
    (fun h1 => hP.2.1.1.ne_top ((Ideal.eq_top_iff_one P).mpr h1))
  rw [hR]
  unfold recR
  rw [tele_divSupp_one, finsum_mem_empty, zero_sub]
  unfold arInt
  have hl : logNorm B 1 = fun z => - Real.log (B.h z) := by
    funext z
    simp [logNorm, Real.log_inv]
  rw [hl, tele_ptsIntegral_neg, neg_neg]

theorem fam_congr_blocks (hI : IsIntersectionFamily I) {P : Ideal (MRing ι)} {n : ℕ} (hP : IsArithVar P (n + 1))
    (L : Fin n → HermLine ι) (hL : ∀ j, IsSmoothHerm (L j)) {X Y : HermLine ι} (hX : IsSmoothHerm X)
    (hY : IsSmoothHerm Y) (ha : X.a = Y.a) (hh : ∀ z, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → X.h z = Y.h z) :
    I P (n + 1) (Fin.snoc L X) = I P (n + 1) (Fin.snoc L Y) := by
  have hT : I P (n + 1) (Fin.snoc L blockInd) = 0 := by
    rw [fam_degZero hI hP L hL blockInd blockInd_smooth rfl,
      ptsIntegral_congr_g P _ (g' := fun _ => 0) (fun z hz => by simp [blockInd, hz.1])]
    exact ptsIntegral_zero_g P _
  have hXT : X.tensor blockInd = Y.tensor blockInd := by
    apply tele_herm_ext
    · show X.a + 0 = Y.a + 0
      rw [ha]
    · funext z
      show X.h z * blockInd.h z = Y.h z * blockInd.h z
      by_cases hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0
      · rw [hh z hz]
      · simp [blockInd, hz]
  have hx := hI.2.1 P n L X blockInd hP hL hX blockInd_smooth
  have hy := hI.2.1 P n L Y blockInd hP hL hY blockInd_smooth
  rw [hXT, hT, add_zero] at hx
  rw [hT, add_zero] at hy
  rw [← hx, hy]

def fam (A A' : HermLine ι) (N i : ℕ) : Fin N → HermLine ι :=
  fun j => if j.val < i then A' else A

theorem fam_succAbove (A A' : HermLine ι) (D i : ℕ) (hi : i < D + 1) (k : ℕ) (hk : k = i ∨ k = i + 1) :
    fam A A' (D + 1) k ∘ (⟨i, hi⟩ : Fin (D + 1)).succAbove = fam A A' D i := by
  funext j
  simp only [Function.comp_apply, fam]
  by_cases h : j.val < i
  · have h' : Fin.castSucc j < (⟨i, hi⟩ : Fin (D + 1)) := by
      rw [Fin.lt_def]
      exact h
    rw [Fin.succAbove_of_castSucc_lt _ _ h', if_pos (show (Fin.castSucc j).val < k by
      show j.val < k
      omega), if_pos h]
  · have h' : (⟨i, hi⟩ : Fin (D + 1)) ≤ Fin.castSucc j := by
      rw [Fin.le_def]
      show i ≤ j.val
      omega
    rw [Fin.succAbove_of_le_castSucc _ _ h', if_neg (show ¬ (Fin.succ j).val < k by
      show ¬ j.val + 1 < k
      omega), if_neg h]

theorem fam_smooth {A A' : HermLine ι} (hA : IsSmoothHerm A) (hA' : IsSmoothHerm A') (N i : ℕ) (j : Fin N) :
    IsSmoothHerm (fam A A' N i j) := by
  unfold fam
  split_ifs
  · exact hA'
  · exact hA

theorem top_sub_top (hI : IsIntersectionFamily I) {P : Ideal (MRing ι)} {n : ℕ} (hP : IsArithVar P (n + 1))
    {A A' : HermLine ι} (hA : IsSmoothHerm A) (hA' : IsSmoothHerm A') (ha : A'.a = A.a) :
    I P (n + 1) (fun _ => A') - I P (n + 1) (fun _ => A) = ∑ i ∈ Finset.range (n + 1),
      ptsIntegral P (stokesMixPot A A' n i) (fun z => Real.log (A'.h z) - Real.log (A.h z)) := by
  classical
  have hsymm := hI.1
  have hadd := hI.2.1
  have hR := ratio_smooth ha hA hA'
  have htel := Finset.sum_range_sub (fun i => I P (n + 1) (fam A A' (n + 1) i)) (n + 1)
  have hT0 : fam A A' (n + 1) 0 = fun _ => A := by
    funext j
    simp [fam]
  have hT1 : fam A A' (n + 1) (n + 1) = fun _ => A' := by
    funext j
    simp [fam, j.isLt]
  simp only [hT0, hT1] at htel
  rw [← htel]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  have hLs := fam_smooth hA hA' n i
  have e1 : I P (n + 1) (fam A A' (n + 1) (i + 1)) = I P (n + 1) (Fin.snoc (fam A A' n i) A') := by
    have h := hsymm _ _ (fam A A' (n + 1) (i + 1)) (tele_perm ⟨i, hi⟩) hP (fam_smooth hA hA' _ _)
    have hv1 : fam A A' (n + 1) (i + 1) ⟨i, hi⟩ = A' := by
      simp [fam]
    rw [tele_comp_perm, fam_succAbove A A' n i hi (i + 1) (Or.inr rfl), hv1] at h
    exact h.symm
  have e0 : I P (n + 1) (fam A A' (n + 1) i) = I P (n + 1) (Fin.snoc (fam A A' n i) A) := by
    have h := hsymm _ _ (fam A A' (n + 1) i) (tele_perm ⟨i, hi⟩) hP (fam_smooth hA hA' _ _)
    have hv0 : fam A A' (n + 1) i ⟨i, hi⟩ = A := by
      simp [fam]
    rw [tele_comp_perm, fam_succAbove A A' n i hi i (Or.inl rfl), hv0] at h
    exact h.symm
  have hAR : IsSmoothHerm (A.tensor (ratio A A' ha)) := hA.mul hR
  have hN' : I P (n + 1) (Fin.snoc (fam A A' n i) A') =
      I P (n + 1) (Fin.snoc (fam A A' n i) (A.tensor (ratio A A' ha))) := by
    refine fam_congr_blocks hI hP _ hLs hA' hAR ?_ ?_
    · show A'.a = A.a + 0
      rw [ha, add_zero]
    · intro z hz
      show A'.h z = A.h z * (A'.h z / A.h z)
      rw [mul_div_cancel₀ _ (A.pos z hz).ne']
  rw [e1, e0, hN', hadd _ _ _ _ _ hP hLs hA hR, add_sub_cancel_left,
    fam_degZero hI hP _ hLs _ hR rfl]
  have hpot : (fun j z => Real.log ((fam A A' n i j).h z)) = stokesMixPot A A' n i := by
    funext j z
    simp only [fam, stokesMixPot]
    split_ifs <;> rfl
  rw [hpot]
  refine ptsIntegral_congr_g P _ fun z hz => ?_
  show Real.log (A'.h z / A.h z) = _
  rw [Real.log_div (A'.pos z hz.1).ne' (A.pos z hz.1).ne']

theorem top_sub_top_le (hS : StokesStep.Statement) (hI : IsIntersectionFamily I) {P : Ideal (MRing ι)} {n : ℕ}
    (hP : IsArithVar P (n + 1)) {A A' : HermLine ι} (hA : IsSemipositiveH P A) (hA' : IsSemipositiveH P A')
    (ha : A'.a = A.a) :
    I P (n + 1) (fun _ => A') - I P (n + 1) (fun _ => A) ≤ ((n + 1 : ℕ) : ℝ) *
      ptsIntegral P (fun (_ : Fin n) z => Real.log (A.h z)) (fun z => Real.log (A'.h z) - Real.log (A.h z)) := by
  rw [top_sub_top hI hP hA.1 hA'.1 ha]
  have h0 : stokesMixPot A A' n 0 = fun (_ : Fin n) z => Real.log (A.h z) := by
    funext j z
    simp [stokesMixPot]
  have hmono : ∀ i, i ≤ n →
      ptsIntegral P (stokesMixPot A A' n i) (fun z => Real.log (A'.h z) - Real.log (A.h z)) ≤
        ptsIntegral P (stokesMixPot A A' n 0) (fun z => Real.log (A'.h z) - Real.log (A.h z)) := by
    intro i
    induction i with
    | zero => intro _; exact le_rfl
    | succ i ih =>
      intro hi
      exact (hS K ι P n i A A' hP ha hA hA' (by omega)).trans (ih (by omega))
  rw [← h0]
  calc _ ≤ ∑ _i ∈ Finset.range (n + 1),
        ptsIntegral P (stokesMixPot A A' n 0) (fun z => Real.log (A'.h z) - Real.log (A.h z)) :=
        Finset.sum_le_sum fun i hi => hmono i (by rw [Finset.mem_range] at hi; omega)
    _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

end StokesTelescope

open StokesTelescope in

theorem StokesTelescope.proof (hS : StokesStep.Statement) : StokesTelescope.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D O Lt _ _ _ X B p q t t' hII hq hMU hN
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have ha : (X.MUq B p q t').a = (X.NbarQ B p q t).a := by
    simp only [ComponentSetting.MUq, MUc, ComponentSetting.NbarQ, smoothRepConj_a, smoothRep_a]
    rfl
  have h := top_sub_top_le hS (hII K ι) (n := D.n) D.arith hN hMU ha
  have hI0 : X.I0 B p q t t' = (q : ℝ)⁻¹ * (q : ℝ)⁻¹ ^ D.n *
      ptsIntegral (mCoordIdeal D.y) (fun (_ : Fin D.n) z => Real.log ((X.NbarQ B p q t).h z))
        (fun z => Real.log ((X.MUq B p q t').h z) - Real.log ((X.NbarQ B p q t).h z)) := by
    have e1 : X.omN B p q t = fun (_ : Fin D.n) z => (q : ℝ)⁻¹ * Real.log ((X.NbarQ B p q t).h z) := by
      funext j z
      simp only [ComponentSetting.omN]
      rw [div_eq_inv_mul]
    have e2 : X.wSt B p q t t' =
        fun z => (q : ℝ)⁻¹ * (Real.log ((X.MUq B p q t').h z) - Real.log ((X.NbarQ B p q t).h z)) := by
      funext z
      simp only [ComponentSetting.wSt]
      rw [div_eq_inv_mul]
    unfold ComponentSetting.I0
    rw [e1, e2, ptsIntegral_scale]
  unfold topMUc ComponentSetting.topN
  rw [← sub_div, div_le_iff₀ (by positivity)]
  refine h.trans (le_of_eq ?_)
  rw [hI0, inv_pow]
  have hqn : (q : ℝ) ^ D.n ≠ 0 := by positivity
  field_simp
  ring

end GroundTheory.Heights₂.Heights.LowerBoundFree
