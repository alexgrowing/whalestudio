import Formalism.HermitianCurvature.HermitianCurvatureProofs.DminStarPd

open Matrix Set
open scoped ComplexConjugate ContDiff Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.AdmissibleLieWords

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

lemma ckOn_of_lss {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : Mat k r → E} {S : Set (Mat k r)}
    (h : LSS f S) (m : ℕ∞) : CkOn m S f := by
  intro g hg
  obtain ⟨f', hf', V, hV, hgV, hfe⟩ := h g hg
  refine ⟨V, f', hV, hgV, (hf'.of_le ?_).contDiffOn, fun g' hg' hG => hfe g' hG hg'⟩
  exact WithTop.coe_le_coe.mpr le_top

section fac

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

lemma ubl_epart (D : RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → Mat k r → C6.EndH Wp Wq)
    (hfib : ∀ j, C6.FibBound D (fib j)) {ε : ℝ} (hε : 0 < ε) {S : Set (Mat k r)}
    (hS : ∀ g ∈ S, g ∈ GV k r ∧ ε ≤ Gf k r D.z D.z' g) (n : ℕ) :
    ∀ es : List (Fin nf × List (Mat k r)), (∀ e ∈ es, ∀ X ∈ e.2, inLie k r X) →
      UBL (C6.Epart fib es) S n (3 * (r + 1) * (es.map fun e => e.2.length).sum) (3 * (r + 1)) := by
  have hSG : S ⊆ GV k r := fun g hg => (hS g hg).1
  intro es
  induction es with
  | nil =>
    intro _
    have e0 : C6.Epart fib ([] : List (Fin nf × List (Mat k r))) = fun _ => 1 := by
      funext g
      simp [C6.Epart]
    rw [e0]
    simpa using ubl_const (1 : C6.EndH Wp Wq) hSG n (3 * (r + 1))
  | cons e es ih =>
    intro hes
    have hA := ubl_fib D (fib e.1) (hfib e.1) hε hS e.2 (hes e (by simp)) n
    have hB := ih (fun e' he' => hes e' (List.mem_cons_of_mem _ he'))
    have hL := ubl_clm ((ContinuousLinearMap.mul ℂ (C6.EndH Wp Wq)).restrictScalars ℝ) hSG hA
    have hAB := ubl_app hSG hL hB
    have e1 : C6.Epart fib (e :: es) =
        fun g => ((ContinuousLinearMap.mul ℂ (C6.EndH Wp Wq)).restrictScalars ℝ
          (Rw e.2 (fib e.1) g)) (C6.Epart fib es g) := by
      funext g
      simp [C6.Epart]
    rw [e1]
    convert hAB using 2
    simp only [List.map_cons, List.sum_cons]
    ring

lemma ubl_coefP (D : RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → Mat k r → C6.EndH Wp Wq)
    (hfib : ∀ j, C6.FibBound D (fib j)) (L : Finset (Fin (r + 2))) {κ : ℕ} (P : Mat k r → ℂ)
    (a b : Fin (r + 2) → ℕ) (c : ℕ) (es : List (Fin nf × List (Mat k r))) (hP : U.IsPolyDeg κ P)
    (hab : ∀ l, l ∉ L → l ≠ Fin.last (r + 1) → a l = 0 ∧ b l = 0) (hes : ∀ e ∈ es, ∀ X ∈ e.2, inLie k r X)
    {ε : ℝ} (hε : 0 < ε) {S : Set (Mat k r)} (hS : ∀ g ∈ S, g ∈ GV k r ∧ ε ≤ Gf k r D.z D.z' g)
    {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hSD : ∀ g ∈ S, ∀ l, (l ∈ L ∨ l = Fin.last (r + 1)) → c₀ ≤ Complex.normSq (Dmin k r D.z D.z' g l))
    (hSGf : ∀ g ∈ S, c₀ ≤ Complex.normSq ((Gf k r D.z D.z' g : ℝ) : ℂ)) (n : ℕ) :
    UBL (fun g => (P g * C6.monoM D a b c g) • C6.Epart fib es g) S n
      (κ + 3 * (r + 1) * (es.map fun e => e.2.length).sum) (3 * (r + 1)) := by
  have hSG : S ⊆ GV k r := fun g hg => (hS g hg).1
  have hP' := ubl_poly hP S hSG n (3 * (r + 1))
  have hM := ubl_mono hSG (ubl_monoM D L a b c hab hSG hc₀ hSD hSGf n) le_rfl
    (show 2 * r + 2 ≤ 3 * (r + 1) by omega)
  have hPM := ubl_mul hSG hP' hM
  have hE := ubl_epart D fib hfib hε hS n es hes
  let Lm : ℂ →L[ℝ] (C6.EndH Wp Wq →L[ℂ] C6.EndH Wp Wq) :=
    (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℂ ℂ)
      (ContinuousLinearMap.id ℂ (C6.EndH Wp Wq))).restrictScalars ℝ
  have hA := ubl_clm Lm hSG hPM
  have hAE := ubl_app hSG hA hE
  have e1 : (fun g => (P g * C6.monoM D a b c g) • C6.Epart fib es g) =
      fun g => Lm (P g * C6.monoM D a b c g) (C6.Epart fib es g) := by
    funext g
    simp [Lm]
  rw [e1]
  simpa using hAE

end fac

section cut

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

private lemma contDiff_of_isPolyDeg {N κ : ℕ} {P : Matrix (Fin N) (Fin N) ℂ → ℂ} (hP : U.IsPolyDeg κ P) :
    ContDiff ℝ ∞ P := by
  obtain ⟨q, -, hq⟩ := hP
  rw [show P = fun g => MvPolynomial.eval (Sum.elim (fun x => g x.1 x.2)
    (fun x => star (g x.1 x.2))) q from funext hq]
  clear hq
  induction q using MvPolynomial.induction_on with
  | C a => simpa using contDiff_const
  | add p q hp hq => simpa only [map_add] using hp.add hq
  | mul_X p i hp =>
    simp only [map_mul, MvPolynomial.eval_X]
    refine hp.mul ?_
    rcases i with x | x
    · exact contDiff_apply_apply ℝ ℂ x.1 x.2
    · exact Complex.conjCLE.contDiff.comp (contDiff_apply_apply ℝ ℂ x.1 x.2)

private lemma exists_bound_iteratedFDeriv_cutoff_normSq {χ₀ : ℝ → ℝ} (hχ : C6.IsCut0 χ₀) (de : ℝ) (j : ℕ) :
    ∃ B : ℝ, ∀ y : ℂ,
      ‖iteratedFDeriv ℝ j (fun y : ℂ => ((χ₀ (Complex.normSq y / de) : ℝ) : ℂ)) y‖ ≤ B := by
  obtain ⟨hs, ⟨δ, hδ, h0⟩, h1⟩ := hχ
  set Φ : ℂ → ℂ := fun y => ((χ₀ (Complex.normSq y / de) : ℝ) : ℂ) with hΦdef
  have hns : ContDiff ℝ ∞ (fun y : ℂ => Complex.normSq y) := by
    simp only [Complex.normSq_apply]
    exact (Complex.reCLM.contDiff.mul Complex.reCLM.contDiff).add
      (Complex.imCLM.contDiff.mul Complex.imCLM.contDiff)
  have hΦ : ContDiff ℝ ∞ Φ := Complex.ofRealCLM.contDiff.comp (hs.comp (hns.div_const de))
  have hc : Continuous (iteratedFDeriv ℝ j Φ) :=
    hΦ.continuous_iteratedFDeriv (WithTop.coe_le_coe.mpr (by exact_mod_cast le_top))
  have hconst : ∀ (c x y : ℂ), iteratedFDeriv ℝ j (fun _ : ℂ => c) x =
      iteratedFDeriv ℝ j (fun _ : ℂ => c) y := by
    intro c x y
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp [iteratedFDeriv_zero_eq_comp]
    · rw [iteratedFDeriv_const_of_ne hj.ne']
      rfl
  obtain ⟨c, R, hR0, hloc⟩ : ∃ c : ℂ, ∃ R : ℝ, 0 ≤ R ∧
      ∀ y : ℂ, R < ‖y‖ → Φ =ᶠ[nhds y] fun _ => c := by
    rcases le_or_gt de 0 with hde | hde
    · refine ⟨0, 0, le_rfl, fun y _ => Filter.Eventually.of_forall fun z => ?_⟩
      have hz : Complex.normSq z / de ≤ 0 :=
        div_nonpos_of_nonneg_of_nonpos (Complex.normSq_nonneg z) hde
      show ((χ₀ (Complex.normSq z / de) : ℝ) : ℂ) = 0
      rw [h0 _ (by linarith)]
      simp
    · refine ⟨1, de + 1, by linarith, fun y hy => ?_⟩
      have hopen : IsOpen {z : ℂ | de + 1 < ‖z‖} := isOpen_lt continuous_const continuous_norm
      filter_upwards [hopen.mem_nhds hy] with z hz
      have hz' : de + 1 < ‖z‖ := hz
      have hn : de ≤ Complex.normSq z := by
        rw [Complex.normSq_eq_norm_sq]
        nlinarith [norm_nonneg z]
      have h1' : 1 ≤ Complex.normSq z / de := by
        rw [le_div_iff₀ hde]
        linarith
      show ((χ₀ (Complex.normSq z / de) : ℝ) : ℂ) = 1
      rw [h1 _ h1']
      simp
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : ℂ) (R + 1)).exists_bound_of_continuousOn
    hc.continuousOn
  have y0n : ‖((R + 1 : ℝ) : ℂ)‖ = R + 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  refine ⟨B, fun y => ?_⟩
  rcases le_or_gt ‖y‖ (R + 1) with hy | hy
  · exact hB y (by rw [mem_closedBall_zero_iff]; exact hy)
  · have e1 := ((hloc y (by linarith)).iteratedFDeriv (𝕜 := ℝ) j).eq_of_nhds
    have e2 := ((hloc ((R + 1 : ℝ) : ℂ) (by rw [y0n]; linarith)).iteratedFDeriv
      (𝕜 := ℝ) j).eq_of_nhds
    rw [e1, hconst c y ((R + 1 : ℝ) : ℂ), ← e2]
    exact hB _ (by rw [mem_closedBall_zero_iff, y0n])

lemma ubl_chi (D : RealPlaceData k r Wp Wq) {χ₀ : ℝ → ℝ} (hχ : C6.IsCut0 χ₀) (de : ℝ) (L : Finset (Fin (r + 2)))
    (n : ℕ) : UBL (fun g => ((C6.chiAll D χ₀ de L g : ℝ) : ℂ)) (GV k r) n 0 (2 * r + 2) := by
  have hSG : GV k r ⊆ GV k r := subset_rfl
  have e0 : (fun g => ((C6.chiAll D χ₀ de L g : ℝ) : ℂ)) =
      fun g => ∏ l ∈ L, ((χ₀ (Complex.normSq (Dmin k r D.z D.z' g l) / de) : ℝ) : ℂ) := by
    funext g
    simp [C6.chiAll]
  rw [e0]
  apply ubl_prod hSG L
  intro l _
  obtain ⟨C, hC0, hC⟩ := (ubl_poly (dmin_pd k r D.z D.z' l) (GV k r) hSG n 0).1
  have hns : ContDiff ℝ ∞ (fun y : ℂ => Complex.normSq y) := by
    simp only [Complex.normSq_apply]
    exact (Complex.reCLM.contDiff.mul Complex.reCLM.contDiff).add
      (Complex.imCLM.contDiff.mul Complex.imCLM.contDiff)
  refine ubl_fdb (fun g => Dmin k r D.z D.z' g l) (contDiff_of_isPolyDeg (dmin_pd k r D.z D.z' l)) (GV k r) hSG
    Set.univ (fun _ _ => trivial) (2 * r + 2) n C ?_
    (fun y : ℂ => ((χ₀ (Complex.normSq y / de) : ℝ) : ℂ))
    (Complex.ofRealCLM.contDiff.comp (hχ.1.comp (hns.div_const de))) (fun j => ?_)
  · intro w hw hne g hg
    refine (hC w hw g hg).trans ?_
    apply mul_le_mul_of_nonneg_left _ hC0
    apply pow_le_pow_right₀ (gN_ge_one hg)
    have hl : 1 ≤ w.length := by
      cases w with
      | nil => exact absurd rfl hne
      | cons _ _ => simp
    simpa using Nat.le_mul_of_pos_right (2 * r + 2) hl
  · obtain ⟨B, hB⟩ := exists_bound_iteratedFDeriv_cutoff_normSq hχ de j
    exact ⟨B, fun y _ => hB y⟩

end cut

end Formalism.FourierDecayAlt.P.AdmissibleLieWords
