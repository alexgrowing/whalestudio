import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ModelDdcForms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviFormLogPotentialFormulaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundaryPotentialSmoothOffDivisorStatement
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms MeasureTheory
open scoped ContDiff Topology

namespace GlobalTheory.PoincareGrowth

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem fderiv_sum_sub {ι : Type} [Fintype ι] (g : ι → E → ℝ) (a : ℝ) (z : E)
    (hg : ∀ i, DifferentiableAt ℝ (g i) z) :
    fderiv ℝ (fun y => ∑ i, g i y - a) z = ∑ i, fderiv ℝ (g i) z :=
  by
    have h := ((HasFDerivAt.sum (u := Finset.univ) (fun i _ => (hg i).hasFDerivAt)).sub_const a).fderiv
    simpa only [Finset.sum_apply] using h

theorem levi_congr {ι : Type} [Fintype ι] {f g : (ι → ℂ) → ℝ} {z : ι → ℂ} (h : f =ᶠ[𝓝 z] g)
    (w : ι → ℂ) : levi f z w = levi g z w := by
  simp only [levi, h.fderiv.fderiv_eq]

theorem levi_sum_sub {ι κ : Type} [Fintype ι] [Fintype κ] (g : κ → (ι → ℂ) → ℝ) (a : ℝ)
    (z w : ι → ℂ) (hg : ∀ i, ContDiffAt ℝ 2 (g i) z) :
    levi (fun y => ∑ i, g i y - a) z w = ∑ i, levi (g i) z w := by
  have hdiff : ∀ᶠ y in 𝓝 z, ∀ i, DifferentiableAt ℝ (g i) y :=
    Filter.eventually_all.2 fun i => ((hg i).eventually (by simp)).mono fun y hy =>
      hy.differentiableAt (by norm_num)
  have hev : fderiv ℝ (fun y => ∑ i, g i y - a) =ᶠ[𝓝 z] fun y => ∑ i, fderiv ℝ (g i) y := by
    filter_upwards [hdiff] with y hy
    exact fderiv_sum_sub g a y hy
  have hd : ∀ i, DifferentiableAt ℝ (fderiv ℝ (g i)) z := fun i =>
    ((hg i).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have h2 : fderiv ℝ (fun y => ∑ i, fderiv ℝ (g i) y) z = ∑ i, fderiv ℝ (fderiv ℝ (g i)) z :=
    by
      have h := (HasFDerivAt.sum (u := Finset.univ) (fun i _ => (hd i).hasFDerivAt)).fderiv
      have hfun : (fun y => ∑ i, fderiv ℝ (g i) y) = ∑ i, fderiv ℝ (g i) := by
        funext y; simp [Finset.sum_apply]
      rw [hfun]; exact h
  unfold levi
  rw [hev.fderiv_eq, h2]
  simp only [ContinuousLinearMap.sum_apply]
  rw [← Finset.sum_add_distrib, Finset.sum_div]

theorem logChain {n : ℕ} (G : (Fin n → ℂ) → ℝ) (z w : Fin n → ℂ) (hG : ContDiffAt ℝ 2 G z)
    (hpos : 0 < G z) :
    1 / Real.pi * levi (fun y => Real.log (G y)) z w =
      1 / Real.pi * levi G z w / G z -
        1 / Real.pi * ((fderiv ℝ G z w ^ 2 + fderiv ℝ G z (Complex.I • w) ^ 2) / 4) / G z ^ 2 := by
  have h := GlobalTheory.T.levi_form_log_potential_formula (m := 1) (fun _ => (0 : ℝ)) (fun _ : Fin 1 => G) (-2) z w contDiffAt_const
    (fun _ => hG) (fun _ => hpos)
  have hf : (fun y => (0 : ℝ) + -((-2 : ℝ) / 2) * ∑ _i : Fin 1, Real.log (G y)) =
      fun y => Real.log (G y) := by
    funext y; norm_num
  have h0 : levi (fun _ : Fin n → ℂ => (0 : ℝ)) z w = 0 := by simp [levi]
  rw [hf, h0] at h
  simp only [Finset.univ_unique, Finset.sum_singleton] at h
  have hpi := Real.pi_pos
  have e1 : 1 / Real.pi * levi (fun y => Real.log (G y)) z w =
      (2 / Real.pi * levi (fun y => Real.log (G y)) z w) / 2 := by ring
  rw [e1, h]; ring

set_option maxHeartbeats 1000000 in

theorem growthBounds : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (K : LocPot X) {m : ℕ} (L : Fin m → LocPot X) (s : Fin m → X → X → ℂ) (D : Fin m → Set X) (Kc C7 c : ℝ), IsPotential A K → IsBoundary A L s D → IsOpen (⋃ i, D i)ᶜ → ScalarBounds L s D → 0 < Kc → (∀ (i : Fin m) (ψ : OpenPartialHomeomorph X (Fin e → ℂ)), IsCompatChart A ψ → ∀ z ∈ ψ.target, ψ.symm z ∉ ⋃ j, D j → ∀ w, |ddcAt ψ (rComp L s i) z w| ≤ Kc * formAt ψ K z w) → (∀ ψ : OpenPartialHomeomorph X (Fin e → ℂ), IsCompatChart A ψ → ∀ z ∈ ψ.target, ∀ w, 0 ≤ formAt ψ K z w) → 0 < C7 → (∀ (i : Fin m) (ψ : OpenPartialHomeomorph X (Fin e → ℂ)), IsCompatChart A ψ → ∀ z ∈ ψ.target, ψ.symm z ∉ ⋃ j, D j → ∀ w, gradSqAt ψ (rComp L s i) z w ≤ C7 * Real.exp (rComp L s i (ψ.symm z)) * formAt ψ K z w) → 0 < c → TwoSided A K L s D c → ∃ C : ℝ, 0 < C ∧ GrowthBounds A K L s D c C := by
  intro e X _ A K m L s D Kc C7 c _hK hB hO hSB hKc hddc hapos hC7 hgrad hc hTS
  have hpi := Real.pi_pos
  have he1 : (1 : ℝ) ≤ Real.exp 1 := by simpa using Real.add_one_le_exp (1 : ℝ) |>.trans' (by norm_num)
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  refine ⟨3 + m / c + 3 * m * Kc + c * m * C7, by positivity, ?_⟩
  intro ψ hψ z hz hz' w
  obtain ⟨hri, hrr, hrle, -⟩ := hSB _ hz'

  have hev : (rTot L s ∘ ψ.symm) =ᶠ[𝓝 z]
      fun y => ∑ i, (rComp L s i ∘ ψ.symm) y - ((m : ℝ) - 1) * Real.exp 1 := by
    filter_upwards [(ψ.continuousAt_symm hz).preimage_mem_nhds (hO.mem_nhds hz')] with y hy
    exact (hSB _ hy).2.1
  have hg : ∀ i, ContDiffAt ℝ 2 (rComp L s i ∘ ψ.symm) z := fun i =>
    (GlobalTheory.T.boundary_potential_smooth_off_divisor A L s D hB i ψ hψ z hz (fun h => hz' (Set.mem_iUnion.2 ⟨i, h⟩))).of_le
      (by norm_cast)
  have hG : ContDiffAt ℝ 2 (rTot L s ∘ ψ.symm) z :=
    ((ContDiffAt.sum fun i _ => hg i).sub contDiffAt_const).congr_of_eventuallyEq hev
  have hD : fderiv ℝ (rTot L s ∘ ψ.symm) z = ∑ i, fderiv ℝ (rComp L s i ∘ ψ.symm) z := by
    rw [hev.fderiv_eq]
    exact fderiv_sum_sub _ _ z fun i => (hg i).differentiableAt (by norm_num)
  have hLv : levi (rTot L s ∘ ψ.symm) z w = ∑ i, levi (rComp L s i ∘ ψ.symm) z w := by
    rw [levi_congr hev]
    exact levi_sum_sub _ _ z w hg

  have hGe : Real.exp 1 ≤ rTot L s (ψ.symm z) := by
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm; rw [hrr]; simp
    · exact (hri ⟨0, hm⟩).trans (hrle ⟨0, hm⟩)
  set r := rTot L s (ψ.symm z) with hr
  have hrpos : 0 < r := lt_of_lt_of_le one_pos (he1.trans hGe)
  set a := formAt ψ K z w with ha
  set β := formAt ψ (poincarePot K L s c) z w with hβ
  set S := ∑ i, gradSqAt ψ (rComp L s i) z w / rComp L s i (ψ.symm z) ^ 2 with hS
  have ha0 : 0 ≤ a := hapos ψ hψ z hz w
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => div_nonneg (gradSqAt_nonneg _ _ _ _) (sq_nonneg _)
  obtain ⟨hlo, hup⟩ := hTS ψ hψ z hz hz' w
  have hcS : c * S ≤ β - a / 2 := by linarith
  have haβ : a ≤ 2 * β := by nlinarith [mul_nonneg hc.le hS0]
  have hβ0 : 0 ≤ β := by linarith

  have hgrad_r : gradSqAt ψ (rTot L s) z w ≤ m * ∑ i, gradSqAt ψ (rComp L s i) z w := by
    unfold gradSqAt
    rw [hD]
    simp only [ContinuousLinearMap.sum_apply]
    have h1 := sq_sum_le_card_mul_sum_sq (s := Finset.univ)
      (f := fun i => fderiv ℝ (rComp L s i ∘ ψ.symm) z w)
    have h2 := sq_sum_le_card_mul_sum_sq (s := Finset.univ)
      (f := fun i => fderiv ℝ (rComp L s i ∘ ψ.symm) z (Complex.I • w))
    simp only [Finset.card_univ, Fintype.card_fin] at h1 h2
    rw [← Finset.mul_sum, ← Finset.sum_div, Finset.sum_add_distrib]
    have hp : 0 ≤ 1 / Real.pi := by positivity
    nlinarith [mul_le_mul_of_nonneg_left (add_le_add h1 h2) hp]
  have hgr0 : 0 ≤ gradSqAt ψ (rTot L s) z w := gradSqAt_nonneg _ _ _ _
  have hgradS : gradSqAt ψ (rTot L s) z w / r ^ 2 ≤ m * S := by
    rw [hS, Finset.mul_sum]
    calc gradSqAt ψ (rTot L s) z w / r ^ 2
        ≤ (m * ∑ i, gradSqAt ψ (rComp L s i) z w) / r ^ 2 :=
          div_le_div_of_nonneg_right hgrad_r (sq_nonneg _)
      _ = ∑ i, m * (gradSqAt ψ (rComp L s i) z w / r ^ 2) := by
          rw [Finset.mul_sum, Finset.sum_div]; congr 1; ext i; ring
      _ ≤ _ := by
          refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ hm0
          have hi0 : 0 < rComp L s i (ψ.symm z) := lt_of_lt_of_le one_pos (he1.trans (hri i))
          exact div_le_div_of_nonneg_left (gradSqAt_nonneg _ _ _ _) (by positivity)
            (pow_le_pow_left₀ hi0.le (hrle i) 2)
  have hmS : (m : ℝ) * S ≤ m / c * β := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hc]
    nlinarith [mul_le_mul_of_nonneg_left hcS hm0]
  have h1 : gradSqAt ψ (rTot L s) z w / r ^ 2 ≤ m / c * β := hgradS.trans hmS

  have hddr : |ddcAt ψ (rTot L s) z w| ≤ m * Kc * a := by
    have : ddcAt ψ (rTot L s) z w = ∑ i, ddcAt ψ (rComp L s i) z w := by
      unfold ddcAt; rw [hLv, Finset.mul_sum]
    rw [this]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun i _ => hddc i ψ hψ z hz hz' w).trans ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring_nf; rfl

  have hlog : ddcAt ψ (fun y => Real.log (rTot L s y)) z w =
      ddcAt ψ (rTot L s) z w / r - gradSqAt ψ (rTot L s) z w / r ^ 2 := by
    unfold ddcAt gradSqAt
    exact logChain (rTot L s ∘ ψ.symm) z w hG hrpos
  have hddr' : |ddcAt ψ (rTot L s) z w| / r ≤ m * Kc * a := by
    rw [div_le_iff₀ hrpos]
    have : m * Kc * a ≤ m * Kc * a * r := by
      have := mul_nonneg (mul_nonneg hm0 hKc.le) ha0
      nlinarith [he1.trans hGe]
    linarith
  have h2 : |ddcAt ψ (fun y => Real.log (rTot L s y)) z w| ≤ (2 * m * Kc + m / c) * β := by
    rw [hlog]
    refine (abs_sub _ _).trans ?_
    rw [abs_div, abs_of_pos hrpos, abs_of_nonneg (div_nonneg hgr0 (sq_nonneg _))]
    have : (m : ℝ) * Kc * a ≤ 2 * m * Kc * β := by
      have := mul_le_mul_of_nonneg_left haβ (mul_nonneg hm0 hKc.le); linarith
    linarith

  have hSb : S ≤ m * C7 * Real.exp r * a := by
    rw [hS]
    have : ∀ i, gradSqAt ψ (rComp L s i) z w / rComp L s i (ψ.symm z) ^ 2 ≤
        C7 * Real.exp r * a := by
      intro i
      have hi1 : 1 ≤ rComp L s i (ψ.symm z) ^ 2 := one_le_pow₀ (he1.trans (hri i))
      have hg' := hgrad i ψ hψ z hz hz' w
      have hexp : Real.exp (rComp L s i (ψ.symm z)) ≤ Real.exp r := Real.exp_le_exp.2 (hrle i)
      have hq : C7 * Real.exp (rComp L s i (ψ.symm z)) * a ≤ C7 * Real.exp r * a :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp hC7.le) ha0
      calc _ ≤ gradSqAt ψ (rComp L s i) z w :=
            div_le_self (gradSqAt_nonneg _ _ _ _) hi1
        _ ≤ _ := hg'.trans hq
    refine (Finset.sum_le_sum fun i _ => this i).trans ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring_nf; rfl
  have hexp1 : 1 ≤ Real.exp r := Real.one_le_exp hrpos.le
  have h4 : β ≤ (2 + c * m * C7) * Real.exp r * a := by
    have : c * S ≤ c * (m * C7 * Real.exp r * a) := mul_le_mul_of_nonneg_left hSb hc.le
    have h2a : 2 * a ≤ 2 * Real.exp r * a := by nlinarith
    nlinarith

  have hCβ : ∀ x : ℝ, x ≤ 3 + m / c + 3 * m * Kc + c * m * C7 → 0 ≤ β →
      x * β ≤ (3 + m / c + 3 * m * Kc + c * m * C7) * β := fun x hx hb =>
    mul_le_mul_of_nonneg_right hx hb
  have hmc : 0 ≤ (m : ℝ) / c := div_nonneg hm0 hc.le
  have hmK : 0 ≤ (m : ℝ) * Kc := mul_nonneg hm0 hKc.le
  have hcmC : 0 ≤ c * m * C7 := by positivity
  have hea : 0 ≤ Real.exp r * a := mul_nonneg (Real.exp_pos _).le ha0
  refine ⟨h1.trans (hCβ _ (by linarith) hβ0), h2.trans (hCβ _ (by linarith) hβ0),
    hddr.trans (mul_le_mul_of_nonneg_right (by linarith) ha0), h4.trans ?_⟩
  have := mul_le_mul_of_nonneg_right
    (show 2 + c * m * C7 ≤ 3 + m / c + 3 * m * Kc + c * m * C7 by linarith) hea
  linarith

end GlobalTheory.PoincareGrowth
