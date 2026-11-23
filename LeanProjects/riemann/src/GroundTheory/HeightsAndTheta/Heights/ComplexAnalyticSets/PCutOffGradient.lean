import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCutOffGradient
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLogLogCutHess
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFibreBound
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.MdiscSt
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.CovLog
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A Filter Topology

noncomputable section

variable {n d : ℕ}

theorem logLogCut_mem_Icc {m : ℕ} (Q : MvPolynomial (Fin m) ℂ) (k : ℕ) (y : Fin m → ℂ) :
    logLogCut Q k y ∈ Set.Icc (0 : ℝ) 1 := by
  unfold logLogCut cutStep
  split_ifs
  · simp
  · simp
  · exact ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

theorem comp_sheet_eventuallyEq {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    {x : Fin n → ℂ} {s : (Fin d → ℂ) → Fin n → ℂ} (hs : IsSheetAt J A x s) (g : (Fin d → ℂ) → ℝ) :
    (fun w => g (A *ᵥ s w)) =ᶠ[𝓝 (A *ᵥ x)] g := by
  obtain ⟨U, hU, hxU, -, -, hsec, -⟩ := hs
  filter_upwards [hU.mem_nhds hxU] with w hw
  rw [(hsec w hw).1]

theorem maDens_cons_of_hessC_eq_smul {D : ℕ} (f g : (Fin (D + 1) → ℂ) → ℝ)
    (ψ : Fin D → (Fin (D + 1) → ℂ) → ℝ) (y : Fin (D + 1) → ℂ) (c : ℝ)
    (h : hessC f y = (c : ℂ) • hessC g y) :
    maDens (Fin.cons f ψ) y = c * maDens (Fin.cons g ψ) y := by
  have e : ∀ u : (Fin (D + 1) → ℂ) → ℝ,
      (fun k => hessC ((Fin.cons u ψ : Fin (D + 1) → (Fin (D + 1) → ℂ) → ℝ) k) y) =
        Fin.cons (hessC u y) (fun k => hessC (ψ k) y) := fun u => by
    funext k; exact Fin.cases rfl (fun i => rfl) k
  have hm := mdisc_update_smul
    (Fin.cons (hessC g y) (fun k => hessC (ψ k) y) : Fin (D + 1) → Matrix (Fin (D + 1)) (Fin (D + 1)) ℂ)
    0 (c : ℂ) (hessC g y)
  rw [Fin.update_cons_zero, Fin.update_cons_zero] at hm
  unfold maDens
  rw [e, e, h, hm, Complex.re_ofReal_mul]
  ring

theorem vecCons_comp {D : ℕ} (f : (Fin n → ℂ) → ℝ) (φ : Fin D → (Fin n → ℂ) → ℝ)
    (s : (Fin (D + 1) → ℂ) → Fin n → ℂ) :
    (fun k => (vecCons f φ : Fin (D + 1) → (Fin n → ℂ) → ℝ) k ∘ s) = Fin.cons (f ∘ s) (fun k => φ k ∘ s) := by
  funext k; exact Fin.cases rfl (fun i => rfl) k

theorem sheetSum_le_mul {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    {y : Fin d → ℂ} (hfin : (fibre J A y).Finite) (c : ℝ)
    (F G : (Fin n → ℂ) → ((Fin d → ℂ) → Fin n → ℂ) → ℝ)
    (h : ∀ x ∈ fibre J A y, ∀ s, IsSheetAt J A x s → F x s ≤ c * G x s) :
    sheetSum J A F y ≤ c * sheetSum J A G y := by
  classical
  unfold sheetSum
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.mul_sum]
  refine Finset.sum_le_sum fun x hx => ?_
  rw [Set.Finite.mem_toFinset] at hx
  split_ifs with hs
  · exact h x hx _ hs.choose_spec
  · simp

theorem term_le_of_hessC {D : ℕ} {X : Type*} (B : Set X) (w t : X → ℝ) (x : X)
    (hw : |w x| ≤ 1) (hwB : x ∉ B → w x = 0) (ht : 0 ≤ t x) (f g : (Fin (D + 1) → ℂ) → ℝ)
    (ψ : Fin D → (Fin (D + 1) → ℂ) → ℝ) (y : Fin (D + 1) → ℂ) {c e : ℝ}
    (h : hessC f y = (e : ℂ) • hessC g y) (he : |e| ≤ c * t x) :
    |w x * maDens (Fin.cons f ψ) y| ≤ c * |B.indicator t x * maDens (Fin.cons g ψ) y| := by
  rw [maDens_cons_of_hessC_eq_smul f g ψ y e h]
  by_cases hx : x ∈ B
  · rw [Set.indicator_of_mem hx, abs_mul, abs_mul, abs_mul, abs_of_nonneg ht]
    have hM := abs_nonneg (maDens (Fin.cons g ψ) y)
    calc |w x| * (|e| * |maDens (Fin.cons g ψ) y|) ≤ 1 * (c * t x * |maDens (Fin.cons g ψ) y|) :=
          mul_le_mul hw (mul_le_mul_of_nonneg_right he hM) (by positivity) zero_le_one
      _ = c * (t x * |maDens (Fin.cons g ψ) y|) := by ring
  · rw [hwB hx, zero_mul, abs_zero, Set.indicator_of_notMem hx, zero_mul, abs_zero, mul_zero]

theorem CutOffGradient.proof (hH : LogLogCutHess.Statement) : CutOffGradient.Statement := by
  obtain ⟨K, hK0, hK⟩ := hH
  refine ⟨K, fun n d J A P R φ k y hJ hdim hA => ?_⟩
  have hfin := (FibreBound.proof n (d + 1) J A hJ hdim hA y).2.1
  obtain ⟨a, b, ha, hb, hHa, hHb⟩ := hK (d + 1) P k y
  have hc : 0 ≤ K / ((k : ℝ) + 1) := by positivity
  set B := Metric.closedBall (0 : Fin n → ℂ) R
  have ht : ∀ x, 0 ≤ tubeWeight P (A *ᵥ x) := fun x => by
    unfold tubeWeight; split_ifs <;> positivity

  have key : ∀ (w : (Fin n → ℂ) → ℝ) (g : (Fin (d + 1) → ℂ) → ℝ) (e : ℝ),
      (∀ x, |w x| ≤ 1) → (∀ x, x ∉ B → w x = 0) →
      hessC g y = (e : ℂ) • hessC (fun z => logAbsSq P z ^ 2 / 2) y →
      |e| ≤ K / ((k : ℝ) + 1) * tubeWeight P y →
      chartAbsDens J A w (vecCons (fun x => g (A *ᵥ x)) φ) y ≤ K / ((k : ℝ) + 1) * tubeDens J A P R φ y := by
    intro w g e hw hwB hg he
    unfold chartAbsDens tubeDens
    refine sheetSum_le_mul hfin _ _ _ fun x hx s hs => ?_
    have hy : A *ᵥ x = y := hx.2
    rw [vecCons_comp, vecCons_comp]
    refine term_le_of_hessC B w (fun x => tubeWeight P (A *ᵥ x)) x (hw x) (hwB x) (ht x) _ _ _ y ?_
      (by rw [hy]; exact he)
    rw [← hy, Function.comp_def, Function.comp_def, hessC_congr' (comp_sheet_eventuallyEq hs g),
      hessC_congr' (comp_sheet_eventuallyEq hs fun z => logAbsSq P z ^ 2 / 2), hy, hg]
  have h1 : ∀ x, |B.indicator (fun _ => (1 : ℝ)) x| ≤ 1 := fun x => by
    unfold Set.indicator; split_ifs <;> simp
  have h0 : ∀ x, x ∉ B → B.indicator (fun _ => (1 : ℝ)) x = 0 := fun x hx => Set.indicator_of_notMem hx _
  refine ⟨key _ (logLogCut P k) a h1 h0 hHa ha, key _ (fun z => logLogCut P k z ^ 2 / 2) b h1 h0 hHb hb,
    key _ (logLogCut P k) a (fun x => ?_) (fun x hx => Set.indicator_of_notMem hx _) hHa ha⟩
  unfold Set.indicator
  split_ifs
  · have hm := logLogCut_mem_Icc P k (A *ᵥ x)
    show |logLogCut P k (A *ᵥ x)| ≤ 1
    rw [abs_of_nonneg hm.1]; exact hm.2
  · simp

end

end GroundTheory.Heights₂.Heights
