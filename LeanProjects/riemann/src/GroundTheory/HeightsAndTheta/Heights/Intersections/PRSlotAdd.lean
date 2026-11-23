import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSupp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.AMixSt
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsWellDefined
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo MeasureTheory Filter
open scoped Topology ContDiff

noncomputable section

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

omit [∀ k, Fintype (ι k)] in

theorem isOpen_blockNonzero : IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  have e : {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} = ⋂ k, ⋃ i, {z | z ⟨k, i⟩ ≠ 0} := by
    ext z; simp
  rw [e]
  exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
    isOpen_ne_fun (continuous_apply _) continuous_const

theorem contDiffAt_log_metric {D : ℕ} {A : HermLine ι} (hA : IsSmoothHerm A)
    {γ : (Fin D → ℂ) → (Σ k, ι k) → ℂ} {y : Fin D → ℂ}
    (hγ : ∀ᶠ y' in 𝓝 y, DifferentiableAt ℂ γ y') (hy : ∀ k, ∃ i, γ y ⟨k, i⟩ ≠ 0) :
    ContDiffAt ℝ 2 (fun y' => Real.log (A.h (γ y'))) y := by
  obtain ⟨U, hU, hUo, hyU⟩ := eventually_nhds_iff.mp hγ
  have hdU : DifferentiableOn ℂ γ U := fun y' h => (hU y' h).differentiableWithinAt
  have hc : ContDiffAt ℝ ∞ γ y :=
    ((ReciprocityTheory.ChartRestriction.DS.S7.cca_contDiffOn hUo hdU).contDiffAt (hUo.mem_nhds hyU)).restrict_scalars ℝ
  have hρ : ContDiffAt ℝ ∞ A.h (γ y) := hA.contDiffAt (isOpen_blockNonzero.mem_nhds hy)
  exact_mod_cast (contDiffAt_infty.mp ((hρ.comp y hc).log (A.pos _ hy).ne')) 2

theorem cxHessian_pot_snoc {n : ℕ} (L : Fin n → HermLine ι) (A X : HermLine ι)
    (γ : (Fin (n + 1) → ℂ) → (Σ k, ι k) → ℂ) (y : Fin (n + 1) → ℂ) :
    (fun k => cxHessian (fun y' => pot (Fin.snoc L X) k (γ y')) y) =
      Function.update (fun k => cxHessian (fun y' => pot (Fin.snoc L A) k (γ y')) y) (Fin.last n)
        (cxHessian (fun y' => Real.log (X.h (γ y'))) y) := by
  funext k
  rcases Fin.eq_castSucc_or_eq_last k with ⟨j, rfl⟩ | rfl
  · rw [Function.update_of_ne (Fin.castSucc_ne_last j)]
    simp only [pot, Fin.snoc_castSucc]
  · rw [Function.update_self]
    simp only [pot, Fin.snoc_last]

theorem maDensity_snoc_tensor {n : ℕ} (L : Fin n → HermLine ι) {A C : HermLine ι}
    (hA : IsSmoothHerm A) (hC : IsSmoothHerm C) {γ : (Fin (n + 1) → ℂ) → (Σ k, ι k) → ℂ}
    {y : Fin (n + 1) → ℂ}
    (hγ : ∀ᶠ y' in 𝓝 y, DifferentiableAt ℂ γ y' ∧ ∀ k, ∃ i, γ y' ⟨k, i⟩ ≠ 0) :
    maDensity (fun j y' => pot (Fin.snoc L (A.tensor C)) j (γ y')) y =
      maDensity (fun j y' => pot (Fin.snoc L A) j (γ y')) y +
        maDensity (fun j y' => pot (Fin.snoc L C) j (γ y')) y := by
  have hev := hγ.eventually_nhds
  have ha : ∀ᶠ y' in 𝓝 y, ContDiffAt ℝ 2 (fun y'' => Real.log (A.h (γ y''))) y' := by
    filter_upwards [hev] with y' hy'
    exact contDiffAt_log_metric hA (hy'.mono fun _ h => h.1) hy'.self_of_nhds.2
  have hc : ∀ᶠ y' in 𝓝 y, ContDiffAt ℝ 2 (fun y'' => Real.log (C.h (γ y''))) y' := by
    filter_upwards [hev] with y' hy'
    exact contDiffAt_log_metric hC (hy'.mono fun _ h => h.1) hy'.self_of_nhds.2
  have hψ : (fun y' => Real.log ((A.tensor C).h (γ y'))) =ᶠ[𝓝 y]
      fun y' => 1 * Real.log (A.h (γ y')) + 1 * Real.log (C.h (γ y')) := by
    filter_upwards [hγ] with y' hy'
    rw [one_mul, one_mul]
    exact Real.log_mul (A.pos _ hy'.2).ne' (C.pos _ hy'.2).ne'
  have hH := ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.gaamix_cxHessian_comb 1 1 ha hc hψ
  simp only [Complex.ofReal_one, one_smul] at hH
  unfold maDensity
  rw [cxHessian_pot_snoc L A (A.tensor C), cxHessian_pot_snoc L A C, hH]
  have hm := ReciprocityTheory.AnForm.A.mdisc_update_add
    (fun k => cxHessian (fun y' => pot (Fin.snoc L A) k (γ y')) y) (Fin.last n)
    (cxHessian (fun y' => Real.log (A.h (γ y'))) y) (cxHessian (fun y' => Real.log (C.h (γ y'))) y)
  change mixedDisc _ = mixedDisc _ + mixedDisc _ at hm
  rw [← cxHessian_pot_snoc L A A γ y] at hm
  rw [hm, Complex.add_re, mul_add]

theorem sheetDensity_snoc_tensor (P : Ideal (MRing ι)) {n : ℕ}
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1 + 1) → ℂ)) (L : Fin n → HermLine ι)
    {A C : HermLine ι} (hA : IsSmoothHerm A) (hC : IsSmoothHerm C) (g : ((Σ k, ι k) → ℂ) → ℝ)
    (y : Fin (n + 1) → ℂ) (w : ((k : K) → ι k) → ℂ) :
    sheetDensity P Ψ (pot (Fin.snoc L (A.tensor C))) g y w =
      sheetDensity P Ψ (pot (Fin.snoc L A)) g y w + sheetDensity P Ψ (pot (Fin.snoc L C)) g y w := by
  unfold sheetDensity
  by_cases h : ∃ γ, IsSheet P Ψ y w γ
  · simp only [dif_pos h]
    have hγ : ∀ᶠ y' in 𝓝 y, DifferentiableAt ℂ h.choose y' ∧ ∀ k, ∃ i, h.choose y' ⟨k, i⟩ ≠ 0 := by
      filter_upwards [h.choose_spec.2] with y' hy'
      exact ⟨hy'.1, hy'.2.1.1⟩
    rw [maDensity_snoc_tensor L hA hC hγ, mul_add]
  · simp only [dif_neg h, add_zero]

theorem arInt_snoc_tensor (hFF : FibreFiniteStatement) (hInt : PtsIntegrableStatement)
    {P : Ideal (MRing ι)} {n : ℕ} (L : Fin n → HermLine ι) {A C B : HermLine ι} {s : MRing ι}
    (hP : IsArithVar P (n + 2)) (hL : ∀ j, IsSmoothHerm (L j)) (hA : IsSmoothHerm A)
    (hC : IsSmoothHerm C) (hB : IsSmoothHerm B) (hs : IsSectionOn P B s) :
    arInt P s B (Fin.snoc L (A.tensor C)) =
      arInt P s B (Fin.snoc L A) + arInt P s B (Fin.snoc L C) := by
  change ptsIntegral P (pot (Fin.snoc L (A.tensor C))) (logNorm B s) =
    ptsIntegral P (pot (Fin.snoc L A)) (logNorm B s) + ptsIntegral P (pot (Fin.snoc L C)) (logNorm B s)
  unfold ptsIntegral
  by_cases hΨ : ∃ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1 + 1) → ℂ), IsGoodProj P Ψ
  · rw [dif_pos hΨ, dif_pos hΨ, dif_pos hΨ]
    have hsm : ∀ X : HermLine ι, IsSmoothHerm X →
        ∀ j, IsSmoothHerm ((Fin.snoc L X : Fin (n + 1) → HermLine ι) j) := by
      intro X hX j
      rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl
      · simpa only [Fin.snoc_castSucc] using hL j
      · simpa only [Fin.snoc_last] using hX
    have iA := hInt K ι P (n + 1) hΨ.choose (Fin.snoc L A) B s hP hΨ.choose_spec (hsm A hA) hB hs
    have iC := hInt K ι P (n + 1) hΨ.choose (Fin.snoc L C) B s hP hΨ.choose_spec (hsm C hC) hB hs
    unfold ptsIntegralAt
    rw [← integral_add iA iC]
    congr 1
    funext y
    rw [← finsum_mem_add_distrib (hFF K ι P (n + 1) hΨ.choose hP hΨ.choose_spec y)]
    exact finsum_mem_congr rfl fun w _ => sheetDensity_snoc_tensor P hΨ.choose L hA hC _ y w
  · rw [dif_neg hΨ, dif_neg hΨ, dif_neg hΨ, add_zero]

omit [∀ k, Fintype (ι k)] in

theorem geoNum_snoc_tensor {n : ℕ} (L : Fin n → HermLine ι) (A C : HermLine ι) (W : Ideal (MRing ι)) :
    geoNum (n + 1) W (fun j => ((Fin.snoc L (A.tensor C) : Fin (n + 1) → HermLine ι) j).a) =
      geoNum (n + 1) W (fun j => ((Fin.snoc L A : Fin (n + 1) → HermLine ι) j).a) + geoNum (n + 1) W (fun j => ((Fin.snoc L C : Fin (n + 1) → HermLine ι) j).a) := by
  have hi : ∀ X : HermLine ι, Fin.init (fun j => ((Fin.snoc L X : Fin (n + 1) → HermLine ι) j).a) = fun j => (L j).a := by
    intro X; funext j; simp only [Fin.init, Fin.snoc_castSucc]
  simp only [geoNum]
  split_ifs with h
  · simp only [hi, Fin.snoc_last, HermLine.tensor, Pi.add_apply, ← Finset.sum_add_distrib, add_mul]
  · simp

open Classical in

theorem RPositionAdd.proof (hFF : FibreFiniteStatement) (hInt : PtsIntegrableStatement) :
    RPositionAdd.Statement := by
  intro K _ ι _ I P n L A C B s hI hP hL hA hC hB hs
  let term : HermLine ι → Ideal (MRing ι) → ℝ := fun X W =>
    (multAt (P ⊔ Ideal.span {s}) W : ℝ) *
      (if IsHorizontal W then I W (n + 1) (Fin.snoc L X)
        else (geoNum (n + 1) W (fun j => ((Fin.snoc L X : Fin (n + 1) → HermLine ι) j).a) : ℝ) * Real.log (charOf W))
  have e : ∀ X, recR I P (Fin.snoc L X) B s =
      (∑ᶠ W ∈ divSupp P s, term X W) - arInt P s B (Fin.snoc L X) := fun X => rfl
  have key : ∀ W ∈ divSupp P s, term (A.tensor C) W = term A W + term C W := by
    intro W hW
    simp only [term]
    split_ifs with hh
    · rw [hI W L A C ((divSuppArith K ι P (n + 1) B s W hP hs hW).1 hh) hL hA hC]; ring
    · rw [geoNum_snoc_tensor L A C W]; push_cast; ring
  rw [e, e, e, finsum_mem_congr rfl key, finsum_mem_add_distrib (divSupp_finite P s),
    arInt_snoc_tensor hFF hInt L hP hL hA hC hB hs]
  ring

end

end GroundTheory.Heights₂.Heights.Inter
