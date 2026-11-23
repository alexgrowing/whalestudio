import Mathlib
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
import Development.AbelianVarietyTheory.Definitions.Divisors.FirstChernLeviEqConstant

open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.WeightThresholdDefs Filter Topology Classical
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.FlagPoly GlobalTheory.FlagAr GlobalTheory.Mean4 GlobalTheory.Mean4O

noncomputable section

namespace GlobalTheory.LeviOnly

theorem levi_polar {D : ℕ} {f : (Fin D → ℂ) → ℝ} {z : Fin D → ℂ} (hf : ContDiffAt ℝ 2 f z) (a b : Fin D → ℂ) :
    fderiv ℝ (fderiv ℝ f) z a b + fderiv ℝ (fderiv ℝ f) z (Complex.I • a) (Complex.I • b) =
      2 * (levi f z (a + b) - levi f z a - levi f z b) := by
  have hs : IsSymmSndFDerivAt ℝ f z := hf.isSymmSndFDerivAt (by simp)
  unfold levi
  simp only [smul_add, map_add, ContinuousLinearMap.add_apply]
  rw [hs b a, hs (Complex.I • b) (Complex.I • a)]
  ring

theorem hessC_eq_of_levi {D : ℕ} {f g : (Fin D → ℂ) → ℝ} {z : Fin D → ℂ} (hf : ContDiffAt ℝ 2 f z)
    (hg : ContDiffAt ℝ 2 g z) (h : ∀ w, levi f z w = levi g z w) : hessC f z = hessC g z := by
  have key : ∀ a b : Fin D → ℂ,
      fderiv ℝ (fderiv ℝ f) z a b + fderiv ℝ (fderiv ℝ f) z (Complex.I • a) (Complex.I • b) =
      fderiv ℝ (fderiv ℝ g) z a b + fderiv ℝ (fderiv ℝ g) z (Complex.I • a) (Complex.I • b) := by
    intro a b
    rw [levi_polar hf, levi_polar hg, h, h, h]
  have key2 : ∀ a b : Fin D → ℂ,
      fderiv ℝ (fderiv ℝ f) z a (Complex.I • b) - fderiv ℝ (fderiv ℝ f) z (Complex.I • a) b =
      fderiv ℝ (fderiv ℝ g) z a (Complex.I • b) - fderiv ℝ (fderiv ℝ g) z (Complex.I • a) b := by
    intro a b
    have h1 := key a (Complex.I • b)
    have h2 : Complex.I • Complex.I • b = -b := by rw [smul_smul, Complex.I_mul_I]; simp
    rw [h2, map_neg, map_neg] at h1
    linarith
  funext i j
  simp only [hessC]
  rw [key, key2]

variable {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X}

theorem pot_two {P : LocPot X} (hP : IsPotential A P) (x : X) (j : Fin A.n) {y : Fin e → ℂ}
    (hy : y ∈ (A.chart j).target) (hx : (A.chart j).symm y ∈ P.U x) :
    ContDiffAt ℝ 2 (P.φ x ∘ (A.chart j).symm) y := by
  have ho : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' P.U x) :=
    (A.chart j).isOpen_inter_preimage_symm (P.isOpen_U x)
  exact ((hP.1 x j).contDiffAt (ho.mem_nhds ⟨hy, hx⟩)).of_le (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))

theorem levi_base {P : LocPot X} (hP : IsPotential A P) (x : X) (j : Fin A.n) {y : Fin e → ℂ}
    (hy : y ∈ (A.chart j).target) (hx : (A.chart j).symm y ∈ P.U x) (w : Fin e → ℂ) :
    levi (P.φ x ∘ (A.chart j).symm) y w = leviAt A P j y w := by
  obtain ⟨W, hW, hyW, G, hG, hGe⟩ := hP.2 x ((A.chart j).symm y) ((A.chart j).symm y) ⟨hx, P.mem_U _⟩
  have hGa : AnalyticAt ℂ (G ∘ (A.chart j).symm) y := hG j y ⟨hy, hyW⟩
  have ho : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (W ∩ P.U x ∩ P.U ((A.chart j).symm y))) :=
    (A.chart j).isOpen_inter_preimage_symm ((hW.inter (P.isOpen_U x)).inter (P.isOpen_U _))
  have hev : (P.φ x ∘ (A.chart j).symm) =ᶠ[𝓝 y] fun v =>
      (P.φ ((A.chart j).symm y) ∘ (A.chart j).symm) v + 1 * ((G ∘ (A.chart j).symm) v).re := by
    filter_upwards [ho.mem_nhds ⟨hy, ⟨hyW, hx⟩, P.mem_U _⟩] with v hv
    have := hGe _ hv.2
    simp only [Function.comp_apply]
    linarith
  have hRe : ContDiffAt ℝ 2 (fun v => ((G ∘ (A.chart j).symm) v).re) y :=
    Complex.reCLM.contDiff.contDiffAt.comp y (hGa.restrictScalars (𝕜 := ℝ)).contDiffAt
  rw [levi_congr hev, levi_add_smul 1 (pot_two hP _ j hy (P.mem_U _)) hRe, levi_re_analytic hGa]
  simp [leviAt]

theorem isPsh_of_leviEq {P Q : LocPot X} (hQ : IsPotential A Q)
    (h : ∀ j, ∀ y ∈ (A.chart j).target, ∀ w, leviAt A P j y w = leviAt A Q j y w) (hp : IsPsh A P) : IsPsh A Q := by
  intro x j y hy w
  rw [levi_base hQ x j hy.1 hy.2, ← h j y hy.1 w]
  exact hp _ j y ⟨hy.1, P.mem_U _⟩ w

theorem locDens_eq {P Q : Fin e → LocPot X} (hP : ∀ i, IsPotential A (P i)) (hQ : ∀ i, IsPotential A (Q i))
    (h : ∀ i, LeviEq A (P i) (Q i)) (j : Fin A.n) {y : Fin e → ℂ} (hy : y ∈ (A.chart j).target) :
    locDens A P j y = locDens A Q j y := by
  have hH : (fun k => hessC (fun y' => (P k).φ ((A.chart j).symm y) ((A.chart j).symm y')) y) =
      fun k => hessC (fun y' => (Q k).φ ((A.chart j).symm y) ((A.chart j).symm y')) y := by
    funext k
    exact hessC_eq_of_levi (pot_two (hP k) _ j hy ((P k).mem_U _)) (pot_two (hQ k) _ j hy ((Q k).mem_U _))
      (h k j y hy)
  unfold locDens maDens
  rw [hH]

theorem mInt_eq_of_leviEq : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (P Q : Fin e → LocPot X) (g : X → ℝ), (∀ i, IsPotential A (P i)) → (∀ i, IsPotential A (Q i)) → (∀ i, LeviEq A (P i) (Q i)) → mInt A P g = mInt A Q g ∧ ∀ i, (IsPsh A (P i) ↔ IsPsh A (Q i)) := by
  intro e X _ _ _ A P Q g hP hQ h
  refine ⟨?_, fun i => ⟨isPsh_of_leviEq (hQ i) (h i),
    isPsh_of_leviEq (hP i) (fun j y hy w => (h i j y hy w).symm)⟩⟩
  unfold mInt
  split_ifs with hn
  · unfold integralWith
    refine Finset.sum_congr rfl fun j _ => ?_
    refine MeasureTheory.setIntegral_congr_fun (A.chart j).open_target.measurableSet fun y hy => ?_
    simp only [locDens_eq hP hQ h j hy]
  · rfl

end GlobalTheory.LeviOnly
