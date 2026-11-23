import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.PiMapMulRight
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacobianCoordinates

noncomputable section

open MeasureTheory Topology
open scoped ENNReal

namespace Formalism.L2.SG.RealObj.InfCut.ProductExactness

open Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.InfCut Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates

instance sf2 : SigmaFinite ((2 : ℝ≥0∞) • (volume : Measure ℂ)) := by
  rw [← ENNReal.coe_ofNat, ← ENNReal.smul_def]
  infer_instance

section PiProd

variable {ι : Type} [Fintype ι] {α β : ι → Type} [∀ i, MeasurableSpace (α i)] [∀ i, MeasurableSpace (β i)]

def piProdEquiv : ((i : ι) → α i × β i) ≃ᵐ ((i : ι) → α i) × ((i : ι) → β i) where
  toFun x := (fun i => (x i).1, fun i => (x i).2)
  invFun p i := (p.1 i, p.2 i)
  left_inv x := rfl
  right_inv p := rfl
  measurable_toFun := (measurable_pi_lambda _ fun i => measurable_fst.comp (measurable_pi_apply i)).prodMk
    (measurable_pi_lambda _ fun i => measurable_snd.comp (measurable_pi_apply i))
  measurable_invFun := measurable_pi_lambda _ fun i =>
    ((measurable_pi_apply i).comp measurable_fst).prodMk ((measurable_pi_apply i).comp measurable_snd)

theorem measurePreserving_piProd (μ : ∀ i, Measure (α i)) (ν : ∀ i, Measure (β i)) [∀ i, SigmaFinite (μ i)]
    [∀ i, SigmaFinite (ν i)] :
    MeasurePreserving (piProdEquiv (α := α) (β := β)) (Measure.pi fun i => (μ i).prod (ν i))
      ((Measure.pi μ).prod (Measure.pi ν)) := by
  have hf := (piProdEquiv (α := α) (β := β)).measurable
  refine ⟨hf, ?_⟩
  refine (Measure.prod_eq_generateFrom generateFrom_pi generateFrom_pi isPiSystem_pi isPiSystem_pi
    (Measure.FiniteSpanningSetsIn.pi fun i => (μ i).toFiniteSpanningSetsIn)
    (Measure.FiniteSpanningSetsIn.pi fun i => (ν i).toFiniteSpanningSetsIn) ?_).symm
  rintro _ ⟨A, hA, rfl⟩ _ ⟨B, hB, rfl⟩
  have hA' : ∀ i, MeasurableSet (A i) := fun i => hA i (Set.mem_univ i)
  have hB' : ∀ i, MeasurableSet (B i) := fun i => hB i (Set.mem_univ i)

  have hpre : (piProdEquiv (α := α) (β := β)) ⁻¹' (Set.univ.pi A ×ˢ Set.univ.pi B) =
      Set.univ.pi fun i => A i ×ˢ B i := by
    ext x
    simp [piProdEquiv, Set.mem_univ_pi, forall_and]
  rw [Measure.map_apply hf ((MeasurableSet.univ_pi hA').prod (MeasurableSet.univ_pi hB')), hpre,
    Measure.pi_pi, Measure.pi_pi, Measure.pi_pi, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => Measure.prod_prod _ _

end PiProd

section Loc

variable {n r : ℕ}

private theorem continuous_Dl_diagonal (l : ℕ) :
    Continuous (fun c : Fin (r + 1) → ℂ => Formalism.L2.SG.RealObj.Dl (Matrix.diagonal c) l) := by
  unfold Formalism.L2.SG.RealObj.Dl
  split_ifs with hl
  · exact (Continuous.matrix_diagonal continuous_id).matrix_submatrix _ _ |>.matrix_det
  · exact continuous_const

theorem gv_cont (T T' : ℝ) : Continuous (fun c : Fin (r + 1) → ℂ => Gv T T' (Matrix.diagonal c)) := by
  unfold Formalism.L2.SG.RealObj.Gv
  exact ((continuous_Dl_diagonal _).norm.pow 2).sub (continuous_const.mul ((continuous_Dl_diagonal _).norm.pow 2))

theorem wtLoc_cont (k : ℕ) (T T' : ℝ) : Continuous (fun c : Fin (r + 1) → ℂ => wtLoc k T T' c) := by
  unfold wtLoc Formalism.L2.SG.RealObj.JacV
  refine ((gv_cont T T').pow _).mul (continuous_finset_prod _ fun l _ => ?_)
  unfold Formalism.L2.SG.RealObj.modC
  exact (((continuous_Dl_diagonal l).norm).pow 2).pow 2

theorem wtLoc_nonneg (k : ℕ) (T T' : ℝ) {c : Fin (r + 1) → ℂ} (hc : c ∈ GoodLoc (r := r) T T') :
    0 ≤ wtLoc k T T' c := by
  unfold wtLoc Formalism.L2.SG.RealObj.JacV
  exact mul_nonneg (pow_nonneg hc.2.le _) (Finset.prod_nonneg fun _ _ => sq_nonneg _)

theorem measurableSet_goodLoc (T T' : ℝ) : MeasurableSet (GoodLoc (r := r) T T') := by
  have h1 : IsOpen {c : Fin (r + 1) → ℂ | ∀ l, c l ≠ 0} := by
    simp only [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun l => isOpen_ne_fun (continuous_apply l) continuous_const
  have h2 : IsOpen {c : Fin (r + 1) → ℂ | 0 < Gv T T' (Matrix.diagonal c)} :=
    isOpen_lt continuous_const (gv_cont T T')
  rw [GoodLoc, Set.setOf_and]
  exact (h1.inter h2).measurableSet

def nuLoc (k : ℕ) (T T' C : ℝ) : Measure (Fin (r + 1) → ℂ) :=
  ((dcLoc (r := r)).restrict (GoodLoc (r := r) T T')).withDensity (fun c => ENNReal.ofReal (C * wtLoc k T T' c))

instance (k : ℕ) (T T' C : ℝ) : SigmaFinite (nuLoc (r := r) k T T' C) := by
  unfold nuLoc dcLoc
  exact SigmaFinite.withDensity_ofReal _

variable (ε : Fin n → Bool)

def phiLoc (h : (Fin (r + 1) → ℂ) → Formalism.REAL.UJ ε) (x : (Fin (r + 1) → ℂ) × (Formalism.REAL.UJ ε × Formalism.REAL.UJ ε)) :
    Formalism.REAL.UJ ε :=
  x.2.1 * h x.1 * x.2.2⁻¹

theorem phiLoc_meas {h : (Fin (r + 1) → ℂ) → Formalism.REAL.UJ ε} (hh : Measurable h) : Measurable (phiLoc ε h) := by
  unfold phiLoc
  exact ((measurable_fst.comp measurable_snd).mul (hh.comp measurable_fst)).mul
    (measurable_snd.comp measurable_snd).inv

theorem muG_eq_map (k : ℕ) (T T' : ℝ) (μS μS' : Measure (Formalism.REAL.UJ ε)) [SFinite μS] [SFinite μS']
    (h : (Fin (r + 1) → ℂ) → Formalism.REAL.UJ ε) (hh : Measurable h) (C : ℝ)
    (hD : DisintLoc ε k T T' μS μS' h C) :
    Formalism.REAL.muG ε = ((nuLoc (r := r) k T T' C).prod (μS.prod μS')).map (phiLoc ε h) := by
  have hp := phiLoc_meas ε hh
  refine Measure.ext fun s hs => ?_
  have hφ : Measurable (s.indicator (1 : Formalism.REAL.UJ ε → ℝ≥0∞)) := measurable_const.indicator hs
  have hm : Measurable fun p => s.indicator (1 : Formalism.REAL.UJ ε → ℝ≥0∞) (phiLoc ε h p) := hφ.comp hp
  have hw : Measurable fun c : Fin (r + 1) → ℂ => ENNReal.ofReal (C * wtLoc k T T' c) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul (wtLoc_cont k T T').measurable)
  have hg := hm.lintegral_prod_right' (ν := μS.prod μS')
  rw [← lintegral_indicator_one hs, hD _ hφ, Measure.map_apply hp hs, ← lintegral_indicator_one (hp hs)]
  have hind : ((phiLoc ε h) ⁻¹' s).indicator
      (1 : (Fin (r + 1) → ℂ) × (Formalism.REAL.UJ ε × Formalism.REAL.UJ ε) → ℝ≥0∞) =
      fun p => s.indicator (1 : Formalism.REAL.UJ ε → ℝ≥0∞) (phiLoc ε h p) := by
    funext p
    by_cases hx : phiLoc ε h p ∈ s <;> simp [hx]
  rw [hind, lintegral_prod _ hm.aemeasurable, nuLoc, lintegral_withDensity_eq_lintegral_mul _ hw hg]
  refine lintegral_congr fun c => ?_
  congr 1
  have hc : Measurable fun y : Formalism.REAL.UJ ε × Formalism.REAL.UJ ε =>
      s.indicator (1 : Formalism.REAL.UJ ε → ℝ≥0∞) (phiLoc ε h (c, y)) := hm.comp measurable_prodMk_left
  beta_reduce
  rw [lintegral_prod _ hc.aemeasurable]
  rfl

end Loc

end Formalism.L2.SG.RealObj.InfCut.ProductExactness
