import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftEisensteinLevelSubgroup

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.ColSlice

variable {D : D7} {n r t a : ℕ}

def colIdx (hn : r + t = n) (j : Fin t) : Fin n := finCongr hn (finSumFinEquiv (Sum.inr j))

theorem colIdx_injective (hn : r + t = n) : Function.Injective (colIdx hn) := fun _ _ h =>
  Sum.inr_injective (finSumFinEquiv.injective ((finCongr hn).injective h))

def colPr (hn : r + t = n) (y : Mx D a n) : Mx D a t := y.submatrix id (colIdx hn)

theorem colPr_jn (hn : r + t = n) (x : Mx D a r) (v : Mx D a t) : colPr hn (jn hn x v) = v := by
  ext i j
  simp [colPr, colIdx, jn, Matrix.submatrix_apply]

theorem continuous_colPr (hn : r + t = n) : Continuous (colPr (D := D) (a := a) hn) :=
  continuous_id.matrix_submatrix _ _

theorem continuous_jn (hn : r + t = n) (x : Mx D a r) : Continuous (jn (D := D) hn x) :=
  continuous_matrix fun i j => by
    show Continuous fun v : Mx D a t => Matrix.fromCols x v i ((finSumFinEquiv.trans (finCongr hn)).symm j)
    rcases (finSumFinEquiv.trans (finCongr hn)).symm j with s | s
    · exact continuous_const
    · exact continuous_id.matrix_elem i s

theorem realSize_le (θ : InfFam D) (hn : r + t = n) (x : Mx D a r) (v : Mx D a t) :
    GlobalTheory.Unf.realSize θ v ≤ GlobalTheory.Unf.realSize θ (jn hn x v) := by
  unfold GlobalTheory.Unf.realSize
  refine Finset.sum_le_sum fun τ _ => Finset.sum_le_sum fun i _ => ?_
  have e : ∀ j, compAt θ τ v i j = compAt θ τ (jn hn x v) i (colIdx hn j) := fun j => by
    have := colPr_jn hn x v
    conv_lhs => rw [← this]
    rfl
  simp only [e]
  have h := Finset.sum_le_univ_sum_of_nonneg (f := fun j => ‖compAt θ τ (jn hn x v) i j‖)
    (s := Finset.univ.map ⟨colIdx hn, colIdx_injective hn⟩) fun _ => norm_nonneg _
  rw [Finset.sum_map] at h
  exact h

theorem maj_jn_le (θ : InfFam D) (hn : r + t = n) (K : Set (Mx D a n)) (N : ℕ) (x : Mx D a r) (v : Mx D a t) :
    GlobalTheory.Unf.maj θ K N (jn hn x v) ≤ GlobalTheory.Unf.maj θ (colPr hn '' K) N v := by
  by_cases hb : GlobalTheory.Unf.InBox K (jn hn x v)
  · have hb' : GlobalTheory.Unf.InBox (colPr hn '' K) v := by
      obtain ⟨k, hk, h0⟩ := hb
      refine ⟨colPr hn k, ⟨k, hk, rfl⟩, ?_⟩
      ext i j
      have := congrFun (congrFun h0 i) (colIdx hn j)
      have e : v i j = jn hn x v i (colIdx hn j) := by
        conv_lhs => rw [← colPr_jn hn x v]
        rfl
      show finPart D (v i j - k i (colIdx hn j)) = 0
      rw [e]
      exact this
    unfold GlobalTheory.Unf.maj
    rw [if_pos hb, if_pos hb']
    have h1 := GlobalTheory.Unf.realSize_nonneg θ v
    have h2 := realSize_le θ hn x v
    gcongr
  · have h0 : GlobalTheory.Unf.maj θ K N (jn hn x v) = 0 := by unfold GlobalTheory.Unf.maj; rw [if_neg hb]
    rw [h0]
    exact GlobalTheory.Unf.maj_nonneg θ _ N v

theorem integrable_slice : ∀ {D : D7} {n r t : ℕ} {θ : InfFam D} (hθ : IsInfFam θ) {a : ℕ} (hn : r + t = n)
    (μt : Measure (Mx D a t)) [μt.IsAddHaarMeasure] (Φ : schwartzA θ a n) (x : Mx D a r),
    Integrable (fun v => Φ.1 (jn hn x v)) μt := by
  intro D n r t θ hθ a hn μt _ Φ x
  obtain ⟨i1, i2, i3, i4, -⟩ := lattice_Mx D a t
  haveI : BorelSpace (Mx D a t) := ⟨rfl⟩
  obtain ⟨hc, K, hK, hC⟩ := GlobalTheory.SchwartzMaj.continuous_and_le_maj D θ hθ a n Φ.1
    (GlobalTheory.SchwartzPure.isSchwartzBruhat_of_mem_schwartzA D θ hθ a n Φ.1 Φ.2)
  obtain ⟨N, hN⟩ := GlobalTheory.Unf.MajInt.maj_integrable D θ hθ a t (fun _ _ => True) 0 μt inferInstance
    (.of_forall fun _ _ _ h => (h trivial).elim) (fun s _ => map_add_right_eq_self μt s)
  obtain ⟨C, hC⟩ := hC N
  have hK' : IsCompact (colPr hn '' K) := hK.image (continuous_colPr hn)
  have hC0 : ∀ v, ‖Φ.1 (jn hn x v)‖ ≤ |C| * GlobalTheory.Unf.maj θ (colPr hn '' K) N v := fun v =>
    (hC _).trans ((mul_le_mul_of_nonneg_right (le_abs_self C) (GlobalTheory.Unf.maj_nonneg θ K N _)).trans
      (mul_le_mul_of_nonneg_left (maj_jn_le θ hn K N x v) (abs_nonneg C)))
  exact ((hN _ hK').const_mul |C|).mono' (hc.comp (continuous_jn hn x)).aestronglyMeasurable (.of_forall hC0)

end GlobalTheory.CompanionTheory.ColSlice
