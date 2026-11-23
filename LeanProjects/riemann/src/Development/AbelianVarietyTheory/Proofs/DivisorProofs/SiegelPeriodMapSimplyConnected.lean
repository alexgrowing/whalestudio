import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff

noncomputable section

namespace GlobalTheory.SiegelOpen
open GlobalTheory

theorem continuous_tauU (g : ℕ) : Continuous (tauU (g := g)) :=
  continuous_matrix fun i j =>
    (continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val)

theorem isSymm_tauU {g : ℕ} (s : symMat g) : (tauU s).IsSymm := by
  ext i j
  simp only [tauU, transpose_apply, of_apply]
  exact s.2 j i

theorem isOpen_siegel (g : ℕ) : IsOpen (siegel g) := by
  refine isOpen_iff_mem_nhds.mpr fun s hs => ?_
  filter_upwards [(continuous_tauU g).continuousAt.eventually
    (IsSiegel.eventually_isSiegel hs)] with t ht
  exact ht (isSymm_tauU t)

theorem differentiable_tauU_apply (g : ℕ) (i j : Fin g) :
    Differentiable ℂ (fun s : symMat g => tauU s i j) :=
  (((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin g => ℂ) j).comp
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin g => Fin g → ℂ) i)).comp
      (Submodule.subtypeL (symMat g))).differentiable

theorem convex_siegel (g : ℕ) : Convex ℝ (siegel g) := by
  intro x hx y hy a b ha hb hab
  refine ⟨isSymm_tauU _, ?_⟩
  have e : (tauU (a • x + b • y)).map Complex.im =
      a • (tauU x).map Complex.im + b • (tauU y).map Complex.im := by
    ext i j
    simp [tauU]
  rw [e]
  rcases ha.eq_or_lt with rfl | ha'
  · have : b = 1 := by simpa using hab
    subst this
    simpa using hy.2
  · exact (hx.2.smul ha').add_posSemidef (hy.2.posSemidef.smul hb)

theorem siegel_nonempty (g : ℕ) : (siegel g).Nonempty :=
  ⟨⟨Matrix.of fun i j => (Complex.I • (1 : Matrix (Fin g) (Fin g) ℂ)) i j, fun i j => by
    simp [Matrix.one_apply, eq_comm]⟩, isSiegel_I_smul_one (ι := Fin g)⟩

theorem simplyConnected_siegel (g : ℕ) : SimplyConnectedSpace (siegel g) := by
  haveI := (convex_siegel g).contractibleSpace (siegel_nonempty g)
  infer_instance

theorem isPeriodMap_tauU_and_simplyConnected :
    ∀ g : ℕ, IsPeriodMap (siegel g) tauU ∧ SimplyConnectedSpace (siegel g) := fun g =>
  ⟨⟨isOpen_siegel g, fun i j => (differentiable_tauU_apply g i j).differentiableOn,
    fun _ hb => hb⟩, simplyConnected_siegel g⟩

end GlobalTheory.SiegelOpen
