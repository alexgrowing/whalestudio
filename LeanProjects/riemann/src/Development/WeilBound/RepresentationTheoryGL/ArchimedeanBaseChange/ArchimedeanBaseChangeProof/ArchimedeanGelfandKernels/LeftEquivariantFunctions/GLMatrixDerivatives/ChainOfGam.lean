import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.ChainOfLoc

noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff

namespace PositivityTheory.RgBcC.LfSt.ChainPf.Gam

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G th tw hb)
open PositivityTheory.RgBcC.LfSt.ChainPf.Eq PositivityTheory.RgBcC.LfSt.ChainPf.Loc

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem iteratedDeriv_equiv {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (A : V ≃L[ℂ] V) (φ : ℝ → V) (k : ℕ)
    (t : ℝ) : iteratedDeriv k (fun s => A (φ s)) t = A (iteratedDeriv k φ t) := by
  have h := (A.restrictScalars ℝ).iteratedFDeriv_comp_left (f := φ) (x := t) (i := k)
  have h2 := congrArg (fun L => L (fun _ : Fin k => (1 : ℝ))) h
  simp only [iteratedDeriv_eq_iteratedFDeriv]
  simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply] at h2
  exact h2

theorem deriv_equiv {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (A : V ≃L[ℂ] V) (φ : ℝ → V) (t : ℝ) :
    deriv (fun s => A (φ s)) t = A (deriv φ t) := by
  have := iteratedDeriv_equiv A φ 1 t
  simpa only [iteratedDeriv_one] using this

theorem wave_equiv (E : KMod n) (A : E.V ≃L[ℂ] E.V) (hA : ∀ (k : Matrix.unitaryGroup (Fin n) ℂ) v, A (E.ρ k v) = E.ρ k (A v))
    (u : ℝ → Mat n → E.V) (hu : IsWave E u) : IsWave E fun t x => A (u t x) := by
  obtain ⟨h1, h2, h3, h4⟩ := hu
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (A.restrictScalars ℝ : E.V →L[ℝ] E.V).contDiff.comp_contDiffOn h1
  · intro t
    refine ⟨(A.restrictScalars ℝ : E.V →L[ℝ] E.V).contDiff.comp_contDiffOn (h2 t).1, ?_⟩
    intro g hg k
    simp only
    rw [(h2 t).2 g hg k, hA]
  · intro t g hg
    rw [iteratedDeriv_equiv A (fun s => u s g) 2 t, h3 t g hg, om_equiv]
  · intro g hg
    rw [deriv_equiv A (fun s => u s g) 0, h4 g hg, map_zero]

theorem act_equiv (hWE : WaveEx) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n))
    [μ.IsHaarMeasure] (E : KMod n) (A : E.V ≃L[ℂ] E.V)
    (hA : ∀ (k : Matrix.unitaryGroup (Fin n) ℂ) v, A (E.ρ k v) = E.ρ k (A v)) (w : List (Bool × ℕ)) (g : ℝ → ℝ)
    (ks : Mat n → (E.V →L[ℂ] E.V)) (hks : IsKer μ E w g ks) (f : Mat n → E.V) (hf : f ∈ CE E) :
    act μ E ks (fun x => A (f x)) 1 = A (act μ E ks f 1) := by
  obtain ⟨u, hu, hu0⟩ := hWE n E f hf
  have hAu := wave_equiv E A hA u hu
  have hone : (1 : Mat n) ∈ GLs n := by simp [GLs]
  have key : ∀ F F' : Mat n → E.V, Set.EqOn F F' (GLs n) → act μ E ks F 1 = act μ E ks F' 1 := by
    intro F F' h
    unfold act
    congr 1
    funext y
    rw [h]
    simp only [GLs, Set.mem_setOf_eq, one_mul]
    exact ((Matrix.isUnit_iff_isUnit_det _).mp y.isUnit).ne_zero
  rw [key (fun x => A (f x)) (fun x => A (u 0 x)) (fun x hx => by simp only [hu0 x hx]),
    key f (u 0) (fun x hx => (hu0 x hx).symm),
    hks.2.2.2 _ hAu 1 hone, hks.2.2.2 _ hu 1 hone]
  refine Eq.trans ?_ (congrFun (zop_equiv A w _) 1)
  congr 2
  funext x'
  rw [← A.integral_comp_comm]
  congr 1
  funext t
  exact ((A : E.V →L[ℂ] E.V).map_smul_of_tower (g t) (u t x')).symm

end PositivityTheory.RgBcC.LfSt.ChainPf.Gam
