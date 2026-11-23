import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.ChainOfDC

noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff

namespace PositivityTheory.RgBcC.LfSt.ChainPf.DCc

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G th tw hb)
open PositivityTheory.RgBcC.LfSt.ChainPf PositivityTheory.RgBcC.LfSt.ChainPf.Eq PositivityTheory.RgBcC.LfSt.ChainPf.Loc

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem mem_GLs_of (y : G n) : y.val ∈ GLs n := (Matrix.isUnit_iff_isUnit_det _).1 y.isUnit |>.ne_zero

theorem mul_mem_GLs {x y : Mat n} (hx : x ∈ GLs n) (hy : y ∈ GLs n) : x * y ∈ GLs n := by
  simp only [GLs, Set.mem_setOf_eq, Matrix.det_mul] at *
  exact mul_ne_zero hx hy

theorem act_congr [MeasurableSpace (G n)] (μ : Measure (G n)) (E : KMod n) (k : Mat n → (E.V →L[ℂ] E.V))
    {F F' : Mat n → E.V} (h : Set.EqOn F F' (GLs n)) {x : Mat n} (hx : x ∈ GLs n) : act μ E k F x = act μ E k F' x := by
  simp only [act]
  exact integral_congr_ae (Eventually.of_forall fun y => by
    show (k y.val) (F (x * y.val)) = (k y.val) (F' (x * y.val))
    rw [h (mul_mem_GLs hx (mem_GLs_of y))])

theorem act_dc (hDW : DCwave) (hP : ParamInt) (hZ : ZopDC) (hG : GelComm) (hWE : WaveEx) {lam : Fin n → ℤ} {E : KMod n}
    {Fr : Mat n → (E.V →L[ℂ] E.V)} {ε ι : Mat n →ₗ[ℝ] (E.V →L[ℂ] E.V)} {S : ℝ → (E.V →L[ℂ] E.V)} {Γ T : E.V →L[ℂ] E.V}
    (hC : CxData lam E Fr ε ι S Γ T) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]
    (w : List (Bool × ℕ)) (g : ℝ → ℝ) (T' : ℝ) (hgb : IsBump g T') (ks : Mat n → (E.V →L[ℂ] E.V))
    (hks : IsKer μ E w g ks) (f : Mat n → E.V) (hf : f ∈ CE E) :
    act μ E ks (DC ε Fr f) 1 = DC ε Fr (act μ E ks f) 1 := by
  haveI := FiniteDimensional.complete ℂ E.V
  obtain ⟨u, hu, hu0⟩ := hWE n E f hf
  have h1 : (1 : Mat n) ∈ GLs n := by simp [GLs]
  have hDu := hDW hG n lam E Fr ε ι S Γ T hC u hu
  have hk1 := hks.2.2.2 _ hDu 1 h1
  obtain ⟨hPs, hPd⟩ := hP n E u hu g T' hgb
  have eqA : Set.EqOn (fun x' => ∫ t, (g t : ℂ) • DC ε Fr (u t) x') (DC ε Fr fun x' => ∫ t, (g t : ℂ) • u t x') (GLs n) :=
    fun x hx => param_dc ε Fr u hu.1 g T' hgb hPd x hx
  have hz := hZ hG n lam E Fr ε ι S Γ T hC (fun x' => ∫ t, (g t : ℂ) • u t x') hPs w
  have eqB : Set.EqOn (zOp w fun x' => ∫ t, (g t : ℂ) • u t x') (act μ E ks f) (GLs n) := by
    intro x hx
    rw [← hks.2.2.2 u hu x hx]
    exact act_congr μ E ks (fun y hy => hu0 y hy) hx
  have eq0 : Set.EqOn (DC ε Fr f) (DC ε Fr (u 0)) (GLs n) :=
    dc_congr ε Fr (isOpen_GLs n) fun y hy => (hu0 y hy).symm
  calc act μ E ks (DC ε Fr f) 1 = act μ E ks (DC ε Fr (u 0)) 1 := act_congr μ E ks eq0 h1
    _ = zOp w (fun x' => ∫ t, (g t : ℂ) • DC ε Fr (u t) x') 1 := hk1
    _ = zOp w (DC ε Fr fun x' => ∫ t, (g t : ℂ) • u t x') 1 := zop_congr (isOpen_GLs n) w eqA h1
    _ = DC ε Fr (zOp w fun x' => ∫ t, (g t : ℂ) • u t x') 1 := hz.2 1 h1
    _ = DC ε Fr (act μ E ks f) 1 := dc_congr ε Fr (isOpen_GLs n) eqB h1

end PositivityTheory.RgBcC.LfSt.ChainPf.DCc
