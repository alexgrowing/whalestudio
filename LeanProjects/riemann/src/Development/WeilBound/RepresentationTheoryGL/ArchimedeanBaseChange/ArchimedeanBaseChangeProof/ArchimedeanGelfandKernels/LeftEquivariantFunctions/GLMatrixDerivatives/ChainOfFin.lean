import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.ChainOfTop
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.FderivApplyConst

noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff

namespace PositivityTheory.RgBcC.LfSt.ChainPf.Fin

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G th tw hb)
open PositivityTheory.RgBcC.LfSt.ChainPf PositivityTheory.RgBcC.LfSt.ChainPf.Eq PositivityTheory.RgBcC.LfSt.ChainPf.Loc
  PositivityTheory.RgBcC.LfSt.ChainPf.DCc PositivityTheory.RgBcC.LfSt.ChainPf.Ker PositivityTheory.RgBcC.LfSt.ChainPf.Gam PositivityTheory.RgBcC.LfSt.ChainPf.Top

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem unitary_mem_GLs (k : Matrix.unitaryGroup (Fin n) ℂ) : k.1 ∈ GLs n := by
  show det k.1 ≠ 0
  intro h0
  have hd := Matrix.det_of_mem_unitary k.2
  rw [h0] at hd
  have h1 : star (0 : ℂ) * 0 = 1 := hd.1
  simp at h1

theorem act_sum (hL : LgFacts) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]
    (E : KMod n) {m : ℕ} (c : Fin m → ℂ) (ks : Fin m → Mat n → (E.V →L[ℂ] E.V)) (k : Mat n → (E.V →L[ℂ] E.V))
    (hsum : ∀ y ∈ GLs n, k y = ∑ i, c i • ks i y) (hcont : ∀ i, ContinuousOn (ks i) (GLs n)) (hcpt : ∀ i, Cpt (ks i))
    (F : Mat n → E.V) (hF : ContinuousOn F (GLs n)) (x : Mat n) (hx : x ∈ GLs n) :
    act μ E k F x = ∑ i, c i • act μ E (ks i) F x := by
  unfold act
  have hFx : ContinuousOn (fun z => F (x * z)) (GLs n) :=
    hF.comp (continuous_const.mul continuous_id).continuousOn (fun z hz => mul_mem_GLs hx hz)
  have hint : ∀ i, Integrable (fun y : G n => (ks i ↑y) (F (x * ↑y))) μ :=
    fun i => int_of_cptK hL μ (ks i) (fun z => F (x * z)) (hcont i) hFx (hcpt i)
  have hint' : ∀ i ∈ (Finset.univ : Finset (Fin m)),
      Integrable (fun y : G n => c i • (ks i ↑y) (F (x * ↑y))) μ :=
    fun i _ => (hint i).smul (c i)
  have hfun : (fun y : G n => (k ↑y) (F (x * ↑y))) = fun (y : G n) => ∑ i, c i • (ks i ↑y) (F (x * ↑y)) := by
    funext y
    rw [hsum _ (mem_GLs_of y)]
    simp [ContinuousLinearMap.sum_apply]
  rw [hfun, integral_finset_sum _ hint']
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [integral_smul]

theorem dc_sum {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (ε : Mat n →ₗ[ℝ] (V →L[ℂ] V))
    (Fr : Mat n → (V →L[ℂ] V)) {m : ℕ} (c : Fin m → ℂ) (h : Fin m → Mat n → V)
    (hd : ∀ i, DifferentiableAt ℝ (h i) 1) :
    DC ε Fr (fun x => ∑ i, c i • h i x) 1 = ∑ i, c i • DC ε Fr (h i) 1 := by
  have hsd : HasFDerivAt (fun x => ∑ i, c i • h i x) (∑ i, c i • fderiv ℝ (h i) 1) 1 :=
    HasFDerivAt.fun_sum fun i _ => (hd i).hasFDerivAt.const_smul (c i)
  simp only [DC, Rd, hsd.fderiv]
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply, map_sum,
    map_smul, Finset.smul_sum, smul_add]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← Finset.sum_add_distrib, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← smul_add, map_smul]

end PositivityTheory.RgBcC.LfSt.ChainPf.Fin
