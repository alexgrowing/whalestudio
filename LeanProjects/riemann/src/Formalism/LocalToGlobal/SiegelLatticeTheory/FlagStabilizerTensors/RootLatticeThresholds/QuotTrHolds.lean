import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.HaarTrHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.RowsBij

noncomputable section

open Matrix MeasureTheory NumberField Formalism.BasicNotions

namespace Formalism.L2.SG.Pf.Carrier.CarPinTor

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj.InfCut Formalism.L2.SG.LocWSOf Formalism.MainNotions.S

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {θ : ℝ} (C : Choice X θ)

theorem y_inv_mem (τ : D.what₂.Tau) : (C.y τ)⁻¹ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS) := by
  have hy : (C.y τ)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * C.y τ = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS := C.y_mem τ
  have hu := Formalism.L2.SG.Pf.LocJEq.unit_det_y C τ
  show ((C.y τ)⁻¹)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * (C.y τ)⁻¹ = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS
  conv_lhs => rw [← hy]
  rw [Matrix.conjTranspose_nonsing_inv]
  calc ((C.y τ)ᴴ)⁻¹ * ((C.y τ)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * C.y τ) * (C.y τ)⁻¹
      = (((C.y τ)ᴴ)⁻¹ * (C.y τ)ᴴ) * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * (C.y τ * (C.y τ)⁻¹) := by
        simp only [Matrix.mul_assoc]
    _ = _ := by
        rw [Matrix.nonsing_inv_mul _ (by rw [Matrix.det_conjTranspose]; exact hu.star),
          Matrix.mul_nonsing_inv _ hu, Matrix.one_mul, Matrix.mul_one]

set_option maxHeartbeats 1000000 in

theorem quotTr_holds (u u' : D.what₂.Word) (τ : D.what₂.Tau) : QuotTr C u u' τ := by
  intro γ μRv ν hH hq
  obtain ⟨hσ, -, -, -⟩ := hH
  obtain ⟨h1, h2, -, -⟩ := C.isT τ
  set F : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS :=
    fun x => Matrix.of.symm (trG (C.Q τ) (C.Qi τ) x) with hF
  have hemb : Topology.IsClosedEmbedding F := Formalism.L2.SG.Pf.WuBL.trG_closedEmb' n_eq _ h2
  have hFm : Measurable F := hemb.continuous.measurable
  set cj : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS :=
    fun x i j => ((gB C τ γ)⁻¹ * Matrix.of x * gB C τ γ) i j with hcjdef
  have hcj : Measurable cj := by
    have : Continuous cj := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
    exact this.measurable
  have hSm : Measurable (Formalism.L2.SG.Pf.LocJEq.Smap C τ γ) := (Formalism.L2.SG.Pf.LocJEq.smap_cont C τ γ).measurable
  set y' := Formalism.L2.SG.Pf.LocJEq.ujOf' (C.Q τ * (C.y τ)⁻¹ * C.Qi τ)
    (Formalism.L2.SG.Pf.LocJEq.transp_mem C τ (y_inv_mem C τ)) with hy'
  have hty' : trG (C.Q τ) (C.Qi τ) y' = (C.y τ)⁻¹ := by
    show C.Qi τ * (C.Q τ * (C.y τ)⁻¹ * C.Qi τ) * C.Q τ = _
    simp only [← Matrix.mul_assoc]
    rw [h1, Matrix.one_mul, Matrix.mul_assoc, h1, Matrix.mul_one]

  have key : ∀ σ z : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)),
      (fun i j => (Matrix.of (cj (F σ)) * Matrix.of (Formalism.L2.SG.Pf.LocJEq.Smap C τ γ z)) i j) =
        F (γ⁻¹ * (σ * z) * y') := by
    intro σ z
    have hs : Matrix.of (Formalism.L2.SG.Pf.LocJEq.Smap C τ γ z) = trG (C.Q τ) (C.Qi τ) (γ⁻¹ * z) * (C.y τ)⁻¹ := by
      rw [Formalism.L2.SG.Pf.LocJEq.smap_val]; rfl
    have hgg : trG (C.Q τ) (C.Qi τ) γ * trG (C.Q τ) (C.Qi τ) γ⁻¹ = 1 := trG_mul_inv C τ γ
    have hM : (gB C τ γ)⁻¹ * trG (C.Q τ) (C.Qi τ) σ * gB C τ γ * Matrix.of (Formalism.L2.SG.Pf.LocJEq.Smap C τ γ z) =
        trG (C.Q τ) (C.Qi τ) (γ⁻¹ * (σ * z) * y') := by
      rw [hs, trG_inv, trG_mul, trG_mul, trG_mul, trG_mul, hty']
      calc trG (C.Q τ) (C.Qi τ) γ⁻¹ * trG (C.Q τ) (C.Qi τ) σ * gB C τ γ *
          (trG (C.Q τ) (C.Qi τ) γ⁻¹ * trG (C.Q τ) (C.Qi τ) z * (C.y τ)⁻¹)
          = trG (C.Q τ) (C.Qi τ) γ⁻¹ * trG (C.Q τ) (C.Qi τ) σ *
            (trG (C.Q τ) (C.Qi τ) γ * trG (C.Q τ) (C.Qi τ) γ⁻¹) * trG (C.Q τ) (C.Qi τ) z * (C.y τ)⁻¹ := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [hgg, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    funext i j
    exact congrFun (congrFun hM i) j
  intro f hf
  show ∫⁻ x, f x ∂((Formalism.REAL.muG (X.B.I.ε (vOf X τ))).map F) = _
  rw [lintegral_map hf hFm]
  haveI : SigmaFinite μRv := hσ
  have hfm2 : Measurable fun p : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS × Formalism.QuantumDeterminants.Mt D.R.k D.R.rS =>
      f (fun i j => (Matrix.of p.2 * Matrix.of p.1) i j) := by
    refine hf.comp ?_
    have : Continuous fun p : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS × Formalism.QuantumDeterminants.Mt D.R.k D.R.rS =>
        ((fun i j => (Matrix.of p.2 * Matrix.of p.1) i j : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)) :=
      continuous_snd.matrix_mul continuous_fst
    exact this.measurable
  have hinner : Measurable fun x : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS =>
      ∫⁻ s, f (fun i j => (Matrix.of s * Matrix.of x) i j) ∂((μRv.map F).map cj) :=
    hfm2.lintegral_prod_right'
  rw [lintegral_map hinner hSm]
  have hin : ∀ z, ∫⁻ s, f (fun i j => (Matrix.of s * Matrix.of (Formalism.L2.SG.Pf.LocJEq.Smap C τ γ z)) i j)
      ∂((μRv.map F).map cj) = ∫⁻ σ, f (F (γ⁻¹ * (σ * z) * y')) ∂μRv := by
    intro z
    have hm3 : Measurable fun s : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS =>
        f (fun i j => (Matrix.of s * Matrix.of (Formalism.L2.SG.Pf.LocJEq.Smap C τ γ z)) i j) :=
      hfm2.comp (measurable_const.prodMk measurable_id)
    rw [lintegral_map hm3 hcj]
    rw [lintegral_map (f := fun a => f fun i j => (Matrix.of (cj a) * Matrix.of (Formalism.L2.SG.Pf.LocJEq.Smap C τ γ z)) i j)
      (hm3.comp hcj) hFm]
    refine lintegral_congr fun σ => ?_
    rw [key]
  simp only [hin]
  have hg : Measurable fun w : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) => f (F (γ⁻¹ * w * y')) :=
    hf.comp (hFm.comp ((continuous_mul_right y').measurable.comp (continuous_mul_left γ⁻¹).measurable))
  rw [← hq _ hg]
  symm
  calc ∫⁻ x, f (F (γ⁻¹ * x * y')) ∂(Formalism.REAL.muG (X.B.I.ε (vOf X τ)))
      = ∫⁻ x, (fun w => f (F (γ⁻¹ * w))) (x * y') ∂(Formalism.REAL.muG (X.B.I.ε (vOf X τ))) := by
        simp only [mul_assoc]
    _ = ∫⁻ x, f (F (γ⁻¹ * x)) ∂(Formalism.REAL.muG (X.B.I.ε (vOf X τ))) :=
        lintegral_mul_right_eq_self (fun w => f (F (γ⁻¹ * w))) y'
    _ = ∫⁻ x, f (F x) ∂(Formalism.REAL.muG (X.B.I.ε (vOf X τ))) :=
        lintegral_mul_left_eq_self (fun w => f (F w)) γ⁻¹

end Formalism.L2.SG.Pf.Carrier.CarPinTor
