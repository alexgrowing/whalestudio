import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaSplitting.SplitW
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKrdRDIota
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKrdPlace
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKrdDenseW

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.KSplitW
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem cw_iota_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (y : GR d.n) :
    d.cw w (inFrame d.b (R.ι w y)) = dZ d.n R.ζ⁻¹ * mR y * dZ d.n R.ζ := by
  have h0 := Krd.zeta_ne R.hζ
  have e := congrArg (fun M => dZ d.n R.ζ⁻¹ * M) (R.at_w w y)
  simp only [← Matrix.mul_assoc, Krd.dZ_inv_mul h0, Matrix.one_mul] at e
  exact e
theorem law_w_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (x : d.G) :
    (d.cw w (inFrame d.b x))ᵀ * Krd.Qc d.n R.ε * (d.cw w (inFrame d.b x)).map star = Krd.Qc d.n R.ε := by
  have hx : (mat2 x)ᵀ * dbl (incM F d.Y.J) * (mat2 x).map (cA σ) = dbl (incM F d.Y.J) := x.2
  have hw := congrArg (d.cw w) hx
  rw [_root_.PositivityTheory.SiegelWeilFormula.Krd.cw_mul_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_mul_k, _root_.PositivityTheory.SiegelWeilFormula.Place.cw_cA_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_transpose_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.dbl_incM_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_incM_k] at hw
  have hQ := _root_.PositivityTheory.SiegelWeilFormula.Krd.hQ_w_k d R.hε w
  set b := d.b.1.map (d.B.emb w).1 with hb
  set bi := (d.b⁻¹).1.map (d.B.emb w).1 with hbi
  set D := (dbl d.Y.J).map (d.B.emb w).1 with hD
  have hbbi : b * bi = 1 := by
    rw [hb, hbi, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  have hbib : bi * b = 1 := by
    rw [hb, hbi, ← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  have hQ' : biᵀ * Krd.Qc d.n R.ε * bi.map star = D := by
    rw [← hQ]
    calc biᵀ * (bᵀ * D * b.map star) * bi.map star = (b * bi)ᵀ * D * (b * bi).map star := by
          rw [Matrix.transpose_mul, Krd.mapStar_mul]; simp only [Matrix.mul_assoc]
      _ = D := by rw [hbbi, Matrix.transpose_one, Krd.mapStar_one, Matrix.one_mul, Matrix.mul_one]
  have hZ : d.cw w (inFrame d.b x) = bi * d.cw w (mat2 x) * b := by
    simp only [inFrame, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_mul_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_incM_k, hb, hbi]
  rw [hZ]
  exact Krd.conj_unit bi b (d.cw w (mat2 x)) _ _ hbib hQ' hw
theorem cw_inFrame_one_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (w : InfinitePlace F) : d.cw w (inFrame d.b (1 : d.G)) = 1 := by
  rw [SiegelEisensteinSeries.Grp.inFrame_one, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_one_k]
theorem decompW_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (g : d.G) :
    ∃ (x : d.G) (y : GR d.n), g = x * R.ι w y ∧ d.cw w (inFrame d.b x) = 1 := by
  have h0 := Krd.zeta_ne R.hζ
  set Zw := d.cw w (inFrame d.b g) with hZw
  let y : GR d.n := Krd.DM.mkG (dZ d.n R.ζ * Zw * dZ d.n R.ζ⁻¹) (Krd.inG_conj R.hζ Zw (_root_.PositivityTheory.SiegelWeilFormula.KSplitW.law_w_k d R w g))
  refine ⟨g * (R.ι w y)⁻¹, y, by rw [inv_mul_cancel_right], ?_⟩
  have hy : d.cw w (inFrame d.b (R.ι w y)) = Zw := by
    rw [_root_.PositivityTheory.SiegelWeilFormula.KSplitW.cw_iota_k, Krd.DM.mR_mkG]
    simp only [← Matrix.mul_assoc, Krd.dZ_inv_mul h0, Matrix.one_mul]
    rw [Matrix.mul_assoc, Krd.dZ_inv_mul h0, Matrix.mul_one]
  have hinv : Zw * d.cw w (inFrame d.b g⁻¹) = 1 := by
    rw [hZw, ← _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_mul_k, ← _root_.PositivityTheory.SiegelWeilFormula.Krd.DM.inFrame_mul_k d, mul_inv_cancel, _root_.PositivityTheory.SiegelWeilFormula.KSplitW.cw_inFrame_one_k]
  have e : d.cw w (inFrame d.b (g * (R.ι w y)⁻¹)) * Zw = Zw := by
    have e0 : d.cw w (inFrame d.b (g * (R.ι w y)⁻¹)) * d.cw w (inFrame d.b (R.ι w y)) = Zw := by
      rw [← _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_mul_k, ← _root_.PositivityTheory.SiegelWeilFormula.Krd.DM.inFrame_mul_k d, inv_mul_cancel_right]
    rwa [hy] at e0
  calc d.cw w (inFrame d.b (g * (R.ι w y)⁻¹)) = d.cw w (inFrame d.b (g * (R.ι w y)⁻¹)) * (Zw * d.cw w (inFrame d.b g⁻¹)) := by
        rw [hinv, Matrix.mul_one]
    _ = 1 := by rw [← Matrix.mul_assoc, e, hinv]
theorem commW_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (x : d.G) (hx : d.cw w (inFrame d.b x) = 1) (y : GR d.n) :
    x * R.ι w y = R.ι w y * x := by
  apply _root_.PositivityTheory.SiegelWeilFormula.Krd.DM.inFrame_inj_k d
  rw [_root_.PositivityTheory.SiegelWeilFormula.Krd.DM.inFrame_mul_k d, _root_.PositivityTheory.SiegelWeilFormula.Krd.DM.inFrame_mul_k d]
  refine _root_.PositivityTheory.SiegelWeilFormula.Place.cw_ext_k d (fun w' => ?_) ?_
  · rw [_root_.PositivityTheory.SiegelWeilFormula.Krd.cw_mul_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_mul_k]
    by_cases h : w' = w
    · subst h; rw [hx, Matrix.one_mul, Matrix.mul_one]
    · rw [R.off_w w w' y h, Matrix.one_mul, Matrix.mul_one]
  · rw [Krd.fin_mul, Krd.fin_mul, R.off_f]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]
theorem finOne_one_mem_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (i j : Fin d.n ⊕ Fin d.n) :
    finOne F • (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) i j ∈ intHat F E := by
  by_cases h : i = j
  · subst h; rw [Matrix.one_apply_eq]; exact finOne_mem
  · rw [Matrix.one_apply_ne h, smul_zero]; exact zero_mem _
theorem iota_mem_K_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (y : GR d.n) (hy : InK (mR y)) : R.ι w y ∈ d.K := by
  have h0 := Krd.zeta_ne R.hζ
  rw [d.ok.stdK]
  refine ⟨fun w' => ?_, fun k' hk' i j => ?_⟩
  · change d.cw w' (inFrame d.b (R.ι w y)) * (d.cw w' (inFrame d.b (R.ι w y)))ᴴ = 1
    by_cases h : w' = w
    · subst h
      have hM : mR y * (mR y)ᴴ = 1 := mul_eq_one_comm.1 hy.2
      rw [_root_.PositivityTheory.SiegelWeilFormula.KSplitW.cw_iota_k, dZ_inv_ct R.hζ, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      have hD : dZ d.n R.ζ * (dZ d.n R.ζ)ᴴ = 1 := by rw [← dZ_inv_ct R.hζ, Krd.dZ_mul_inv h0]
      calc (dZ d.n R.ζ)ᴴ * mR y * dZ d.n R.ζ * ((dZ d.n R.ζ)ᴴ * ((mR y)ᴴ * dZ d.n R.ζ))
          = (dZ d.n R.ζ)ᴴ * (mR y * (dZ d.n R.ζ * (dZ d.n R.ζ)ᴴ) * (mR y)ᴴ) * dZ d.n R.ζ := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hD, Matrix.mul_one, hM, Matrix.mul_one, ← dZ_inv_ct R.hζ, Krd.dZ_inv_mul h0]
    · rw [R.off_w w w' y h, Matrix.conjTranspose_one, Matrix.mul_one]
  · have hk'' : ∃ z, k' = R.ι w z := by
      rcases hk' with rfl | hk'
      · exact ⟨y, rfl⟩
      · rw [Set.mem_singleton_iff] at hk'
        exact ⟨y⁻¹, by rw [hk', map_inv]⟩
    obtain ⟨z, rfl⟩ := hk''
    have e := congrFun (congrFun (R.off_f w z) i) j
    rw [Matrix.smul_apply, Matrix.smul_apply] at e
    rw [e]
    exact _root_.PositivityTheory.SiegelWeilFormula.KSplitW.finOne_one_mem_k d i j
theorem kSplit_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (k : d.G) (hk : k ∈ d.K) :
    ∃ y : GR d.n, (R.ι w y)⁻¹ * k ∈ d.K ∧ d.cw w (inFrame d.b ((R.ι w y)⁻¹ * k)) = 1 := by
  have h0 := Krd.zeta_ne R.hζ
  obtain ⟨x, y, hxy, hx⟩ := _root_.PositivityTheory.SiegelWeilFormula.KSplitW.decompW_k d R w k
  have hkx : (R.ι w y)⁻¹ * k = x := by rw [hxy, _root_.PositivityTheory.SiegelWeilFormula.KSplitW.commW_k d R w x hx y, inv_mul_cancel_left]
  have hU : d.cw w (inFrame d.b k) * (d.cw w (inFrame d.b k))ᴴ = 1 := ((d.ok.stdK k).1 hk).1 w
  have hkw : d.cw w (inFrame d.b k) = (dZ d.n R.ζ)ᴴ * mR y * dZ d.n R.ζ := by
    rw [hxy, _root_.PositivityTheory.SiegelWeilFormula.Krd.DM.inFrame_mul_k d, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_mul_k, hx, Matrix.one_mul, _root_.PositivityTheory.SiegelWeilFormula.KSplitW.cw_iota_k, dZ_inv_ct R.hζ]
  have hD : dZ d.n R.ζ * (dZ d.n R.ζ)ᴴ = 1 := by rw [← dZ_inv_ct R.hζ, Krd.dZ_mul_inv h0]
  have hD' : (dZ d.n R.ζ)ᴴ * dZ d.n R.ζ = 1 := by rw [← dZ_inv_ct R.hζ, Krd.dZ_inv_mul h0]
  have hM : mR y = dZ d.n R.ζ * d.cw w (inFrame d.b k) * (dZ d.n R.ζ)ᴴ := by
    rw [hkw]; simp only [← Matrix.mul_assoc]; rw [hD, Matrix.one_mul, Matrix.mul_assoc, hD, Matrix.mul_one]
  have hU' : (d.cw w (inFrame d.b k))ᴴ * d.cw w (inFrame d.b k) = 1 := mul_eq_one_comm.1 hU
  have hK : InK (mR y) := by
    refine ⟨y.2, ?_⟩
    rw [hM, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc dZ d.n R.ζ * ((d.cw w (inFrame d.b k))ᴴ * (dZ d.n R.ζ)ᴴ) * (dZ d.n R.ζ * d.cw w (inFrame d.b k) * (dZ d.n R.ζ)ᴴ)
        = dZ d.n R.ζ * ((d.cw w (inFrame d.b k))ᴴ * ((dZ d.n R.ζ)ᴴ * dZ d.n R.ζ) * d.cw w (inFrame d.b k)) *
          (dZ d.n R.ζ)ᴴ := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hD', Matrix.mul_one, hU', Matrix.mul_one, hD]
  refine ⟨y, ?_, by rw [hkx]; exact hx⟩
  exact (d.K).mul_mem ((d.K).inv_mem (_root_.PositivityTheory.SiegelWeilFormula.KSplitW.iota_mem_K_k d R w y hK)) hk
end PositivityTheory.SiegelWeilFormula.KSplitW
end
end
