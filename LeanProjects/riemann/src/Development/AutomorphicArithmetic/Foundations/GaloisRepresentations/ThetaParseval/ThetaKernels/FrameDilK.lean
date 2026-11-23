import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.FrameDil
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopStepMA
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKsplitSplitP
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopChiW
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopStepMVal
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopMChar
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKrdPlace
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopRelPf

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.Act.CL
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem rEx_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (w : InfinitePlace F) : ∃ r : ℝ → GroundTheory.Global.IdeleGroup F,
    (∀ τ τ', r (τ + τ') = r τ * r τ') ∧ r 0 = 1 ∧
    (∀ τ, (GroundTheory.Global.IdeleGroup.ideleModule F (r τ) : ℝ) = Real.exp τ) ∧
    (∀ τ, piInf (d.B.emb w) ((r τ : AF F) • (1 : AE F E)) = (Real.exp τ : ℂ)) ∧
    (∀ τ w', w' ≠ w → piInf (d.B.emb w') ((r τ : AF F) • (1 : AE F E)) = 1) ∧
    (∀ τ, finOne F * (r τ : AF F) = finOne F) := by
  have := d.cm.1
  have hw : w.IsReal := IsTotallyReal.isReal w
  let e := InfinitePlace.Completion.ringEquivRealOfIsReal hw
  let u : ℝ → ℝˣ := fun τ => ⟨Real.exp τ, Real.exp (-τ), by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero],
    by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]⟩
  let r : ℝ → GroundTheory.Global.IdeleGroup F := fun τ => GroundTheory.Global.IdeleGroup.infiniteEmbedding w (Units.map e.symm.toMonoidHom (u τ))
  have hu : ∀ τ τ', u (τ + τ') = u τ * u τ' := fun τ τ' => Units.ext (Real.exp_add τ τ')
  have hu0 : u 0 = 1 := Units.ext Real.exp_zero
  have hr1 : ∀ τ, ((r τ : AF F)).1 = GroundTheory.Global.IdeleGroup.infiniteAdeleSingle w (e.symm (Real.exp τ)) := fun τ => rfl
  have hr2 : ∀ τ, ((r τ : AF F)).2 = 1 := fun τ => rfl
  have hee : ∀ x : ℝ, InfinitePlace.Completion.extensionEmbeddingOfIsReal hw (e.symm x) = x := fun x => e.apply_symm_apply x
  have hext : ∀ τ, InfinitePlace.Completion.extensionEmbedding w (e.symm (Real.exp τ)) = (Real.exp τ : ℂ) := by
    intro τ
    rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw, hee]
  refine ⟨r, fun τ τ' => by simp only [r, hu, map_mul], by simp only [r, hu0, map_one], fun τ => ?_, fun τ => ?_,
    fun τ w' hw' => ?_, fun τ => ?_⟩
  · rw [GroundTheory.Global.IdeleGroup.ideleModule_infiniteEmbedding, hw.mult_eq_one, pow_one]
    show ‖e.symm (Real.exp τ)‖ = _
    rw [← (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero (map_zero _), hee,
      Real.norm_of_nonneg (Real.exp_pos τ).le]
  · rw [St.piInf_smul, map_one, mul_one, hr1, GroundTheory.Global.IdeleGroup.infiniteAdeleSingle_apply, Pi.mulSingle_eq_same]
    exact hext τ
  · rw [St.piInf_smul, map_one, mul_one, hr1, GroundTheory.Global.IdeleGroup.infiniteAdeleSingle_apply, Pi.mulSingle_eq_of_ne hw', map_one]
  · refine Prod.ext ?_ ?_
    · show (0 : Ainf F) * _ = 0
      rw [zero_mul]
    · show (1 : Af F) * (r τ : AF F).2 = 1
      rw [hr2, mul_one]
theorem frame_dil_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (r : ℝ → GroundTheory.Global.IdeleGroup F)
    (hw : ∀ τ, piInf (d.B.emb w) ((r τ : AF F) • (1 : AE F E)) = (Real.exp τ : ℂ))
    (ho : ∀ τ w', w' ≠ w → piInf (d.B.emb w') ((r τ : AF F) • (1 : AE F E)) = 1)
    (hf : ∀ τ, finOne F * (r τ : AF F) = finOne F) (i₀ : Fin d.n) {τ : ℝ} {y : GR d.n}
    (hy : IsDil (Pi.single i₀ 1) τ y) :
    inFrame d.b (R.ι w y) = dM i₀ ((r τ : AF F) • (1 : AE F E)) ((r (-τ) : AF F) • (1 : AE F E)) := by
  have hζ0 : R.ζ ≠ 0 := Krd.zeta_ne R.hζ
  have hC : Matrix.fromBlocks (Matrix.diagonal fun j => (Real.exp (τ * (Pi.single i₀ 1 : Fin d.n → ℝ) j) : ℂ)) 0 0
      (Matrix.diagonal fun j => (Real.exp (-(τ * (Pi.single i₀ 1 : Fin d.n → ℝ) j)) : ℂ)) = dM i₀ (Real.exp τ : ℂ) (Real.exp (-τ) : ℂ) := by
    ext u v
    rw [dM_apply]
    rcases u with u | u <;> rcases v with v | v <;>
      simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
        Matrix.diagonal_apply, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, if_false, Matrix.zero_apply] <;>
      by_cases h : u = v <;> by_cases h' : u = i₀ <;> subst_vars <;> simp_all [Pi.single_apply]
  refine _root_.PositivityTheory.SiegelWeilFormula.Place.cw_ext_k d (fun w' => ?_) ?_
  · by_cases hw' : w' = w
    · subst hw'
      rw [R.cw_iota_pf w' y, hy, dZ_conj_diag hζ0, hC, _root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, dM_map, hw, hw]
    · rw [R.off_w w w' y hw', _root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, dM_map, ho τ w' hw', ho (-τ) w' hw']
      ext u v
      rw [dM_apply, Matrix.one_apply]
      split_ifs <;> rfl
  · rw [R.off_f w y]
    ext u v
    rw [Matrix.smul_apply, Matrix.smul_apply, dM_apply, Matrix.one_apply]
    have e : ∀ t, finOne F • ((r t : AF F) • (1 : AE F E)) = finOne F • (1 : AE F E) := fun t => by
      rw [smul_smul, hf]
    split_ifs <;> simp [e]
theorem par_dil_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (i₀ : Fin d.n) {τ : ℝ} {y : GR d.n}
    (hy : IsDil (Pi.single i₀ 1) τ y) :
    ∃ t, IsPar (R.ι w y) t ∧ (absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) = Real.exp (2 * τ) ∧
      (d.χ (Matrix.GeneralLinearGroup.det t) : ℂ) = 1 := by
  obtain ⟨t0, ht0⟩ := d.ok.frame.2
  set A : Matrix (Fin d.n) (Fin d.n) ℂ := Matrix.diagonal fun j => (Real.exp (τ * (Pi.single i₀ 1 : Fin d.n → ℝ) j) : ℂ) with hAdef
  set D : Matrix (Fin d.n) (Fin d.n) ℂ := Matrix.diagonal fun j => (Real.exp (-(τ * (Pi.single i₀ 1 : Fin d.n → ℝ) j)) : ℂ)
  have hy' : mR y = Matrix.fromBlocks A 0 0 D := hy
  obtain ⟨-, hA, -, hoA, hfA, -⟩ := R.frame_diag w y A D hy'
  have h21 : (mR y).toBlocks₂₁ = 0 := by rw [hy', Matrix.toBlocks_fromBlocks₂₁]
  obtain ⟨t, ht, habs⟩ := _root_.PositivityTheory.SiegelWeilFormula.KSplitP.iota_isPar_k d R w y h21
  have hdetA : A.det = (Real.exp τ : ℂ) := by
    rw [hAdef, Matrix.det_diagonal, Finset.prod_eq_single i₀ (fun j _ hj => by simp [Pi.single_eq_of_ne hj])
      (fun h => absurd (Finset.mem_univ _) h)]
    simp
  refine ⟨t, ht, ?_, ?_⟩
  · rw [habs, hy', Matrix.toBlocks_fromBlocks₁₁, hdetA, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos τ).le,
      ← Real.exp_nat_mul]
    norm_num
  · have ht1 := ((kunf.isPar_frame ht0 (R.ι w y) t).1 ht).2
    set P := (inFrame d.b (R.ι w y)).toBlocks₁₁ with hP
    have hcw : ∀ w', d.cw w' t.1 = d.cw w' (incM F t0.1) * d.cw w' P * d.cw w' (incM F (t0⁻¹).1) := by
      intro w'; rw [ht1]; simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, Matrix.map_mul]
    have hI : incM F t0.1 * incM F (t0⁻¹).1 = 1 := by
      rw [← kunf.incM_mul', Units.mul_inv]; ext i j; simp [incM, Matrix.one_apply]
    have hT : ∀ w', d.cw w' (incM F t0.1) * d.cw w' (incM F (t0⁻¹).1) = 1 := by
      intro w'; rw [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, _root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, ← Matrix.map_mul, hI, Matrix.map_one _ (map_zero _) (map_one _)]
    have ho : ∀ w', w' ≠ w → d.cw w' t.1 = 1 := fun w' h => by rw [hcw, (hoA w' h).1, Matrix.mul_one, hT]
    have hf : finOne F • t.1 = finOne F • (1 : Matrix (Fin d.n) (Fin d.n) (AE F E)) := by
      rw [ht1, ← Matrix.smul_mul, ← Matrix.mul_smul, hfA, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hI]
    have hdet : (d.cw w t.1).det = (Real.exp τ : ℂ) := by
      have hXY := congrArg Matrix.det (hT w)
      rw [Matrix.det_mul, Matrix.det_one] at hXY
      rw [hcw, Matrix.det_mul, Matrix.det_mul, hA, hdetA]
      linear_combination ((Real.exp τ : ℝ) : ℂ) * hXY
    rw [_root_.PositivityTheory.SiegelWeilFormula.RD_k.chi_det (d := d) w t _ rfl ho hf, hdet]
    exact d.chiW_pos w _ (Real.exp_pos τ)
end PositivityTheory.SiegelWeilFormula.Act.CL
end
end
