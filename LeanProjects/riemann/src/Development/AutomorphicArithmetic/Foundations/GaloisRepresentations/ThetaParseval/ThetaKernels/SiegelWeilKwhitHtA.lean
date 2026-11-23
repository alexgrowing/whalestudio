import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.InFrameForm
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKwhitIwa

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KWhit.Ht
open PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KWhit
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
local notation:70 X:70 " ⬝ " Y:71 => @HMul.hMul _ _ _ Matrix.instHMulOfFintypeOfMulOfAddCommMonoid X Y
theorem par_topleft_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (p : d.G) (t : GL (Fin d.n) (AE F E)) (hp : IsPar p t) :
    ∃ tb : GL (Fin d.n) E, (inFrame d.b p).toBlocks₁₁ = incM F (tb⁻¹).1 * t.1 * incM F tb.1 := by
  obtain ⟨-, tb, htb⟩ := d.ok.frame
  refine ⟨tb, ?_⟩
  let E1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E) := Matrix.fromRows 1 0
  let DC : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E) := diagCols (Fin d.n)
  have htb' : d.b.1.toCols₁ = (diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) E) ⬝ tb.1 := htb
  have hp' : mat2 p ⬝ DC = DC ⬝ t.1 := hp
  have hcol : ∀ M : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E), M ⬝ E1 = M.toCols₁ := by
    intro M
    ext i j
    simp [E1, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, Matrix.toCols₁]
  have h1 : incM F d.b.1 ⬝ E1 = incM F (d.b.1.toCols₁) := by
    rw [hcol]
    ext i j
    rfl
  have h2 : incM F ((diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) E) ⬝ tb.1) = DC ⬝ incM F tb.1 := by
    rw [incM_mul']
    congr 1
    ext i j
    cases i <;> simp [DC, diagCols, incM, Matrix.one_apply, apply_ite] <;> split_ifs <;> simp_all
  have hb : incM F d.b.1 ⬝ E1 = DC ⬝ incM F tb.1 := h1.trans ((congrArg (incM F) htb').trans h2)
  have hTb : incM F tb.1 ⬝ incM F (tb⁻¹).1 = 1 := by
    rw [← incM_mul', Units.mul_inv]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hBB : incM F (d.b⁻¹).1 ⬝ incM F d.b.1 = 1 := _root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_inv_mul_k d
  have hdc : DC = incM F d.b.1 ⬝ E1 ⬝ incM F (tb⁻¹).1 := by
    rw [hb, Matrix.mul_assoc, hTb, Matrix.mul_one]
  have key : inFrame d.b p ⬝ E1 = E1 ⬝ (incM F (tb⁻¹).1 ⬝ t.1 ⬝ incM F tb.1) := by
    have e0 : inFrame d.b p = incM F (d.b⁻¹).1 ⬝ mat2 p ⬝ incM F d.b.1 := rfl
    calc inFrame d.b p ⬝ E1 = incM F (d.b⁻¹).1 ⬝ (mat2 p ⬝ (incM F d.b.1 ⬝ E1)) := by
          rw [e0]; simp only [Matrix.mul_assoc]
      _ = incM F (d.b⁻¹).1 ⬝ ((mat2 p ⬝ DC) ⬝ incM F tb.1) := by
          rw [hb, Matrix.mul_assoc]
      _ = incM F (d.b⁻¹).1 ⬝ ((DC ⬝ t.1) ⬝ incM F tb.1) := by rw [hp']
      _ = (incM F (d.b⁻¹).1 ⬝ incM F d.b.1) ⬝ E1 ⬝ (incM F (tb⁻¹).1 ⬝ t.1 ⬝ incM F tb.1) := by
          rw [hdc]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [hBB, Matrix.one_mul]
  ext i j
  have := congrFun (congrFun key (Sum.inl i)) j
  rw [hcol] at this
  simpa [E1, Matrix.toBlocks₁₁, Matrix.toCols₁, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, ite_mul,
    Finset.sum_ite_eq] using this
theorem inFrame_form_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (y : d.G) : ∃ C' : Matrix (Fin d.n) (Fin d.n) (AE F E),
    (∃ ε : ℤˣ, C' = ((ε : ℤ) : AE F E) • 1) ∧
    (inFrame d.b y)ᵀ * Matrix.fromBlocks 0 1 C' 0 * (inFrame d.b y).map (cA σ) = Matrix.fromBlocks 0 1 C' 0 := by
  obtain ⟨⟨ε, hε⟩, -⟩ := d.ok.frame
  have e1 : (incM F d.b.1).map (cA σ) = incM F (d.b.1.map σ) := by
    ext i j
    simp [incM, cA, inclR, Algebra.TensorProduct.map_tmul]
  have e2 : dbl (incM F d.Y.J) = incM F (dbl d.Y.J) := by
    simp [dbl, incM, Matrix.fromBlocks_map, Matrix.map_neg]
  have key : incM F (d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ) =
      (incM F d.b.1)ᵀ * incM F (dbl d.Y.J) * incM F (d.b.1.map σ) := by
    simp only [incM, Matrix.map_mul, Matrix.transpose_map]
  have hF : (incM F d.b.1)ᵀ * dbl (incM F d.Y.J) * (incM F d.b.1).map (cA σ) =
      Matrix.fromBlocks 0 1 (((ε : ℤ) : AE F E) • 1) 0 := by
    rw [e1, e2, ← key, hε]
    simp only [incM, Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero _), Matrix.map_one _ (map_zero _) (map_one _)]
    congr 1
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply]
    split_ifs <;> simp
  refine ⟨((ε : ℤ) : AE F E) • 1, ⟨ε, rfl⟩, ?_⟩
  have hM : (mat2 y)ᵀ * dbl (incM F d.Y.J) * (mat2 y).map (cA σ) = dbl (incM F d.Y.J) := y.2
  have := form_conj_in (cA σ).toRingHom (_root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_mul_inv_k d) hM
  rw [← hF]
  exact this
theorem levi_tu_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (x : d.G) (t u : GL (Fin d.n) (AE F E)) (hx : inFrame d.b x = Matrix.fromBlocks t.1 0 0 u.1) :
    t.1ᵀ * u.1.map (cA σ) = 1 := by
  obtain ⟨C', -, h⟩ := _root_.PositivityTheory.SiegelWeilFormula.KWhit.Ht.inFrame_form_k d x
  rw [hx] at h
  simp only [Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply, Matrix.transpose_zero,
    Matrix.map_zero _ (map_zero (cA σ)), Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, Matrix.mul_one,
    Matrix.fromBlocks_inj] at h
  exact h.2.1
theorem frame_iwa_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (g : d.G) : ∃ (D : GL (Fin d.n) (AE F E)) (k : d.G), k ∈ d.K ∧
    d.a g = ((GlobalTheory.Doubling.absE F E (Matrix.GeneralLinearGroup.det D) : ℝ≥0) : ℝ)⁻¹ ∧
    (inFrame d.b g).toBlocks₂₁ = D.1 * (inFrame d.b k).toBlocks₂₁ ∧
    (inFrame d.b g).toBlocks₂₂ = D.1 * (inFrame d.b k).toBlocks₂₂ := by
  obtain ⟨p, t', hp, k, hk, rfl⟩ := d.ok.hgt.iwa g
  have h21 := _root_.PositivityTheory.SiegelWeilFormula.KWhit.parabolic_lowerLeft_block_zero d p t' hp
  obtain ⟨tb, htl⟩ := _root_.PositivityTheory.SiegelWeilFormula.KWhit.Ht.par_topleft_k d p t' hp
  set A := (inFrame d.b p).toBlocks₁₁ with hA
  set B := (inFrame d.b p).toBlocks₁₂ with hB
  set D₀ := (inFrame d.b p).toBlocks₂₂ with hD₀
  have hPb : inFrame d.b p = Matrix.fromBlocks A B 0 D₀ := by rw [← h21, Matrix.fromBlocks_toBlocks]
  obtain ⟨C', ⟨ε, hC'⟩, hform⟩ := _root_.PositivityTheory.SiegelWeilFormula.KWhit.Ht.inFrame_form_k d p
  rw [hPb, hC'] at hform
  simp only [Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply, Matrix.transpose_zero,
    Matrix.map_zero _ (map_zero (cA σ)), Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, Matrix.mul_one,
    Matrix.fromBlocks_inj] at hform
  have hεε : ((ε : ℤ) : AE F E) * ((ε : ℤ) : AE F E) = 1 := by
    rcases Int.units_eq_one_or ε with h | h <;> simp [h]
  have hDA : D₀ᵀ * A.map (cA σ) = 1 := by
    have h3 := hform.2.2.1
    rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul] at h3
    have := congrArg (fun M => ((ε : ℤ) : AE F E) • M) h3
    simpa [smul_smul, hεε] using this
  have hdet : D₀.det * cA σ A.det = 1 := by
    have := congrArg Matrix.det hDA
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one,
      show (A.map (cA σ)).det = cA σ A.det from (AlgHom.map_det (cA σ) A).symm] at this
    exact this
  have hDu : IsUnit D₀ := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_exists_inv.2 ⟨_, hdet⟩)
  refine ⟨hDu.unit, k, hk, ?_, ?_, ?_⟩
  · rw [d.ok.hgt.val p t' hp k hk]
    have hAt : A.det = (Matrix.GeneralLinearGroup.det t').1 := by
      rw [htl, Matrix.det_mul, Matrix.det_mul]
      have hinv : (incM F (tb⁻¹).1).det * (incM F tb.1).det = 1 := by
        rw [← Matrix.det_mul]
        have e : incM F (tb⁻¹).1 * incM F tb.1 = 1 := by
          simp only [incM, ← Matrix.map_mul, Units.inv_mul]
          exact Matrix.map_one _ (map_zero _) (map_one _)
        rw [e, Matrix.det_one]
      simp only [Matrix.GeneralLinearGroup.val_det_apply]
      linear_combination (t'.1.det) * hinv
    have hU : Matrix.GeneralLinearGroup.det hDu.unit *
        GlobalTheory.Doubling.conjUnit σ (Matrix.GeneralLinearGroup.det t') = 1 := by
      ext
      simp only [Units.val_mul, Units.val_one, Matrix.GeneralLinearGroup.val_det_apply, IsUnit.unit_spec,
        GlobalTheory.Doubling.conjUnit, Units.coe_map]
      change D₀.det * Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ t'.1.det = 1
      rw [sigR_eq_cA, ← Matrix.GeneralLinearGroup.val_det_apply, ← hAt]
      exact hdet
    have := congrArg (GlobalTheory.Doubling.absE F E) hU
    rw [map_mul, GlobalTheory.Doubling.absE_conjUnit, map_one] at this
    have hpos : (0 : ℝ≥0) < GlobalTheory.Doubling.absE F E (Matrix.GeneralLinearGroup.det hDu.unit) := by
      rcases eq_or_ne (GlobalTheory.Doubling.absE F E (Matrix.GeneralLinearGroup.det hDu.unit)) 0 with h | h
      · rw [h, zero_mul] at this; exact absurd this zero_ne_one
      · exact pos_iff_ne_zero.2 h
    rw [eq_inv_of_mul_eq_one_right this, NNReal.coe_inv]
  · rw [_root_.PositivityTheory.SiegelWeilFormula.KWhit.inFrame_mul_k, hPb]
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks (inFrame d.b k)]
    simp [Matrix.fromBlocks_multiply]
  · rw [_root_.PositivityTheory.SiegelWeilFormula.KWhit.inFrame_mul_k, hPb]
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks (inFrame d.b k)]
    simp [Matrix.fromBlocks_multiply]
theorem bottom_rows_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (x : d.G) (t u : GL (Fin d.n) (AE F E)) (hx : inFrame d.b x = Matrix.fromBlocks t.1 0 0 u.1)
    (nb : nA σ d.Y d.b → d.G) (hnb : IsNMap d.b nb) (ε : ℤˣ) (w : d.G) (hw : d.IsW ε w) (β : nA σ d.Y d.b) :
    (inFrame d.b (w * nb β * x)).toBlocks₂₁ = (((ε : ℤ) : AE F E) • t.1) ∧
    (inFrame d.b (w * nb β * x)).toBlocks₂₂ = (((ε : ℤ) : AE F E) • (β.1 * u.1)) := by
  rw [_root_.PositivityTheory.SiegelWeilFormula.KWhit.inFrame_mul_k, _root_.PositivityTheory.SiegelWeilFormula.KWhit.inFrame_mul_k, hw, hnb β, hx]
  simp only [Matrix.fromBlocks_multiply, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂, Matrix.zero_mul, Matrix.mul_zero,
    Matrix.one_mul, Matrix.mul_one, add_zero, zero_add, Matrix.of_apply, Matrix.fromBlocks_apply₂₁,
    Matrix.fromBlocks_apply₂₂]
  constructor <;> ext i j <;> simp [Matrix.smul_apply, Matrix.mul_apply, Matrix.one_apply, ite_mul, Finset.sum_ite_eq,
    Finset.mul_sum, mul_assoc]
end PositivityTheory.SiegelWeilFormula.KWhit.Ht
end
end
