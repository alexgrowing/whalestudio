import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.FinOneDilV
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.G2HaarMeasure.ContinuousInFrame

noncomputable section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula.AStep

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem dilV_off (h : IsCMExt F E σ) {n : ℕ} (w : InfinitePlace F) (i₀ : Fin n) (τ : ℝ) (k : Fin n ⊕ Fin n)
    (hk : k ∉ ({Sum.inl i₀, Sum.inr i₀} : Set (Fin n ⊕ Fin n))) : dilV h w i₀ τ k = 1 := by
  haveI := h.1
  rcases k with j | j
  · have hj : j ≠ i₀ := fun hj => hk (by subst hj; simp)
    show (if j = i₀ then _ else (1 : AE F E)) = 1
    rw [if_neg hj]
  · have hj : j ≠ i₀ := fun hj => hk (by subst hj; simp)
    show (if j = i₀ then _ else (1 : AE F E)) = 1
    rw [if_neg hj]

theorem j_comm_dil {d : SD σ} (R : RD d) (L : LD d) (w : InfinitePlace F) (τ : ℝ) (y : GR d.n)
    (hy : IsDil (Pi.single L.i₀ 1) τ y) (g : L.sd.G) : L.j g * R.ι w y = R.ι w y * L.j g := by
  have hPQ := GlobalTheory.EisBL.DoubledParabolic.incM_mul_inv (F := F) d.b
  have hQP := GlobalTheory.EisBL.DoubledParabolic.incM_inv_mul (F := F) d.b
  have key : ∀ x : d.G, mat2 x = incM F ((d.b : GL (Fin d.n ⊕ Fin d.n) E) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E) * inFrame d.b x * incM F ((d.b⁻¹ : GL (Fin d.n ⊕ Fin d.n) E) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E) := by
    intro x
    show mat2 x = incM F ((d.b : GL (Fin d.n ⊕ Fin d.n) E) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E) * (incM F ((d.b⁻¹ : GL (Fin d.n ⊕ Fin d.n) E) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E) * mat2 x * incM F ((d.b : GL (Fin d.n ⊕ Fin d.n) E) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E)) * incM F ((d.b⁻¹ : GL (Fin d.n ⊕ Fin d.n) E) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E)
    simp only [Matrix.mul_assoc, hPQ, Matrix.mul_one]
    rw [← Matrix.mul_assoc, hPQ, Matrix.one_mul]
  have hM := L.j_out g
  have hcomm : inFrame d.b (L.j g) * inFrame d.b (R.ι w y) = inFrame d.b (R.ι w y) * inFrame d.b (L.j g) := by
    rw [inFrame_dil R w L.i₀ τ y hy]
    ext u v
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases hS : u ∈ ({Sum.inl L.i₀, Sum.inr L.i₀} : Set (Fin d.n ⊕ Fin d.n)) ∨ v ∈ ({Sum.inl L.i₀, Sum.inr L.i₀} : Set (Fin d.n ⊕ Fin d.n))
    · have h1 : inFrame d.b (L.j g) u v = (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) u v := by
        rcases hS with hu | hv
        · exact (hM u hu v).1
        · exact (hM v hv u).2
      rw [h1]
      by_cases huv : u = v
      · subst huv
        exact mul_comm _ _
      · rw [Matrix.one_apply_ne huv, zero_mul, mul_zero]
    · obtain ⟨hu, hv⟩ := not_or.mp hS
      rw [dilV_off _ w L.i₀ τ u hu, dilV_off _ w L.i₀ τ v hv, mul_one, one_mul]
  apply Subtype.ext
  apply Units.ext
  show mat2 (L.j g) * mat2 (R.ι w y) = mat2 (R.ι w y) * mat2 (L.j g)
  rw [key (L.j g), key (R.ι w y)]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (incM F ((d.b⁻¹ : GL (Fin d.n ⊕ Fin d.n) E) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E)) (incM F ((d.b : GL (Fin d.n ⊕ Fin d.n) E) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E)), hQP, Matrix.one_mul,
    ← Matrix.mul_assoc (incM F ((d.b⁻¹ : GL (Fin d.n ⊕ Fin d.n) E) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E)) (incM F ((d.b : GL (Fin d.n ⊕ Fin d.n) E) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E)), hQP, Matrix.one_mul,
    ← Matrix.mul_assoc (inFrame d.b (L.j g)), hcomm, Matrix.mul_assoc]

theorem l_eq_T_zero (d : SD σ) (Ψ : d.Fn) (hΨ : Ψ ∈ d.sch) : d.l Ψ = d.T Ψ 0 := by
  have hk := d.ok.dbl.kill 0 Ψ hΨ
  show d.l Ψ = d.l (d.dd.rho d.B.ψ (0 * (incM F (↑d.b : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E).toCols₂).transpose) Ψ)
  convert hk.symm using 3
  exact (Matrix.zero_mul _).trans (Matrix.zero_mul _).symm

theorem dilV_mul (h : IsCMExt F E σ) {n : ℕ} (w : InfinitePlace F) (i₀ : Fin n) (τ : ℝ) (j : Fin n) :
    dilV h w i₀ τ (Sum.inl j) * dilV h w i₀ τ (Sum.inr j) = 1 := by
  haveI := h.1
  show (if j = i₀ then _ else (1 : AE F E)) * (if j = i₀ then _ else (1 : AE F E)) = 1
  by_cases hj : j = i₀
  · rw [if_pos hj, if_pos hj, ← map_mul, adr_mul, ← Real.exp_add, add_neg_cancel, Real.exp_zero,
      adr_one, map_one]
  · rw [if_neg hj, if_neg hj, mul_one]

theorem dilV_mul' (h : IsCMExt F E σ) {n : ℕ} (w : InfinitePlace F) (i₀ : Fin n) (τ : ℝ) (j : Fin n) :
    dilV h w i₀ τ (Sum.inr j) * dilV h w i₀ τ (Sum.inl j) = 1 := by
  rw [mul_comm]
  exact dilV_mul h w i₀ τ j

def dilT (h : IsCMExt F E σ) {n : ℕ} (w : InfinitePlace F) (i₀ : Fin n) (τ : ℝ) : GL (Fin n) (AE F E) :=
  ⟨Matrix.diagonal fun j => dilV h w i₀ τ (Sum.inl j), Matrix.diagonal fun j => dilV h w i₀ τ (Sum.inr j), by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext j; exact dilV_mul h w i₀ τ j, by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext j; exact dilV_mul' h w i₀ τ j⟩

theorem det_dilT (h : IsCMExt F E σ) {n : ℕ} (w : InfinitePlace F) (i₀ : Fin n) (τ : ℝ) :
    haveI := h.1
    Matrix.GeneralLinearGroup.det (dilT h w i₀ τ) = Units.map (algebraMap (AF F) (AE F E)).toMonoidHom (adrU w τ) := by
  haveI := h.1
  apply Units.ext
  show (Matrix.diagonal fun j => dilV h w i₀ τ (Sum.inl j)).det =
    algebraMap (AF F) (AE F E) (adr w (Real.exp τ))
  rw [Matrix.det_diagonal, Finset.prod_eq_single i₀]
  · show (if i₀ = i₀ then _ else (1 : AE F E)) = _
    rw [if_pos rfl]
  · intro j _ hj
    show (if j = i₀ then _ else (1 : AE F E)) = 1
    rw [if_neg hj]
  · intro hi
    exact absurd (Finset.mem_univ i₀) hi

theorem inFrame_dil' {d : SD σ} (R : RD d) (w : InfinitePlace F) (i₀ : Fin d.n) (τ : ℝ) (y : GR d.n)
    (hy : IsDil (Pi.single i₀ 1) τ y) :
    inFrame d.b (R.ι w y) = Matrix.fromBlocks (dilT d.cm w i₀ τ).1 0 0 (dilT d.cm w i₀ (-τ)).1 := by
  rw [inFrame_dil R w i₀ τ y hy]
  show _ = Matrix.fromBlocks (Matrix.diagonal fun j => dilV d.cm w i₀ τ (Sum.inl j)) 0 0
    (Matrix.diagonal fun j => dilV d.cm w i₀ (-τ) (Sum.inl j))
  rw [Matrix.fromBlocks_diagonal]
  congr 1

theorem section_dilation_exp (H : Hyps) {d : SD σ} (R : RD d) (w : InfinitePlace F) (i₀ : Fin d.n) (τ : ℝ) (y : GR d.n)
    (hy : IsDil (Pi.single i₀ 1) τ y) {Φ : d.Fn} (hΦ : Φ ∈ d.sch) (h : d.G) :
    d.sec0 Φ (R.ι w y * h) = Complex.exp (τ * d.m) * d.sec0 Φ h := by
  haveI := d.cm.1
  have hφ : d.om h Φ ∈ d.sch := d.ok.dbl.weil.2.1.toIsSplitting.pres h Φ hΦ
  have hφ' : d.om (R.ι w y) (d.om h Φ) ∈ d.sch := d.ok.dbl.weil.2.1.toIsSplitting.pres _ _ hφ
  have hT := (H.tAll.2.1 F E σ d (d.om h Φ) hφ).2.1 (R.ι w y) (dilT d.cm w i₀ τ) (dilT d.cm w i₀ (-τ))
    (inFrame_dil' R w i₀ τ y hy) 0
  show d.l (d.om (R.ι w y * h) Φ) = Complex.exp (↑τ * ↑d.m) * d.l (d.om h Φ)
  rw [map_mul, Module.End.mul_apply, l_eq_T_zero d _ hφ', hT, Matrix.zero_mul, ← l_eq_T_zero d _ hφ, det_dilT]
  erw [chi_adrU d w τ]
  erw [absE_adrU d.cm w τ]
  rw [one_mul, ← Real.exp_mul, Complex.ofReal_exp]
  congr 2
  push_cast
  ring

end PositivityTheory.SiegelWeilFormula.AStep

end
