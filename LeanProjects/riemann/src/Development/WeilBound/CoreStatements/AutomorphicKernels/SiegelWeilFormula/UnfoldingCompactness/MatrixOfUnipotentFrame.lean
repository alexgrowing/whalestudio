import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AuxiliaryPrimeFunction
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.G2HaarMeasure.CountableRationalPointsDoubled
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.G2HaarMeasure.ContinuousInFrame
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.G2HaarMeasure.IsHaarMeasureDoubledGroup
import Development.WeilBound.ThetaLifts.LatticeBasics.ContinuousFlat
import Development.WeilBound.ThetaLifts.LatticeBasics.IsCompactOfUnits
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.IncMTranspose

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl

namespace PositivityTheory.SiegelWeilFormula.kunf

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {Y : Spc F E n} {b : GL (Fin n ⊕ Fin n) E} {nb : nA σ Y b → G2 σ Y}

instance aeBorel : BorelSpace (AE F E) := ⟨rfl⟩

instance matSC : SecondCountableTopology (Matrix (Fin n) (Fin n) (AE F E)) :=
  inferInstanceAs (SecondCountableTopology (Fin n → Fin n → AE F E))
instance matBorel : BorelSpace (Matrix (Fin n) (Fin n) (AE F E)) := inferInstanceAs (BorelSpace (Fin n → Fin n → AE F E))
instance nATop : IsTopologicalAddGroup (nA σ Y b) := inferInstance
instance nASC : SecondCountableTopology (nA σ Y b) := TopologicalSpace.Subtype.secondCountableTopology _
instance nABorel : BorelSpace (nA σ Y b) := Subtype.borelSpace _
instance borelSpaceDoubledGroup : BorelSpace (G2 σ Y) := GlobalTheory.EisBL.DoubledGroupTopology.borelSpace_doubled_group_eq σ Y

theorem matrix_eq_inFrame_conj (b : GL (Fin n ⊕ Fin n) E) (x : G2 σ Y) :
    mat2 x = incM F b.1 * inFrame b x * incM F (b⁻¹).1 := by
  show mat2 x = incM F b.1 * (incM F (b⁻¹).1 * mat2 x * incM F b.1) * incM F (b⁻¹).1
  simp only [Matrix.mul_assoc, GlobalTheory.EisBL.DoubledParabolic.incM_mul_inv, Matrix.mul_one]
  rw [← Matrix.mul_assoc, GlobalTheory.EisBL.DoubledParabolic.incM_mul_inv, Matrix.one_mul]

theorem inFrame_injective (b : GL (Fin n ⊕ Fin n) E) : Function.Injective (inFrame (σ := σ) (Y := Y) b) := by
  intro x y h
  have e : mat2 x = mat2 y := by rw [matrix_eq_inFrame_conj b x, matrix_eq_inFrame_conj b y, h]
  exact Subtype.ext (Units.ext e)

theorem nb_add (h : IsNMap b nb) (β β' : nA σ Y b) : nb (β + β') = nb β * nb β' := by
  apply inFrame_injective b
  rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, h, h, h, Matrix.fromBlocks_multiply]
  simp [add_comm]

theorem nb_zero (h : IsNMap b nb) : nb 0 = 1 := by
  apply inFrame_injective b
  rw [h, GlobalTheory.EisBL.DoubledParabolic.inFrame_one]
  simp

theorem nb_comm (h : IsNMap b nb) (β β' : nA σ Y b) : nb β * nb β' = nb β' * nb β := by
  rw [← nb_add h, ← nb_add h, add_comm]

theorem nb_neg (h : IsNMap b nb) (β : nA σ Y b) : nb (-β) = (nb β)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← nb_add h, neg_add_cancel, nb_zero h]

theorem matrix_of_unipotent_frame (h : IsNMap b nb) (β : nA σ Y b) :
    mat2 (nb β) = incM F b.1 * Matrix.fromBlocks 1 β.1 0 1 * incM F (b⁻¹).1 := by
  rw [matrix_eq_inFrame_conj b, h]

theorem continuous_nb (h : IsNMap b nb) : Continuous nb := by
  have hc : Continuous fun β : nA σ Y b => incM F b.1 * Matrix.fromBlocks 1 β.1 0 1 * incM F (b⁻¹).1 :=
    (continuous_const.matrix_mul (Continuous.matrix_fromBlocks continuous_const continuous_subtype_val
      continuous_const continuous_const)).matrix_mul continuous_const
  refine continuous_induced_rng.2 (Units.continuous_iff.2 ⟨?_, ?_⟩)
  · exact hc.congr fun β => (matrix_of_unipotent_frame h β).symm
  · refine (hc.comp continuous_neg).congr fun β => ?_
    show _ = mat2 (nb β)⁻¹
    rw [← nb_neg h, matrix_of_unipotent_frame h]
    rfl

theorem nmat_form (e : AE F E) (β : Matrix (Fin n) (Fin n) (AE F E)) :
    (Matrix.fromBlocks 1 β 0 1)ᵀ * jw n e * (Matrix.fromBlocks 1 β 0 1).map (cA σ) =
      Matrix.fromBlocks 0 1 (e • 1) (e • β.map (cA σ) + βᵀ) := by
  simp only [jw, Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply, Matrix.transpose_one,
    Matrix.transpose_zero]
  have h1 : (1 : Matrix (Fin n) (Fin n) (AE F E)).map (cA σ) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have h0 : (0 : Matrix (Fin n) (Fin n) (AE F E)).map (cA σ) = 0 := Matrix.map_zero _ (map_zero _)
  rw [h1, h0]
  simp

theorem mem_nA_iff {ε : ℤˣ} (hε : b.1ᵀ * dbl Y.J * b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0)
    (β : Matrix (Fin n) (Fin n) (AE F E)) : β ∈ nA σ Y b ↔ βᵀ = -((((ε : ℤ) : AE F E)) • β.map (cA σ)) := by
  refine ⟨fun hβ => ?_, fun hβ => ?_⟩
  · induction hβ using AddSubgroup.closure_induction with
    | mem β h =>
      obtain ⟨x, hx⟩ := h
      have h2 := frame_eq hε x
      rw [hx, nmat_form] at h2
      have h3 := (Matrix.fromBlocks_inj.1 h2).2.2.2
      rw [← sub_eq_zero, sub_neg_eq_add, add_comm]
      exact h3
    | zero => simp
    | add β β' _ _ h h' =>
      rw [Matrix.transpose_add, h, h', Matrix.map_add _ (map_add _), smul_add, neg_add]
    | neg β _ h =>
      rw [Matrix.transpose_neg, h, Matrix.map_neg _ (map_neg _), smul_neg]
  · obtain ⟨x, hx⟩ := exists_of_frame hε (Matrix.fromBlocks 1 β 0 1) (Matrix.fromBlocks 1 (-β) 0 1)
      (by simp [Matrix.fromBlocks_multiply]) (by
        rw [nmat_form, hβ, add_neg_cancel]
        rfl)
    exact AddSubgroup.subset_closure ⟨x, hx⟩

theorem mem_nF_iff {ν : nA σ Y b} : ν ∈ nF σ Y b ↔ ∃ T : Matrix (Fin n) (Fin n) E, ν.1 = incM F T := by
  refine ⟨fun hν => ?_, fun hν => AddSubgroup.subset_closure hν⟩
  induction hν using AddSubgroup.closure_induction with
  | mem _ h => exact h
  | zero => exact ⟨0, by simp [incM]⟩
  | add _ _ _ _ h h' =>
    obtain ⟨T, hT⟩ := h
    obtain ⟨T', hT'⟩ := h'
    exact ⟨T + T', by rw [AddSubgroup.coe_add, hT, hT']; simp [incM, Matrix.map_add]⟩
  | neg _ _ h =>
    obtain ⟨T, hT⟩ := h
    exact ⟨-T, by rw [AddSubgroup.coe_neg, hT]; simp [incM, Matrix.map_neg]⟩

theorem rat_of_inFrame {x : G2 σ Y} {M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) E} (h : inFrame b x = incM F M) :
    x ∈ rat2 σ Y := by
  have hinv : incM F M * inFrame b x⁻¹ = 1 := by
    rw [← h, ← GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, mul_inv_cancel, GlobalTheory.EisBL.DoubledParabolic.inFrame_one]
  have hdet : M.det ≠ 0 := fun h0 => by
    have := congrArg Matrix.det hinv
    rw [Matrix.det_mul, Matrix.det_one, incM, show (M.map (inclR (F := F) (AF F))).det = inclR (F := F) (AF F) M.det from
      (RingHom.map_det _ M).symm, h0, map_zero, zero_mul] at this
    exact zero_ne_one this
  let g : GL (Fin n ⊕ Fin n) E := b * Matrix.GeneralLinearGroup.mkOfDetNeZero M hdet * b⁻¹
  refine Subgroup.mem_subgroupOf.2 ⟨g, Units.ext ?_⟩
  show (g.1).map (inclR (F := F) (AF F)) = mat2 x
  rw [matrix_eq_inFrame_conj b x, h]
  simp only [g, Units.val_mul, Matrix.GeneralLinearGroup.val_mkOfDetNeZero, Matrix.map_mul]
  rfl

theorem nb_rat (h : IsNMap b nb) {ν : nA σ Y b} (hν : ν ∈ nF σ Y b) : nb ν ∈ rat2 σ Y := by
  obtain ⟨T, hT⟩ := mem_nF_iff.1 hν
  refine rat_of_inFrame (b := b) (M := Matrix.fromBlocks 1 T 0 1) ?_
  rw [h, hT]
  simp [incM, Matrix.fromBlocks_map]

instance countable_nF : Countable (nF σ Y b) := by
  have : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  have : Countable (Matrix (Fin n) (Fin n) E) := inferInstanceAs (Countable (Fin n → Fin n → E))
  refine Function.Injective.countable (f := fun ν : nF σ Y b => Classical.choose (mem_nF_iff.1 ν.2)) ?_
  intro x y hxy
  have hx := Classical.choose_spec (mem_nF_iff.1 x.2)
  have hy := Classical.choose_spec (mem_nF_iff.1 y.2)
  apply Subtype.ext; apply Subtype.ext
  rw [hx, hy]
  exact congrArg _ hxy

theorem trace_inclR (e : E) :
    Algebra.trace (AF F) (AE F E) (inclR (F := F) (AF F) e) = algebraMap F (AF F) (Algebra.trace F E e) := by
  show Algebra.trace (AF F) (AF F ⊗[F] E) ((1 : AF F) ⊗ₜ[F] e) = _
  rw [Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange]

theorem tt_rat (M : Matrix (Fin n) (Fin n) E) :
    Algebra.trace (AF F) (AE F E) (incM F M).trace = algebraMap F (AF F) (Algebra.trace F E M.trace) := by
  rw [← trace_inclR]
  congr 1
  simp [incM, Matrix.trace, map_sum]

theorem psi_rat {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (T ν : nF σ Y b) :
    ψ (Algebra.trace (AF F) (AE F E) (T.1.1 * ν.1.1).trace) = 1 := by
  obtain ⟨A, hA⟩ := mem_nF_iff.1 T.2
  obtain ⟨B, hB⟩ := mem_nF_iff.1 ν.2
  rw [hA, hB, incM, incM, ← Matrix.map_mul, ← incM, tt_rat]
  exact hψ.2.1 _

end PositivityTheory.SiegelWeilFormula.kunf

end
