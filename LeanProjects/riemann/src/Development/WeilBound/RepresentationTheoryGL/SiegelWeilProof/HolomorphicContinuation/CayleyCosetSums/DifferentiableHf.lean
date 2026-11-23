import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.InverseSecondBlockEqNegConjTranspose
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.SpanUnitaryMatrix
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.TsContinuousNU
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.HolParam

noncomputable section

open Matrix MeasureTheory Filter Topology
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.HSt.CompactCayleyBlocks

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.HSt PositivityTheory.Rg.Sw.HSt.LoweringDerivative

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def Hf (m : ℕ) (e : ℤ) (ψ : (Fin n → Fin n → ℝ) → ℂ) (a b : M2 n) (z : ℂ) (y : M2 n) : ℂ :=
  ∫ t, fz m e z (y * a * nU (herm t) * b) * ψ t

theorem isClosed_G : IsClosed {x : M2 n | InG x} := by
  show IsClosed {x : M2 n | xᴴ * JJ n * x = JJ n}
  exact isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
    continuous_const

instance instLC : LocallyCompactSpace (M2 n) :=
  inferInstanceAs (LocallyCompactSpace (Fin n ⊕ Fin n → Fin n ⊕ Fin n → ℂ))

instance instFC : FirstCountableTopology (M2 n) :=
  inferInstanceAs (FirstCountableTopology (Fin n ⊕ Fin n → Fin n ⊕ Fin n → ℂ))

def Gs (n : ℕ) : Set (M2 n) := {x | InG x}

theorem continuousAt_fz {x : M2 n} (hx : InG x) (m : ℕ) (e : ℤ) (z : ℂ) :
    ContinuousAt (fun p : M2 n × ℂ => fz m e p.2 p.1) (x, z) := by
  have hdx : x.det ≠ 0 := (LoweringDerivative.isUnit_det_of_inG hx).ne_zero
  have hdet : Continuous (fun y : M2 n => y.det) := continuous_id.matrix_det
  have hdetn : Continuous (fun M : Matrix (Fin n) (Fin n) ℂ => M.det) := continuous_id.matrix_det
  have hu1 : Continuous (fun y : M2 n => u1 y) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [u1, Matrix.add_apply, Matrix.smul_apply, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂, Matrix.of_apply,
      smul_eq_mul]
    fun_prop
  have hub : ContinuousAt (fun y : M2 n => ub1 y) x :=
    continuousAt_pi.2 fun i => continuousAt_pi.2 fun j =>
      (contDiffOn_inverse_first_block i j).continuousOn.continuousAt (isOpen_det_ne.mem_nhds hdx)
  have hw : (u1 x).det * (ub1 x).det = ((Complex.normSq (u1 x).det : ℝ) : ℂ) := by
    rw [inverse_first_block_eq_conjTranspose hx, Matrix.det_conjTranspose, Complex.star_def, Complex.normSq_eq_conj_mul_self]
    ring
  have hslit : (u1 x).det * (ub1 x).det ∈ Complex.slitPlane := by
    rw [hw, Complex.ofReal_mem_slitPlane]
    exact Complex.normSq_pos.2 (det_first_block_ne_zero_group hx)
  show ContinuousAt (fun p : M2 n × ℂ =>
    p.1.det ^ e * (u1 p.1).det ^ (-(m : ℤ)) * ((u1 p.1).det * (ub1 p.1).det) ^ (-p.2)) (x, z)
  have hA : ContinuousAt (fun p : M2 n × ℂ => p.1.det) (x, z) := (hdet.comp continuous_fst).continuousAt
  have hB : ContinuousAt (fun p : M2 n × ℂ => (u1 p.1).det) (x, z) :=
    ((hu1.comp continuous_fst).matrix_det).continuousAt
  have hub' : ContinuousAt (fun y : M2 n => (ub1 y).det) x := hdetn.continuousAt.comp hub
  have hC : ContinuousAt (fun p : M2 n × ℂ => (ub1 p.1).det) (x, z) :=
    ContinuousAt.comp (g := fun y : M2 n => (ub1 y).det) (f := Prod.fst) (x := (x, z)) hub'
      continuous_fst.continuousAt
  refine ((hA.zpow₀ e (Or.inl hdx)).mul (hB.zpow₀ _ (Or.inl (det_first_block_ne_zero_group hx)))).mul ?_
  exact (hB.mul hC).cpow continuous_snd.neg.continuousAt hslit

theorem inG_path {y a b : M2 n} (hy : InG y) (ha : InG a) (hb : InG b) (t : Fin n → Fin n → ℝ) :
    InG (y * a * nU (herm t) * b) := by
  have hH : (herm t)ᴴ = herm t := by
    ext i j
    simp only [herm, Matrix.conjTranspose_apply, Complex.star_def, map_add, map_div₀, map_mul,
      Complex.conj_ofReal, Complex.conj_I, map_ofNat]
    push_cast
    ring
  have hN : InG (nU (herm t)) := by
    show (nU (herm t))ᴴ * JJ n * nU (herm t) = JJ n
    simp [nU, JJ, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, hH]
  exact inG_mul (inG_mul (inG_mul hy ha) hN) hb

private theorem continuous_nU_herm : Continuous (fun t : Fin n → Fin n → ℝ => nU (herm t)) := by
  have hherm : Continuous (fun t : Fin n → Fin n → ℝ => herm t) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [herm]
    fun_prop
  unfold nU
  exact continuous_const.matrix_fromBlocks hherm continuous_const continuous_const

private theorem continuous_fz_mul_nU_herm_mul {X : Type} [TopologicalSpace X] (m : ℕ) (e : ℤ)
    {ψ : (Fin n → Fin n → ℝ) → ℂ} (hψ : Continuous ψ) {a b : M2 n} (ha : InG a) (hb : InG b)
    (Y : X → M2 n) (hY : Continuous Y) (hYG : ∀ x, InG (Y x)) (Z : X → ℂ) (hZ : Continuous Z)
    (T : X → (Fin n → Fin n → ℝ)) (hT : Continuous T) :
    Continuous fun x => fz m e (Z x) (Y x * a * nU (herm (T x)) * b) * ψ (T x) := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  refine ContinuousAt.mul ?_ (hψ.comp hT).continuousAt
  have hG := inG_path (hYG x) ha hb (T x)
  have hP : Continuous fun x => (Y x * a * nU (herm (T x)) * b, Z x) :=
    (((hY.matrix_mul continuous_const).matrix_mul (continuous_nU_herm.comp hT)).matrix_mul
      continuous_const).prodMk hZ
  exact ContinuousAt.comp (g := fun p : M2 n × ℂ => fz m e p.2 p.1)
    (f := fun x => (Y x * a * nU (herm (T x)) * b, Z x)) (x := x)
    (continuousAt_fz hG m e (Z x)) hP.continuousAt

theorem continuous_Hf (m : ℕ) (e : ℤ) {ψ : (Fin n → Fin n → ℝ) → ℂ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ)
    {a b : M2 n} (ha : InG a) (hb : InG b) :
    Continuous fun q : ↥(Gs n) × ℂ => Hf m e ψ a b q.2 q.1.1 := by
  haveI : LocallyCompactSpace ↥(Gs n) := (isClosed_G (n := n)).locallyCompactSpace
  have hF := continuous_fz_mul_nU_herm_mul (X := (↥(Gs n) × ℂ) × (Fin n → Fin n → ℝ)) m e hψ ha hb
    (fun p => p.1.1.1) (continuous_subtype_val.comp (continuous_fst.comp continuous_fst))
    (fun p => p.1.1.2) (fun p => p.1.2) (continuous_snd.comp continuous_fst) (fun p => p.2) continuous_snd
  have key := continuous_parametric_integral_of_continuous (μ := (volume : Measure (Fin n → Fin n → ℝ)))
    (f := fun (q : ↥(Gs n) × ℂ) t => fz m e q.2 (q.1.1 * a * nU (herm t) * b) * ψ t) hF hψc
  refine key.congr fun q => ?_
  unfold Hf
  exact setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht => by
    rw [image_eq_zero_of_notMem_tsupport ht, mul_zero]

theorem differentiable_Hf (m : ℕ) (e : ℤ) {ψ : (Fin n → Fin n → ℝ) → ℂ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ)
    {a b y : M2 n} (ha : InG a) (hb : InG b) (hy : InG y) : Differentiable ℂ fun z => Hf m e ψ a b z y := by
  have hC : IsCompact (tsupport ψ) := hψc
  haveI : IsFiniteMeasure ((volume : Measure (Fin n → Fin n → ℝ)).restrict (tsupport ψ)) :=
    isFiniteMeasure_restrict.2 hC.measure_lt_top.ne
  have hnull : ((volume : Measure (Fin n → Fin n → ℝ)).restrict (tsupport ψ)) (tsupport ψ)ᶜ = 0 := by
    rw [Measure.restrict_apply' (isClosed_tsupport ψ).measurableSet, Set.compl_inter_self, measure_empty]
  have hF := continuous_fz_mul_nU_herm_mul (X := (Fin n → Fin n → ℝ) × ℂ) m e hψ ha hb (fun _ => y) continuous_const
    (fun _ => hy) (fun p => p.2) continuous_snd (fun p => p.1) continuous_fst
  have hdiff : ∀ t ∈ tsupport ψ,
      DifferentiableOn ℂ (fun z => fz m e z (y * a * nU (herm t) * b) * ψ t) Set.univ := by
    intro t _ z _
    have hG := inG_path hy ha hb t
    have hc : (u1 (y * a * nU (herm t) * b)).det * (ub1 (y * a * nU (herm t) * b)).det ≠ 0 := by
      refine mul_ne_zero (det_first_block_ne_zero_group hG) ?_
      rw [inverse_first_block_eq_conjTranspose hG, Matrix.det_conjTranspose]
      exact star_ne_zero.2 (det_first_block_ne_zero_group hG)
    simp only [fz]
    exact (((differentiableAt_const _).mul (differentiableAt_id.neg.const_cpow (Or.inl hc))).mul_const
      _).differentiableWithinAt
  have main := (AbsSt.holParam (Fin n → Fin n → ℝ) ((volume : Measure (Fin n → Fin n → ℝ)).restrict (tsupport ψ))
    (tsupport ψ) hC hnull Set.univ (fun t z => fz m e z (y * a * nU (herm t) * b) * ψ t) isOpen_univ
    hF.continuousOn hdiff).1
  rw [differentiableOn_univ] at main
  have hEq : ∀ z, Hf m e ψ a b z y = ∫ t in tsupport ψ, fz m e z (y * a * nU (herm t) * b) * ψ t := by
    intro z
    unfold Hf
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht => by
      rw [image_eq_zero_of_notMem_tsupport ht, mul_zero]).symm
  simp only [hEq]
  exact main

end PositivityTheory.Rg.Sw.HSt.CompactCayleyBlocks
