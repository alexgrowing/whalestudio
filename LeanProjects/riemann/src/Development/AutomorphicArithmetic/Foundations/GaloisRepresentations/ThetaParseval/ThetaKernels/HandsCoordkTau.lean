import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RationalCoordinates.RationalCoordinateCountability.ContinuousFrameUM
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LiftedSchrodingerDatum
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.BMatK
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.UnipotentNilpotentMulEqZero
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.BlockDiagonalPreservesFormIff
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.EisensteinSecondTerm
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKawayDecG
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.EisensteinTermLeftInvariant

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal ENNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.Act.C5.CoordK
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} {R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d} {L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d}
variable {nb : nA σ d.Y d.b → d.G} {uM : (Fin L.n → AE F E) → d.G} {nb' : nA σ L.Y L.b → G2 σ L.Y} {w₁ : d.G}
  {cM : (Fin L.n → AE F E) × AF F → d.G} {δ : E}
variable (L) in
def kom_k (uM : (Fin L.n → AE F E) → d.G) (nb' : nA σ L.Y L.b → G2 σ L.Y) (p : (Fin L.n → AE F E) × nA σ L.Y L.b) : d.G :=
  L.j (nb' p.2) * uM p.1 * (L.j (nb' p.2))⁻¹ * (uM p.1)⁻¹
variable (L) in
def tau_k (uM : (Fin L.n → AE F E) → d.G) (nb' : nA σ L.Y L.b → G2 σ L.Y) (δ : E) (p : (Fin L.n → AE F E) × nA σ L.Y L.b) :
    (Fin L.n → AE F E) × AF F :=
  (fun k => inFrame d.b (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.kom_k L uM nb' p) (Sum.inl L.i₀) (Sum.inr (L.em k)),
    ellA δ (inFrame d.b (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.kom_k L uM nb' p) (Sum.inl L.i₀) (Sum.inr L.i₀)))
variable (L) in
def Du_k (u : Fin L.n → AE F E) : Matrix (Fin d.n) (Fin d.n) (AE F E) := (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L (-u))ᵀ.map (cA σ)
theorem frame_uM_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) (u : Fin L.n → AE F E) :
    inFrame d.b (uM u) = Matrix.fromBlocks (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L u) 0 0 (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.Du_k L u) := by
  obtain ⟨a', ha⟩ := h.uM u
  rw [ha, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.lr_of_k ha (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_mul_neg_k L u)]
  rfl
theorem Du_mul_k (u : Fin L.n → AE F E) : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.Du_k (σ := σ) L u * _root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.Du_k L (-u) = 1 := by
  unfold _root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.Du_k
  rw [← Matrix.map_mul, ← Matrix.transpose_mul, neg_neg, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_mul_neg_k L u]
  ext i j
  simp [Matrix.one_apply, Matrix.map_apply]
theorem uM_neg'_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) (u : Fin L.n → AE F E) : uM (-u) = (uM u)⁻¹ := by
  refine eq_inv_of_mul_eq_one_right (_root_.PositivityTheory.SiegelWeilFormula.KAway.inFrame_inj_k d ?_)
  rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.frame_uM_k h, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.frame_uM_k h, GlobalTheory.EisBL.DoubledParabolic.inFrame_one, Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_mul_neg_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.Du_mul_k, Matrix.fromBlocks_one]
theorem continuous_uA_k : Continuous (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k (σ := σ) L) := by
  unfold _root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k
  refine continuous_const.add (continuous_finsetSum _ fun j _ => ?_)
  have e : (fun b : Fin L.n → AE F E => Matrix.single L.i₀ (L.em j) (b j)) =
      fun b => b j • Matrix.single L.i₀ (L.em j) (1 : AE F E) := by
    funext b; rw [Matrix.smul_single, smul_eq_mul, mul_one]
  rw [e]; exact (continuous_apply j).smul continuous_const
theorem continuous_frame_uM_k : Continuous fun u : Fin L.n → AE F E =>
    (Matrix.fromBlocks (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L u) 0 0 (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.Du_k (σ := σ) L u) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) := by
  refine Continuous.matrix_fromBlocks _root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.continuous_uA_k continuous_const continuous_const ?_
  unfold _root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.Du_k
  exact ((_root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.continuous_uA_k.comp continuous_neg).matrix_transpose).matrix_map (GlobalTheory.EisBL.DoubledGroupTopology.continuous_cA σ)
theorem frame_kom_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) (p : (Fin L.n → AE F E) × nA σ L.Y L.b) :
    inFrame d.b (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.kom_k L uM nb' p) = inFrame d.b (L.j (nb' p.2)) * Matrix.fromBlocks (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L p.1) 0 0 (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.Du_k L p.1) *
      inFrame d.b (L.j (nb' (-p.2))) * Matrix.fromBlocks (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L (-p.1)) 0 0 (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.Du_k L (-p.1)) := by
  unfold _root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.kom_k
  rw [← _root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.uM_neg'_k h, ← map_inv, ← kunf.nb_neg h.nb', GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, GlobalTheory.EisBL.DoubledParabolic.inFrame_mul,
    GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.frame_uM_k h, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.frame_uM_k h]
theorem continuous_kom_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) : Continuous fun p => inFrame d.b (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.kom_k L uM nb' p) := by
  have hj : Continuous fun β : nA σ L.Y L.b => inFrame d.b (L.j (nb' β)) :=
    (GlobalTheory.EisBL.DoubledParabolic.continuous_inFrame d.b).comp (L.cont.comp (kunf.continuous_nb h.nb'))
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.frame_kom_k h]
  exact (((hj.comp continuous_snd).matrix_mul (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.continuous_frame_uM_k.comp continuous_fst)).matrix_mul
    ((hj.comp continuous_neg).comp continuous_snd)).matrix_mul ((_root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.continuous_frame_uM_k.comp continuous_neg).comp continuous_fst)
theorem continuous_tau_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) : Continuous (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.tau_k L uM nb' δ) := by
  have hk := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.continuous_kom_k h
  refine Continuous.prodMk (continuous_pi fun k => hk.matrix_elem _ _) ?_
  exact (IsModuleTopology.continuous_of_linearMap (R := AF F) (ellA δ)).comp (hk.matrix_elem _ _)
theorem Du_neg_row_k (u : Fin L.n → AE F E) (k : Fin d.n) :
    _root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.Du_k (σ := σ) L (-u) L.i₀ k = if k = L.i₀ then 1 else 0 := by
  unfold _root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.Du_k
  rw [neg_neg, Matrix.map_apply, Matrix.transpose_apply]
  by_cases hk : k = L.i₀
  · subst hk
    simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k, Matrix.add_apply, Matrix.sum_apply, Matrix.single_apply, Matrix.one_apply, fun j => _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.em_ne_k L j]
  · simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k, Matrix.add_apply, Matrix.sum_apply, Matrix.single_apply, Matrix.one_apply, hk, Ne.symm hk]
theorem sM_zero'_k : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L 0 = 1 := by
  apply _root_.PositivityTheory.SiegelWeilFormula.KAway.inFrame_inj_k d
  rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.inFrame_sM'_k, GlobalTheory.EisBL.DoubledParabolic.inFrame_one]
  have : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sB_k R L 0 = 0 := by simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sB_k]
  rw [this, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.bMat_k, Matrix.fromBlocks_one]
theorem cM_zero'_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) (u : Fin L.n → AE F E) : cM (u, 0) = uM u := by
  apply _root_.PositivityTheory.SiegelWeilFormula.KAway.inFrame_inj_k d
  rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.inFrame_cM_k h, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.frame_uM_k h]
  simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.aB_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.Du_k]
theorem move_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) (u : Fin L.n → AE F E) (β'' : nA σ L.Y L.b) (b : Fin L.n → AE F E) (a : AF F) :
    L.j (nb' β'') * (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L b * cM (u, a)) =
      _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L (b + (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.tau_k L uM nb' δ (u, β'')).1) * cM (u, a + (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.tau_k L uM nb' δ (u, β'')).2) * L.j (nb' β'') := by
  obtain ⟨B, A, hBA⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.j_move_k (R := R) h u β''
  suffices hτ : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.tau_k L uM nb' δ (u, β'') = (B, A) by rw [hτ]; exact hBA b a
  have e0 := hBA 0 0
  rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.sM_zero'_k, one_mul, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.cM_zero'_k h, zero_add, zero_add] at e0
  have hk : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.kom_k L uM nb' (u, β'') = _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L B * cM (u, A) * (uM u)⁻¹ := by
    show L.j (nb' β'') * uM u * (L.j (nb' β''))⁻¹ * (uM u)⁻¹ = _
    rw [e0, mul_inv_cancel_right]
  have hf : inFrame d.b (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.kom_k L uM nb' (u, β'')) =
      Matrix.fromBlocks 1 (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.aB_k L δ A * _root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.Du_k L (-u) + _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sB_k R L B) 0 1 := by
    rw [hk, ← _root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.uM_neg'_k h, GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.inFrame_sM'_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.inFrame_cM_k h, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.frame_uM_k h, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.bMat_k]
    rw [show (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L (-u))ᵀ.map (cA σ) = _root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.Du_k L u from rfl]
    simp only [Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.one_mul,
      Matrix.mul_one, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_mul_neg_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.Du_mul_k]
    rw [Matrix.add_mul, Matrix.mul_assoc, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.Du_mul_k, Matrix.mul_one]
  have hrow : ∀ k, (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.aB_k L δ A * _root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.Du_k (σ := σ) L (-u)) L.i₀ k = if k = L.i₀ then A • inclR (F := F) (AF F) δ else 0 := by
    intro k
    rw [Matrix.mul_apply, Finset.sum_eq_single L.i₀]
    · rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.Du_neg_row_k]; simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.aB_k]
    · intro m _ hm; simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.aB_k, Matrix.single_apply, Ne.symm hm]
    · simp
  refine Prod.ext (funext fun k => ?_) ?_
  · show inFrame d.b (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.kom_k L uM nb' (u, β'')) (Sum.inl L.i₀) (Sum.inr (L.em k)) = B k
    rw [hf, Matrix.fromBlocks_apply₁₂, Matrix.add_apply, hrow, if_neg (_root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.em_ne_k L k), zero_add, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sB_i0em_k]
  · show ellA δ (inFrame d.b (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.kom_k L uM nb' (u, β'')) (Sum.inl L.i₀) (Sum.inr L.i₀)) = A
    rw [hf, Matrix.fromBlocks_apply₁₂, Matrix.add_apply, hrow, if_pos rfl, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sB_i0i0_k, add_zero, map_smul, ellA_self h.δ0,
      smul_eq_mul, mul_one]
end PositivityTheory.SiegelWeilFormula.Act.C5.CoordK
end
end
