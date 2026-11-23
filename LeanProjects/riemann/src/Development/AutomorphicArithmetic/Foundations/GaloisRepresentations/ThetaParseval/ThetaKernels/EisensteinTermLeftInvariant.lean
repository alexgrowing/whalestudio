import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.EisensteinNormSumRationalInvariant
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LiftedSchrodingerDatum
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.EisensteinSecondTerm
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilActDefs
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.EisensteinNormSumInvariantRight
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ExtensionByZeroAtBaseIndex
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.BMatK
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.UnipotentNilpotentMulEqZero
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.BlockDiagonalPreservesFormIff
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKawayDecG
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.PadMatrixLowerBlockZero

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.Act.C5
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d)
theorem uA_zero_k : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L 0 = 1 := by simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k]
theorem uA_col_k (u : Fin L.n → AE F E) (j : Fin d.n) : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L u j L.i₀ = if j = L.i₀ then 1 else 0 := by
  simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k, Matrix.add_apply, Matrix.sum_apply, Matrix.single_apply, Matrix.one_apply, fun k => (_root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.em_ne_k L k),
    fun k => (_root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.em_ne_k L k).symm]
theorem uA_mul_aB_k (u : Fin L.n → AE F E) (δ : E) (a : AF F) : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L u * _root_.PositivityTheory.SiegelWeilFormula.Act.C5.aB_k L δ a = _root_.PositivityTheory.SiegelWeilFormula.Act.C5.aB_k L δ a := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.aB_k, add_mul, one_mul, Finset.sum_mul]
  rw [Finset.sum_eq_zero fun j _ => Matrix.single_mul_single_of_ne _ _ _ _ (_root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.em_ne_k L j) _, add_zero]
theorem aB_mul_D_k (u : Fin L.n → AE F E) (δ : E) (a : AF F) : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.aB_k L δ a * (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L u)ᵀ.map (cA σ) = _root_.PositivityTheory.SiegelWeilFormula.Act.C5.aB_k L δ a := by
  ext i j
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.aB_k, Matrix.mul_apply, Matrix.single_apply, Matrix.map_apply, Matrix.transpose_apply]
  by_cases hi : L.i₀ = i
  · subst hi
    by_cases hj : j = L.i₀
    · subst hj; simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_col_k]
    · simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_col_k, hj, Ne.symm hj]
  · simp [hi]
theorem aB_add_k (δ : E) (a a' : AF F) : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.aB_k L δ (a + a') = _root_.PositivityTheory.SiegelWeilFormula.Act.C5.aB_k L δ a + _root_.PositivityTheory.SiegelWeilFormula.Act.C5.aB_k L δ a' := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.aB_k, add_smul, Matrix.single_add]
theorem sB_add_k (b b' : Fin L.n → AE F E) : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sB_k R L (b + b') = _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sB_k R L b + _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sB_k R L b' := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sB_k, Pi.add_apply, map_add, mul_add, neg_add, Matrix.single_add, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => by abel
theorem index_cases_sum (r : Fin d.n ⊕ Fin d.n) : r = Sum.inl L.i₀ ∨ r = Sum.inr L.i₀ ∨ ∃ a, r = Sum.map L.em L.em a := by
  rcases r with i | i <;> rcases _root_.PositivityTheory.SiegelWeilFormula.Act.C5.idx_k L i with rfl | ⟨k, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr (Or.inr ⟨Sum.inl k, rfl⟩)
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr ⟨Sum.inr k, rfl⟩)
def padB_k (β : Matrix (Fin L.n) (Fin L.n) (AE F E)) : Matrix (Fin d.n) (Fin d.n) (AE F E) :=
  ∑ k, ∑ l, Matrix.single (L.em k) (L.em l) (β k l)
theorem pad_block_row_zero (β : Matrix (Fin L.n) (Fin L.n) (AE F E)) (j : Fin d.n) : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.padB_k L β L.i₀ j = 0 := by
  simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.padB_k, Matrix.sum_apply, Matrix.single_apply, fun k => _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.em_ne_k L k]
theorem pad_block_column_zero (β : Matrix (Fin L.n) (Fin L.n) (AE F E)) (i : Fin d.n) : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.padB_k L β i L.i₀ = 0 := by
  simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.padB_k, Matrix.sum_apply, Matrix.single_apply, fun k => _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.em_ne_k L k]
theorem padB_em_k (β : Matrix (Fin L.n) (Fin L.n) (AE F E)) (k l : Fin L.n) : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.padB_k L β (L.em k) (L.em l) = β k l := by
  simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.padB_k, Matrix.sum_apply, Matrix.single_apply, L.inj.eq_iff, ite_and, Finset.sum_ite_eq']
theorem mem_ratV_k {b : Fin L.n → AE F E} (hb : b ∈ L.ratV) : ∃ x : Fin L.n → E, b = GlobalTheory.ThK.incV F x := by
  let φ : (Fin L.n → E) →+ (Fin L.n → AE F E) :=
    AddMonoidHom.compLeft (inclR (F := F) (E := E) (AF F)).toAddMonoidHom (Fin L.n)
  have hle : L.ratV ≤ φ.range := (AddSubgroup.closure_le _).2 (by rintro _ ⟨x, rfl⟩; exact ⟨x, rfl⟩)
  obtain ⟨x, hx⟩ := hle hb
  exact ⟨x, hx.symm⟩
variable {R L}
variable {nb : nA σ d.Y d.b → d.G} {uM : (Fin L.n → AE F E) → d.G} {nb' : nA σ L.Y L.b → G2 σ L.Y} {w₁ : d.G}
  {cM : (Fin L.n → AE F E) × AF F → d.G} {δ : E}
theorem inFrame_uM'_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) (u : Fin L.n → AE F E) :
    inFrame d.b (uM u) = Matrix.fromBlocks (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L u) 0 0 ((_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L (-u))ᵀ.map (cA σ)) := by
  obtain ⟨a', ha⟩ := h.uM u
  rw [ha, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.lr_of_k ha (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_mul_neg_k L u)]
theorem inFrame_jn_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) (β : nA σ L.Y L.b) :
    inFrame d.b (L.j (nb' β)) = Matrix.fromBlocks 1 (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.padB_k L β.1) 0 1 := by
  have hin : ∀ a b, inFrame d.b (L.j (nb' β)) (Sum.map L.em L.em a) (Sum.map L.em L.em b) = inFrame L.b (nb' β) a b :=
    fun a b => congrFun (congrFun (L.j_in (nb' β)) a) b
  ext r c
  rcases _root_.PositivityTheory.SiegelWeilFormula.Act.C5.index_cases_sum L r with rfl | rfl | ⟨a, rfl⟩
  · rw [(L.j_out _ _ (by simp) c).1]
    rcases c with c | c <;> simp [Matrix.one_apply, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.pad_block_row_zero]
  · rw [(L.j_out _ _ (by simp) c).1]
    rcases c with c | c <;> simp [Matrix.one_apply]
  · rcases _root_.PositivityTheory.SiegelWeilFormula.Act.C5.index_cases_sum L c with rfl | rfl | ⟨b, rfl⟩
    · rw [(L.j_out _ _ (by simp) _).2]
      rcases a with a | a <;> simp [Matrix.one_apply, _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.em_ne_k]
    · rw [(L.j_out _ _ (by simp) _).2]
      rcases a with a | a <;> simp [Matrix.one_apply, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.pad_block_column_zero, _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.em_ne_k]
    · rw [hin, h.nb' β]
      rcases a with a | a <;> rcases b with b | b <;> simp [Matrix.one_apply, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.padB_em_k, L.inj.eq_iff]
theorem frame_centre_block_form (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) (a : AF F) :
    inFrame d.b (cM (0, a)) = Matrix.fromBlocks 1 (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.aB_k L δ a) 0 1 := by
  rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.inFrame_cM_k h]
  simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_zero_k, Matrix.transpose_one]
theorem sM_add_k (b b' : Fin L.n → AE F E) : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L (b + b') = _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L b * _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L b' := by
  apply _root_.PositivityTheory.SiegelWeilFormula.KAway.inFrame_inj_k d
  rw [_root_.PositivityTheory.SiegelWeilFormula.KAway.inFrame_mul_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.inFrame_sM'_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.inFrame_sM'_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.inFrame_sM'_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sB_add_k]
  exact (kfour.nM_mul _ _).symm
theorem cM_split_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) (u : Fin L.n → AE F E) (a : AF F) : cM (u, a) = uM u * cM (0, a) := by
  apply _root_.PositivityTheory.SiegelWeilFormula.KAway.inFrame_inj_k d
  rw [_root_.PositivityTheory.SiegelWeilFormula.KAway.inFrame_mul_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.inFrame_cM_k h, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.inFrame_uM'_k h, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.frame_centre_block_form h, Matrix.fromBlocks_multiply]
  simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_mul_aB_k]
theorem cM_comm_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) (u : Fin L.n → AE F E) (a : AF F) : uM u * cM (0, a) = cM (0, a) * uM u := by
  apply _root_.PositivityTheory.SiegelWeilFormula.KAway.inFrame_inj_k d
  rw [_root_.PositivityTheory.SiegelWeilFormula.KAway.inFrame_mul_k, _root_.PositivityTheory.SiegelWeilFormula.KAway.inFrame_mul_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.inFrame_uM'_k h, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.frame_centre_block_form h, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply]
  simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_mul_aB_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.aB_mul_D_k]
theorem centre_additive (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) (a a' : AF F) : cM (0, a + a') = cM (0, a) * cM (0, a') := by
  apply _root_.PositivityTheory.SiegelWeilFormula.KAway.inFrame_inj_k d
  rw [_root_.PositivityTheory.SiegelWeilFormula.KAway.inFrame_mul_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.frame_centre_block_form h, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.frame_centre_block_form h, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.frame_centre_block_form h, Matrix.fromBlocks_multiply, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.aB_add_k]
  simp [add_comm]
theorem unipotent_commutes_centre (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) (b : Fin L.n → AE F E) (a : AF F) : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L b * cM (0, a) = cM (0, a) * _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L b := by
  apply _root_.PositivityTheory.SiegelWeilFormula.KAway.inFrame_inj_k d
  rw [_root_.PositivityTheory.SiegelWeilFormula.KAway.inFrame_mul_k, _root_.PositivityTheory.SiegelWeilFormula.KAway.inFrame_mul_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.frame_centre_block_form h, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.inFrame_sM'_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.bMat_k, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply]
  simp [add_comm]
theorem nb_split_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) (β : nA σ d.Y d.b) :
    nb β = L.j (nb' (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β)) * (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.pb_k L β) * cM (0, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.pa_k L δ β)) := by
  have hc : β.1ᵀ = -((((R.ε : ℤ) : AE F E)) • β.1.map (cA σ)) := (kfour.mem_nA_iff (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.nilpotentMap_add d) R.hε β.1).1 β.2
  have hcij : ∀ i j, β.1 j i = -(((R.ε : ℤ) : AE F E) * cA σ (β.1 i j)) := fun i j => by
    have := congrFun (congrFun hc i) j
    simpa using this
  have e2 := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.eps_mul_k R
  apply _root_.PositivityTheory.SiegelWeilFormula.KAway.inFrame_inj_k d
  rw [_root_.PositivityTheory.SiegelWeilFormula.KAway.inFrame_mul_k, _root_.PositivityTheory.SiegelWeilFormula.KAway.inFrame_mul_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.inFrame_jn_k h, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.inFrame_sM'_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.frame_centre_block_form h, h.nb β, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.bMat_k,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp only [Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  congr 1
  ext i j
  rcases _root_.PositivityTheory.SiegelWeilFormula.Act.C5.idx_k L i with rfl | ⟨k, rfl⟩ <;> rcases _root_.PositivityTheory.SiegelWeilFormula.Act.C5.idx_k L j with rfl | ⟨l, rfl⟩ <;>
    simp only [Matrix.add_apply, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sB_i0i0_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sB_i0em_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.section_entry_embedded_row, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sB_emem_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.pad_block_row_zero, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.pad_block_column_zero, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.padB_em_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.aB_k,
      Matrix.single_apply, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_val_k, Matrix.submatrix_apply, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.pb_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.pa_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.eA_eq_k, fun k => _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.em_ne_k L k,
      fun k => (_root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.em_ne_k L k).symm, and_self, and_false, false_and, if_true, if_false, add_zero, zero_add]
  · have hy : cA σ (β.1 L.i₀ L.i₀) = -(((R.ε : ℤ) : AE F E)) * β.1 L.i₀ L.i₀ := by
      have e := hcij L.i₀ L.i₀
      calc cA σ (β.1 L.i₀ L.i₀) = -(((R.ε : ℤ) : AE F E)) * -(((R.ε : ℤ) : AE F E) * cA σ (β.1 L.i₀ L.i₀)) := by
            rw [neg_mul_neg, ← mul_assoc, e2, one_mul]
        _ = _ := by rw [← e]
    exact (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.eig_k h _ hy).symm
  · exact hcij _ _
theorem j_move_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) (u : Fin L.n → AE F E) (β'' : nA σ L.Y L.b) :
    ∃ (B : Fin L.n → AE F E) (A : AF F), ∀ b a, L.j (nb' β'') * (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L b * cM (u, a)) =
      _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L (b + B) * cM (u, a + A) * L.j (nb' β'') :=
  _root_.PositivityTheory.SiegelWeilFormula.Act.C5.j_move'_k h u β''
theorem j_conj_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) (γ' : G2 σ L.Y) :
    ∃ (Λ : ((Fin L.n → AE F E) × (Fin L.n → AE F E)) ≃ₜ+ ((Fin L.n → AE F E) × (Fin L.n → AE F E)))
      (Q : (Fin L.n → AE F E) × (Fin L.n → AE F E) → AF F), Continuous Q ∧
      (∀ b u a, L.j γ' * (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L b * cM (u, a)) = _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L (Λ (b, u)).1 * cM ((Λ (b, u)).2, a + Q (b, u)) * L.j γ') ∧
      (γ' ∈ rat2 σ L.Y → ∀ w, w ∈ (L.ratV.prod L.ratV : AddSubgroup _) ↔ Λ w ∈ (L.ratV.prod L.ratV : AddSubgroup _)) :=
  _root_.PositivityTheory.SiegelWeilFormula.Act.C5.j_conj'_k h γ'
theorem heis_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) :
    ∃ Z : (Fin L.n → AE F E) → (Fin L.n → AE F E) → AF F, Continuous (Function.uncurry Z) ∧
      (∀ u₀ b, u₀ ∈ L.ratV → b ∈ L.ratV → Z u₀ b ∈ (algebraMap F (AF F)).range) ∧
      ∀ u₀ a₀ b u a, cM (u₀, a₀) * (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L b * cM (u, a)) = _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L b * cM (u₀ + u, a₀ + a + Z u₀ b) :=
  _root_.PositivityTheory.SiegelWeilFormula.Act.C5.heis'_k h
theorem section_unipotent_invariant (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) {s₁ : ℂ} {f : d.G → ℂ} (hf : IsSec d.K d.χ s₁ f) (z : ℂ)
    (b : Fin L.n → AE F E) (g : d.G) : _root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (w₁ * (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L b * g)) = _root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (w₁ * g) :=
  _root_.PositivityTheory.SiegelWeilFormula.Act.C5.section_unipotent_invariant_weyl h hf z b g
theorem sM_rat_k {b : Fin L.n → AE F E} (hb : b ∈ L.ratV) : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L b ∈ rat2 σ d.Y := by
  obtain ⟨x, rfl⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.mem_ratV_k L hb
  refine kunf.rat_of_inFrame (b := d.b) (M := Matrix.fromBlocks 1 (∑ j, (Matrix.single L.i₀ (L.em j) (x j) +
    Matrix.single (L.em j) L.i₀ (-(((R.ε : ℤ) : E) * σ (x j))))) 0 1) ?_
  rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.inFrame_sM'_k]
  ext r c
  rcases r with i | i <;> rcases c with j | j <;>
    simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.bMat_k, incM, Matrix.map_apply, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sB_k, Matrix.sum_apply, Matrix.add_apply, Matrix.single_apply, Matrix.one_apply,
      map_sum, apply_ite (inclR (F := F) (E := E) (AF F)), GlobalTheory.ThK.incV, GlobalTheory.EisBL.DoubledUnipotentRadical.cA_inclR, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.eA_k, map_neg, map_mul,
      map_intCast]
theorem cM_rat_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) {c : (Fin L.n → AE F E) × AF F} (hu : c.1 ∈ L.ratV)
    (ha : c.2 ∈ (algebraMap F (AF F)).range) : cM c ∈ rat2 σ d.Y := by
  obtain ⟨c1, c2⟩ := c
  obtain ⟨x, rfl⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.mem_ratV_k L hu
  obtain ⟨t, rfl⟩ := ha
  refine kunf.rat_of_inFrame (b := d.b) (M := Matrix.fromBlocks (1 + ∑ j, Matrix.single L.i₀ (L.em j) (x j))
    (Matrix.single L.i₀ L.i₀ (t • δ)) 0 ((1 + ∑ j, Matrix.single L.i₀ (L.em j) (-(x j)))ᵀ.map σ)) ?_
  rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.inFrame_cM_k h]
  ext r c
  rcases r with i | i <;> rcases c with j | j <;>
    simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.aB_k, incM, Matrix.map_apply, Matrix.sum_apply, Matrix.add_apply, Matrix.single_apply, Matrix.one_apply,
      Matrix.transpose_apply, map_sum, apply_ite (inclR (F := F) (E := E) (AF F)), apply_ite (cA σ), apply_ite (⇑σ), GlobalTheory.ThK.incV,
      GlobalTheory.EisBL.DoubledUnipotentRadical.cA_inclR, map_neg, inclR_smul]
theorem eisenstein_term_left_invariant {s₁ : ℂ} {f : d.G → ℂ} (hf : IsSec d.K d.χ s₁ f) (z : ℂ) {r : d.G} (hr : r ∈ rat2 σ d.Y)
    (hx : ∀ k, inFrame d.b r k (Sum.inl L.i₀) = (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) k (Sum.inl L.i₀))
    (g : d.G) : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.eisensteinSecondTerm L (_root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z) (r * g) = _root_.PositivityTheory.SiegelWeilFormula.Act.C5.eisensteinSecondTerm L (_root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z) g :=
  _root_.PositivityTheory.SiegelWeilFormula.Act.C5.eisenstein_term_right_invariant hf z hr hx g
theorem eisenstein_norm_sum_invariant {s₁ : ℂ} {f : d.G → ℂ} (hf : IsSec d.K d.χ s₁ f) (z : ℂ) {r : d.G} (hr : r ∈ rat2 σ d.Y)
    (hx : ∀ k, inFrame d.b r k (Sum.inl L.i₀) = (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) k (Sum.inl L.i₀))
    (g : d.G) : ∑' q : {q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d // ¬ _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q)}, ‖_root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q.1 * (r * g))‖ₑ =
      ∑' q : {q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d // ¬ _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q)}, ‖_root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q.1 * g)‖ₑ :=
  _root_.PositivityTheory.SiegelWeilFormula.Act.C5.eisenstein_norm_sum_invariant_right hf z hr hx g
theorem fix_sM_k (b : Fin L.n → AE F E) (k) :
    inFrame d.b (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L b) k (Sum.inl L.i₀) = (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) k (Sum.inl L.i₀) := by
  rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.inFrame_sM'_k]
  rcases k with k | k <;> simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.bMat_k, Matrix.one_apply]
theorem fix_cM_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) (c : (Fin L.n → AE F E) × AF F) (k) :
    inFrame d.b (cM c) k (Sum.inl L.i₀) = (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) k (Sum.inl L.i₀) := by
  rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.inFrame_cM_k h]
  rcases k with k | k <;> simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_col_k, Matrix.one_apply]
theorem fix_nb_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) (β : nA σ d.Y d.b) (k) :
    inFrame d.b (nb β) k (Sum.inl L.i₀) = (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) k (Sum.inl L.i₀) := by
  rw [h.nb β]
  rcases k with k | k <;> simp [Matrix.one_apply]
end PositivityTheory.SiegelWeilFormula.Act.C5
end
end
