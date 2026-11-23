import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.FirstChernHodgeTateFacts
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LiftedSchrodingerDatum
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.CAInjectiveK
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ContinuousCjK

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.Act.C1
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} {L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d} {uM : (Fin L.n → AE F E) → d.G} {ν : Measure (Fin L.n → AE F E)}
  {𝓤 : Set (Fin L.n → AE F E)} {nb : nA σ d.Y d.b → d.G}
theorem ratV_inc_k {u : Fin L.n → AE F E} (hu : u ∈ L.ratV) : ∃ v : Fin L.n → E, u = GlobalTheory.ThK.incV F v := by
  induction hu using AddSubgroup.closure_induction with
  | mem _ h => obtain ⟨v, rfl⟩ := h; exact ⟨v, rfl⟩
  | zero => exact ⟨0, funext fun i => by simp [GlobalTheory.ThK.incV]⟩
  | add _ _ _ _ h h' =>
    obtain ⟨v, rfl⟩ := h; obtain ⟨w, rfl⟩ := h'; exact ⟨v + w, funext fun i => by simp [GlobalTheory.ThK.incV]⟩
  | neg _ _ h => obtain ⟨v, rfl⟩ := h; exact ⟨-v, funext fun i => by simp [GlobalTheory.ThK.incV]⟩
theorem neg_incV_k (v : Fin L.n → E) : -GlobalTheory.ThK.incV F v = GlobalTheory.ThK.incV F (-v) := funext fun i => by simp [GlobalTheory.ThK.incV]
def unipotentFirstMatrix (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (v : Fin L.n → E) : Matrix (Fin d.n) (Fin d.n) E := 1 + ∑ j, Matrix.single L.i₀ (L.em j) (v j)
theorem Au_inc_k (v : Fin L.n → E) : _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k L (GlobalTheory.ThK.incV F v) = incM F (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.unipotentFirstMatrix L v) := by
  ext a b
  simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.unipotentFirstMatrix, incM, Matrix.one_apply, Matrix.sum_apply, Matrix.single_apply, GlobalTheory.ThK.incV, map_sum, apply_ite]
theorem Apc_k (hU : L.UData uM ν 𝓤) (u : Fin L.n → AE F E) : (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.Ap_k hU u).map (cA σ) = (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k L (-u))ᵀ := by
  have h1 : (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.Ap_k hU u).map (cA σ) * (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k L u)ᵀ = 1 := mul_eq_one_comm.1 (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.frame_blk_k d (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.inFrame_uM_k hU u))
  have h2 : (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k L u)ᵀ * (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k L (-u))ᵀ = 1 := by rw [← Matrix.transpose_mul, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_mul_k, neg_add_cancel, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_zero_k, Matrix.transpose_one]
  calc (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.Ap_k hU u).map (cA σ) = (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.Ap_k hU u).map (cA σ) * ((_root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k L u)ᵀ * (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k L (-u))ᵀ) := by rw [h2, Matrix.mul_one]
    _ = (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k L (-u))ᵀ := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
theorem Ap_inc_k (hU : L.UData uM ν 𝓤) (v : Fin L.n → E) : ∃ M : Matrix (Fin d.n) (Fin d.n) E,
    _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Ap_k hU (GlobalTheory.ThK.incV F v) = incM F M := by
  have : FiniteDimensional F E := Module.Finite.of_basis d.bs
  let e := AlgEquiv.ofBijective σ (AlgHom.bijective σ)
  refine ⟨((_root_.PositivityTheory.SiegelWeilFormula.Act.C1.unipotentFirstMatrix L (-v))ᵀ).map e.symm, Matrix.map_injective (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cA_injective_k d) ?_⟩
  show (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.Ap_k hU (GlobalTheory.ThK.incV F v)).map (cA σ) = (incM F (((_root_.PositivityTheory.SiegelWeilFormula.Act.C1.unipotentFirstMatrix L (-v))ᵀ).map e.symm)).map (cA σ)
  rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C1.Apc_k, kunf.incM_map_cA, Matrix.map_map, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.neg_incV_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_inc_k]
  have h : (⇑σ ∘ ⇑e.symm) = id := funext fun x => e.apply_symm_apply x
  rw [h, Matrix.map_id]
  rfl
theorem uM_rat_k (hU : L.UData uM ν 𝓤) {u : Fin L.n → AE F E} (hu : u ∈ L.ratV) : uM u ∈ rat2 σ d.Y := by
  obtain ⟨v, rfl⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C1.ratV_inc_k hu
  obtain ⟨M, hM⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Ap_inc_k hU v
  refine kunf.rat_of_inFrame (b := d.b) (M := Matrix.fromBlocks (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.unipotentFirstMatrix L v) 0 0 M) ?_
  rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C1.inFrame_uM_k hU, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_inc_k, hM]
  simp [incM, Matrix.fromBlocks_map]
theorem cj_rat_k (hU : L.UData uM ν 𝓤) (hN : IsNMap d.b nb) {u : Fin L.n → AE F E} (hu : u ∈ L.ratV)
    {β : nA σ d.Y d.b} (hβ : β ∈ nF σ d.Y d.b) : _root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_k hU hN u β ∈ nF σ d.Y d.b := by
  obtain ⟨v, rfl⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C1.ratV_inc_k hu
  obtain ⟨M, hM⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Ap_inc_k hU v
  obtain ⟨T, hT⟩ := kunf.mem_nF_iff.1 hβ
  refine kunf.mem_nF_iff.2 ⟨_root_.PositivityTheory.SiegelWeilFormula.Act.C1.unipotentFirstMatrix L (-v) * T * M, ?_⟩
  rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_val_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.neg_incV_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_inc_k, hT, hM, kunf.incM_mul', kunf.incM_mul']
theorem mul_Au_k (X : Matrix (Fin d.n) (Fin d.n) (AE F E)) (hX : ∀ a, X a L.i₀ = 0) (u : Fin L.n → AE F E) :
    X * _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k L u = X := by
  have h : ∀ j, X * Matrix.single L.i₀ (L.em j) (u j) = 0 := fun j => by
    ext a b
    simp only [Matrix.mul_apply, Matrix.single_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    split_ifs with h
    · rw [← h.1, hX, zero_mul]
    · exact mul_zero _
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k, Matrix.mul_add, Matrix.mul_one, Finset.mul_sum, h, Finset.sum_const_zero, add_zero]
theorem AuT_mul_k (X : Matrix (Fin d.n) (Fin d.n) (AE F E)) (hX : ∀ b, X L.i₀ b = 0) (u : Fin L.n → AE F E) :
    (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k L u)ᵀ * X = X := by
  have h : ∀ j, (Matrix.single L.i₀ (L.em j) (u j))ᵀ * X = 0 := fun j => by
    ext a b
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.single_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    split_ifs with h
    · rw [← h.1, hX, mul_zero]
    · exact zero_mul _
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k, Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_sum, Matrix.add_mul, Matrix.one_mul,
    Finset.sum_mul, h, Finset.sum_const_zero, add_zero]
theorem trace_cj_k (hU : L.UData uM ν 𝓤) (hN : IsNMap d.b nb) {T : nF σ d.Y d.b} {T' : nF σ L.Y L.b}
    (hT : L.IsSub T T') (u : Fin L.n → AE F E) (β : nA σ d.Y d.b) :
    Matrix.trace (T.1.1 * (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_k hU hN u β).1) = Matrix.trace (T.1.1 * β.1) := by
  have h1 : T.1.1 * _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k L (-u) = T.1.1 := _root_.PositivityTheory.SiegelWeilFormula.Act.C1.mul_Au_k _ (fun a => (hT.1 a).2) _
  have h2 : _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Ap_k hU u * T.1.1 = T.1.1 := by
    apply Matrix.map_injective (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cA_injective_k d)
    show (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.Ap_k hU u * T.1.1).map (cA σ) = T.1.1.map (cA σ)
    rw [kunf.map_cA_mul, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Apc_k]
    exact _root_.PositivityTheory.SiegelWeilFormula.Act.C1.AuT_mul_k _ (fun b => by simp [(hT.1 b).1]) _
  rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_val_k, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.trace_mul_comm, ← Matrix.mul_assoc, h2]
end PositivityTheory.SiegelWeilFormula.Act.C1
end
end
