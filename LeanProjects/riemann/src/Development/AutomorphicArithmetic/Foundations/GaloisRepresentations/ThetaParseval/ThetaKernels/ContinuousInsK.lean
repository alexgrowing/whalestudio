import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.InclRSmul
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LiftedSchrodingerDatum
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.UnipotentNilpotentMulEqZero
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.PadMatrixLowerBlockZero
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ExistsNeSigmaK
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKunfCells
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.BMatK

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Act.C5.Meas
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d)
def pre_k (r : Fin d.n) (h : r ≠ L.i₀) : Fin L.n := ((L.rng r).1 h).choose
theorem em_pre_k (r : Fin d.n) (h : r ≠ L.i₀) : L.em (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.Meas.pre_k L r h) = r := ((L.rng r).1 h).choose_spec
theorem pre_em_k (k : Fin L.n) (h : L.em k ≠ L.i₀) : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Meas.pre_k L (L.em k) h = k := L.inj (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.Meas.em_pre_k L _ h)
def padZ_k (β : Matrix (Fin L.n) (Fin L.n) (AE F E)) : Matrix (Fin d.n) (Fin d.n) (AE F E) := fun r c =>
  if hr : r = L.i₀ then 0 else if hc : c = L.i₀ then 0 else β (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.Meas.pre_k L r hr) (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.Meas.pre_k L c hc)
theorem one_em_k (k l : Fin L.n) :
    (1 : Matrix (Fin d.n) (Fin d.n) (AE F E)) (L.em k) (L.em l) = (1 : Matrix (Fin L.n) (Fin L.n) (AE F E)) k l := by
  simp [Matrix.one_apply, L.inj.eq_iff]
theorem inFrame_j_nb_k {x : G2 σ L.Y} {β : Matrix (Fin L.n) (Fin L.n) (AE F E)}
    (hx : inFrame L.b x = Matrix.fromBlocks 1 β 0 1) :
    inFrame d.b (L.j x) = Matrix.fromBlocks 1 (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.Meas.padZ_k L β) 0 1 := by
  have hin := L.j_in x
  rw [hx] at hin
  have emb : ∀ u v : Fin L.n ⊕ Fin L.n, inFrame d.b (L.j x) (Sum.map L.em L.em u) (Sum.map L.em L.em v) =
      Matrix.fromBlocks 1 β 0 1 u v := fun u v => by rw [← hin]; rfl
  have kl : ∀ v, inFrame d.b (L.j x) (Sum.inl L.i₀) v = (1 : Matrix _ _ (AE F E)) (Sum.inl L.i₀) v ∧
      inFrame d.b (L.j x) v (Sum.inl L.i₀) = (1 : Matrix _ _ (AE F E)) v (Sum.inl L.i₀) :=
    fun v => L.j_out x _ (by simp) v
  have kr : ∀ v, inFrame d.b (L.j x) (Sum.inr L.i₀) v = (1 : Matrix _ _ (AE F E)) (Sum.inr L.i₀) v ∧
      inFrame d.b (L.j x) v (Sum.inr L.i₀) = (1 : Matrix _ _ (AE F E)) v (Sum.inr L.i₀) :=
    fun v => L.j_out x _ (by simp) v
  ext (r | r) (c | c)
  · rcases eq_or_ne r L.i₀ with rfl | hr
    · rw [(kl _).1]; simp [Matrix.one_apply]
    rcases eq_or_ne c L.i₀ with rfl | hc
    · rw [(kl _).2]; simp [Matrix.one_apply, hr]
    obtain ⟨k, rfl⟩ := (L.rng r).1 hr
    obtain ⟨l, rfl⟩ := (L.rng c).1 hc
    have := emb (Sum.inl k) (Sum.inl l)
    simp only [Sum.map_inl, Matrix.fromBlocks_apply₁₁] at this ⊢
    rw [this, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Meas.one_em_k]
  · rcases eq_or_ne r L.i₀ with rfl | hr
    · rw [(kl _).1]; simp [Matrix.one_apply, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Meas.padZ_k]
    rcases eq_or_ne c L.i₀ with rfl | hc
    · rw [(kr _).2]; simp [Matrix.one_apply, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Meas.padZ_k]
    obtain ⟨k, rfl⟩ := (L.rng r).1 hr
    obtain ⟨l, rfl⟩ := (L.rng c).1 hc
    have := emb (Sum.inl k) (Sum.inr l)
    simp only [Sum.map_inl, Sum.map_inr, Matrix.fromBlocks_apply₁₂] at this ⊢
    rw [this]
    simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.Meas.padZ_k, _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.em_ne_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Meas.pre_em_k]
  · rcases eq_or_ne r L.i₀ with rfl | hr
    · rw [(kr _).1]; simp [Matrix.one_apply]
    rcases eq_or_ne c L.i₀ with rfl | hc
    · rw [(kl _).2]; simp [Matrix.one_apply]
    obtain ⟨k, rfl⟩ := (L.rng r).1 hr
    obtain ⟨l, rfl⟩ := (L.rng c).1 hc
    have := emb (Sum.inr k) (Sum.inl l)
    simp only [Sum.map_inl, Sum.map_inr, Matrix.fromBlocks_apply₂₁] at this ⊢
    rw [this]
    simp
  · rcases eq_or_ne r L.i₀ with rfl | hr
    · rw [(kr _).1]; simp [Matrix.one_apply]
    rcases eq_or_ne c L.i₀ with rfl | hc
    · rw [(kr _).2]; simp [Matrix.one_apply, hr]
    obtain ⟨k, rfl⟩ := (L.rng r).1 hr
    obtain ⟨l, rfl⟩ := (L.rng c).1 hc
    have := emb (Sum.inr k) (Sum.inr l)
    simp only [Sum.map_inr, Matrix.fromBlocks_apply₂₂] at this ⊢
    rw [this, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Meas.one_em_k]
theorem padCond_k {ε : ℤˣ} (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0)
    {β : Matrix (Fin L.n) (Fin L.n) (AE F E)} (hβ : β ∈ nA σ L.Y L.b) (k l : Fin L.n) :
    β l k = -(((ε : ℤ) : AE F E) * cA σ (β k l)) := by
  revert k l
  induction hβ using AddSubgroup.closure_induction with
  | mem β h =>
    obtain ⟨x, hx⟩ := h
    have hmem : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Meas.padZ_k L β ∈ nA σ d.Y d.b := AddSubgroup.subset_closure ⟨L.j x, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Meas.inFrame_j_nb_k L hx⟩
    have hc := (kunf.mem_nA_iff hε _).1 hmem
    intro k l
    have := congrFun (congrFun hc (L.em k)) (L.em l)
    simpa [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.Meas.padZ_k, _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.em_ne_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Meas.pre_em_k, Matrix.transpose_apply, smul_eq_mul] using this
  | zero => intro k l; simp
  | add β β' _ _ h h' => intro k l; rw [Matrix.add_apply, Matrix.add_apply, h, h', map_add, mul_add, neg_add]
  | neg β _ h => intro k l; rw [Matrix.neg_apply, Matrix.neg_apply, h, map_neg, mul_neg]
theorem sig_delta_k (hB : _root_.UpperTheory.TP.W.GoodK σ d.B) {ε : ℤˣ}
    (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) {δ : E}
    (hcf : ∃ (x : d.G) (A' : Matrix (Fin d.n) (Fin d.n) (AE F E)), inFrame d.b x = Matrix.fromBlocks 1 (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.aB_k L δ 1) 0 A') :
    σ δ = ((-(ε : ℤ) : ℤ) : E) * δ := by
  obtain ⟨x, A', hx⟩ := hcf
  have inv : ∀ z, cA σ (cA σ z) = z := GlobalTheory.EisBL.DoubledUnipotentRadical.cA_cA σ (_root_.PositivityTheory.SiegelWeilFormula.kunf.sigma_invol_k d.B hB)
  have h := kunf.frame_eq hε x
  rw [hx] at h
  have h1 : (1 : Matrix (Fin d.n) (Fin d.n) (AE F E)).map (cA σ) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have h0 : (0 : Matrix (Fin d.n) (Fin d.n) (AE F E)).map (cA σ) = 0 := Matrix.map_zero _ (map_zero _)
  simp only [kunf.jw, Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply,
    Matrix.transpose_one, Matrix.transpose_zero, h1, h0, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one,
    Matrix.one_mul, add_zero, zero_add] at h
  obtain ⟨-, h2, -, h4⟩ := Matrix.fromBlocks_inj.1 h
  have hA : A' = 1 := by
    ext i j
    have := congrFun (congrFun h2 i) j
    rw [Matrix.map_apply] at this
    rw [← inv (A' i j), this]
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  rw [hA, h1, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one] at h4
  have he := congrFun (congrFun h4 L.i₀) L.i₀
  simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.aB_k, GlobalTheory.EisBL.DoubledUnipotentRadical.cA_inclR] at he
  have e2 : ((ε : ℤ) : E) * ((ε : ℤ) : E) = 1 := eps_sq ε
  have h5 : ((ε : ℤ) : E) * σ δ + δ = 0 := by
    apply kfour.inclR_injective (F := F)
    rw [map_add, map_mul, map_intCast, he, map_zero]
  push_cast
  linear_combination ((ε : ℤ) : E) * h5 - σ δ * e2
def ins_k (e : AE F E) (δ : E) (x : ((Fin L.n → AE F E) × AF F) × Matrix (Fin L.n) (Fin L.n) (AE F E)) :
    Matrix (Fin d.n) (Fin d.n) (AE F E) := fun r c =>
  if hr : r = L.i₀ then (if hc : c = L.i₀ then x.1.2 • inclR (F := F) (AF F) δ else x.1.1 (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.Meas.pre_k L c hc))
  else (if hc : c = L.i₀ then -(e * cA σ (x.1.1 (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.Meas.pre_k L r hr))) else x.2 (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.Meas.pre_k L r hr) (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.Meas.pre_k L c hc))
theorem continuous_ins_k (e : AE F E) (δ : E) : Continuous (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.Meas.ins_k L e δ) := by
  refine continuous_pi fun r => continuous_pi fun c => ?_
  unfold _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Meas.ins_k
  have hcA := continuous_cA' (σ := σ)
  by_cases hr : r = L.i₀ <;> by_cases hc : c = L.i₀ <;> simp only [hr, hc, dite_true, dite_false] <;> fun_prop
theorem ins_mem_k (hB : _root_.UpperTheory.TP.W.GoodK σ d.B) {ε : ℤˣ}
    (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) {δ : E}
    (hδ : σ δ = ((-(ε : ℤ) : ℤ) : E) * δ) (b : Fin L.n → AE F E) (a : AF F) {β : Matrix (Fin L.n) (Fin L.n) (AE F E)}
    (hβ : β ∈ nA σ L.Y L.b) : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Meas.ins_k L (((ε : ℤ) : AE F E)) δ ((b, a), β) ∈ nA σ d.Y d.b := by
  rw [kunf.mem_nA_iff hε]
  have e2 : ((ε : ℤ) : AE F E) * ((ε : ℤ) : AE F E) = 1 := eps_sq ε
  have cε : cA σ (((ε : ℤ) : AE F E)) = ((ε : ℤ) : AE F E) := map_intCast _ _
  have inv : ∀ z, cA σ (cA σ z) = z := GlobalTheory.EisBL.DoubledUnipotentRadical.cA_cA σ (_root_.PositivityTheory.SiegelWeilFormula.kunf.sigma_invol_k d.B hB)
  ext r c
  simp only [Matrix.transpose_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
  rcases eq_or_ne r L.i₀ with rfl | hr <;> rcases eq_or_ne c L.i₀ with rfl | hc
  · simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.Meas.ins_k, dite_true]
    rw [map_smul, GlobalTheory.EisBL.DoubledUnipotentRadical.cA_inclR, hδ, map_mul, map_intCast, Algebra.smul_def, Algebra.smul_def]
    push_cast
    linear_combination (-(algebraMap (AF F) (AE F E) a * inclR (F := F) (AF F) δ)) * e2
  · simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.Meas.ins_k, hc]
  · simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.Meas.ins_k, hr, dite_true, dite_false]
    rw [map_neg, map_mul, cε, inv]
    linear_combination (-(b (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.Meas.pre_k L r hr))) * e2
  · obtain ⟨k, rfl⟩ := (L.rng r).1 hr
    obtain ⟨l, rfl⟩ := (L.rng c).1 hc
    simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.Meas.ins_k, hr, hc, dite_false, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Meas.pre_em_k]
    exact _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Meas.padCond_k L hε hβ k l
theorem ins_left_k (hB : _root_.UpperTheory.TP.W.GoodK σ d.B) {ε : ℤˣ}
    (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) {δ : E} (hδ0 : δ ≠ 0)
    (hδ : σ δ = ((-(ε : ℤ) : ℤ) : E) * δ) (β : nA σ d.Y d.b) :
    _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Meas.ins_k L (((ε : ℤ) : AE F E)) δ (((fun j => β.1 L.i₀ (L.em j)), linearFormAdelic (F := F) δ (β.1 L.i₀ L.i₀)), (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β).1) =
      β.1 := by
  have hc := (kunf.mem_nA_iff hε β.1).1 β.2
  have e2 : ((ε : ℤ) : AE F E) * ((ε : ℤ) : AE F E) = 1 := eps_sq ε
  have hk : (-(ε : ℤ)) * (-(ε : ℤ)) = 1 := by rw [neg_mul_neg]; exact eps_sq ε
  ext r c
  rcases eq_or_ne r L.i₀ with rfl | hr <;> rcases eq_or_ne c L.i₀ with rfl | hc'
  · simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.Meas.ins_k, dite_true]
    have h0 := congrFun (congrFun hc L.i₀) L.i₀
    simp only [Matrix.transpose_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul] at h0
    refine (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.Meas.eig_AE_k d.ok.good hk hδ0 hδ ?_).symm
    push_cast
    linear_combination ((ε : ℤ) : AE F E) * h0 - cA σ (β.1 L.i₀ L.i₀) * e2
  · obtain ⟨l, rfl⟩ := (L.rng c).1 hc'
    simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.Meas.ins_k, _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.em_ne_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Meas.pre_em_k]
  · obtain ⟨k, rfl⟩ := (L.rng r).1 hr
    have h0 := congrFun (congrFun hc L.i₀) (L.em k)
    simp only [Matrix.transpose_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul] at h0
    simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.Meas.ins_k, hr, dite_true, dite_false, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Meas.pre_em_k]
    exact h0.symm
  · obtain ⟨k, rfl⟩ := (L.rng r).1 hr
    obtain ⟨l, rfl⟩ := (L.rng c).1 hc'
    simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.Meas.ins_k, hr, hc', dite_false, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Meas.pre_em_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_val_k, Matrix.submatrix_apply]
theorem ins_pb_k (e : AE F E) (δ : E) (x : ((Fin L.n → AE F E) × AF F) × Matrix (Fin L.n) (Fin L.n) (AE F E)) :
    (fun j => _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Meas.ins_k L e δ x L.i₀ (L.em j)) = x.1.1 := by
  funext j
  simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.Meas.ins_k, _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.em_ne_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Meas.pre_em_k]
theorem ins_pa_k {δ : E} (hδ0 : δ ≠ 0) (e : AE F E) (x : ((Fin L.n → AE F E) × AF F) × Matrix (Fin L.n) (Fin L.n) (AE F E)) :
    linearFormAdelic (F := F) δ (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.Meas.ins_k L e δ x L.i₀ L.i₀) = x.1.2 := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.Meas.ins_k, dite_true]
  exact ellA_smul_inclR hδ0 _
theorem ins_sub_k (e : AE F E) (δ : E) (x : ((Fin L.n → AE F E) × AF F) × Matrix (Fin L.n) (Fin L.n) (AE F E)) :
    (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.Meas.ins_k L e δ x).submatrix L.em L.em = x.2 := by
  ext k l
  simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.Meas.ins_k, _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.em_ne_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Meas.pre_em_k]
theorem pEquiv0_k {δ : E} (hδ0 : δ ≠ 0)
    (hcf : ∃ (x : d.G) (A' : Matrix (Fin d.n) (Fin d.n) (AE F E)), inFrame d.b x = Matrix.fromBlocks 1 (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.aB_k L δ 1) 0 A') :
    ∃ P : (nA σ d.Y d.b) ≃ₜ+ (((Fin L.n → AE F E) × AF F) × nA σ L.Y L.b),
      (∀ β, P β = (((fun j => β.1 L.i₀ (L.em j)), linearFormAdelic (F := F) δ (β.1 L.i₀ L.i₀)), _root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β)) ∧
      ∀ β, β ∈ nF σ d.Y d.b ↔ (((fun j => β.1 L.i₀ (L.em j)) ∈ L.ratV ∧
        linearFormAdelic (F := F) δ (β.1 L.i₀ L.i₀) ∈ (algebraMap F (AF F)).range.toAddSubgroup) ∧ _root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β ∈ nF σ L.Y L.b) := by
  have hB := d.ok.good
  obtain ⟨ε, hε⟩ := d.ok.frame.1
  have hδ := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Meas.sig_delta_k L hB hε hcf
  let fwd : nA σ d.Y d.b → ((Fin L.n → AE F E) × AF F) × nA σ L.Y L.b :=
    fun β => (((fun j => β.1 L.i₀ (L.em j)), linearFormAdelic (F := F) δ (β.1 L.i₀ L.i₀)), _root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β)
  let bwd : ((Fin L.n → AE F E) × AF F) × nA σ L.Y L.b → nA σ d.Y d.b :=
    fun x => ⟨_root_.PositivityTheory.SiegelWeilFormula.Act.C5.Meas.ins_k L (((ε : ℤ) : AE F E)) δ (x.1, x.2.1), _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Meas.ins_mem_k L hB hε hδ x.1.1 x.1.2 x.2.2⟩
  have hleft : ∀ β, bwd (fwd β) = β := fun β => Subtype.ext (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.Meas.ins_left_k L hB hε hδ0 hδ β)
  have hright : ∀ x, fwd (bwd x) = x := by
    rintro ⟨⟨b, a⟩, β''⟩
    refine Prod.ext (Prod.ext (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.Meas.ins_pb_k L _ δ _) (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.Meas.ins_pa_k L hδ0 _ _)) (Subtype.ext ?_)
    rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_val_k]
    exact _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Meas.ins_sub_k L _ δ _
  let P : (nA σ d.Y d.b) ≃ₜ+ (((Fin L.n → AE F E) × AF F) × nA σ L.Y L.b) :=
    { toFun := fwd
      invFun := bwd
      left_inv := hleft
      right_inv := hright
      map_add' := fun β β' => by
        refine Prod.ext (Prod.ext ?_ ?_) (map_add (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L) β β')
        · funext j
          rfl
        · show linearFormAdelic (F := F) δ ((β + β').1 L.i₀ L.i₀) = linearFormAdelic (F := F) δ (β.1 L.i₀ L.i₀) + linearFormAdelic (F := F) δ (β'.1 L.i₀ L.i₀)
          rw [← map_add]
          rfl
      continuous_toFun := by
        refine Continuous.prodMk (Continuous.prodMk ?_ ?_) ?_
        · exact continuous_pi fun j => (continuous_apply _).comp ((continuous_apply _).comp continuous_subtype_val)
        · exact (continuous_ellA δ).comp ((continuous_apply _).comp ((continuous_apply _).comp continuous_subtype_val))
        · exact continuous_induced_rng.2 (continuous_subtype_val.matrix_submatrix _ _)
      continuous_invFun := by
        refine Continuous.subtype_mk ((_root_.PositivityTheory.SiegelWeilFormula.Act.C5.Meas.continuous_ins_k L _ δ).comp ?_) _
        exact continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd) }
  refine ⟨P, fun β => rfl, fun β => ?_⟩
  constructor
  · intro hβ
    obtain ⟨T, hT⟩ := kunf.mem_nF_iff.1 hβ
    refine ⟨⟨ComplexParameterFamilyContinuity.mem_ratVec.2 ⟨fun j => T L.i₀ (L.em j), ?_⟩, ?_⟩, kunf.mem_nF_iff.2 ⟨T.submatrix L.em L.em, ?_⟩⟩
    · funext j
      rw [hT]
      rfl
    · obtain ⟨f, hf⟩ := ellA_inclR (F := F) δ (T L.i₀ L.i₀)
      refine ⟨f, ?_⟩
      rw [hT]
      exact hf.symm
    · rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_val_k, hT]
      rfl
  · rintro ⟨⟨h1, h2⟩, h3⟩
    obtain ⟨v, hv⟩ := ComplexParameterFamilyContinuity.mem_ratVec.1 h1
    obtain ⟨f, hf⟩ := h2
    obtain ⟨T'', hT''⟩ := kunf.mem_nF_iff.1 h3
    have hv' : ∀ j, β.1 L.i₀ (L.em j) = inclR (F := F) (AF F) (v j) := fun j => (congrFun hv j).symm
    have hT2 : ∀ k l, (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β).1 k l = inclR (F := F) (AF F) (T'' k l) := fun k l => by rw [hT'']; rfl
    refine kunf.mem_nF_iff.2 ⟨Matrix.of fun r c => if hr : r = L.i₀ then (if hc : c = L.i₀ then f • δ else v (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.Meas.pre_k L c hc))
      else (if hc : c = L.i₀ then -(((ε : ℤ) : E) * σ (v (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.Meas.pre_k L r hr))) else T'' (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.Meas.pre_k L r hr) (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.Meas.pre_k L c hc)), ?_⟩
    conv_lhs => rw [← _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Meas.ins_left_k L hB hε hδ0 hδ β]
    ext r c
    by_cases hr : r = L.i₀ <;> by_cases hc : c = L.i₀ <;>
      simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.Meas.ins_k, incM, Matrix.map_apply, Matrix.of_apply, hr, hc, dite_true, dite_false]
    · rw [inclR_smul', ← hf]
    · exact hv' _
    · rw [hv', map_neg, map_mul, map_intCast, GlobalTheory.EisBL.DoubledUnipotentRadical.cA_inclR]
    · exact hT2 _ _
end PositivityTheory.SiegelWeilFormula.Act.C5.Meas
end
end
