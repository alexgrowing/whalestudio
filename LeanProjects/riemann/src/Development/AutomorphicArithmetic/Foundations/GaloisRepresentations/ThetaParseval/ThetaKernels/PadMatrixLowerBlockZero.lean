import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.SplitPrimeIdeals
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LiftedSchrodingerDatum
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.EpsEqK

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.Act.C4
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d)
def emS_k : Fin L.n ⊕ Fin L.n → Fin d.n ⊕ Fin d.n := Sum.map L.em L.em
def padM_k (M : Matrix (Fin L.n ⊕ Fin L.n) (Fin L.n ⊕ Fin L.n) (AE F E)) :
    Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E) :=
  fun r c => if h : (∃ a, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a = r) ∧ ∃ a, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a = c then M h.1.choose h.2.choose
    else (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) r c
theorem emS_inj_k : Function.Injective (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L) := Sum.map_injective.2 ⟨L.inj, L.inj⟩
theorem padM_emS_k (M : Matrix (Fin L.n ⊕ Fin L.n) (Fin L.n ⊕ Fin L.n) (AE F E)) (a a' : Fin L.n ⊕ Fin L.n) :
    _root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_k L M (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a') = M a a' := by
  have h : (∃ x, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L x = _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a) ∧ ∃ x, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L x = _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a' := ⟨⟨a, rfl⟩, ⟨a', rfl⟩⟩
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_k]
  rw [dif_pos h, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_inj_k L h.1.choose_spec, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_inj_k L h.2.choose_spec]
theorem padM_out_row_k (M : Matrix (Fin L.n ⊕ Fin L.n) (Fin L.n ⊕ Fin L.n) (AE F E)) {r : Fin d.n ⊕ Fin d.n}
    (hr : ¬ ∃ a, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a = r) (c : Fin d.n ⊕ Fin d.n) : _root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_k L M r c = (1 : Matrix _ _ (AE F E)) r c := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_k]
  rw [dif_neg (fun h => hr h.1)]
theorem padM_out_col_k (M : Matrix (Fin L.n ⊕ Fin L.n) (Fin L.n ⊕ Fin L.n) (AE F E)) (r : Fin d.n ⊕ Fin d.n)
    {c : Fin d.n ⊕ Fin d.n} (hc : ¬ ∃ a, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a = c) : _root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_k L M r c = (1 : Matrix _ _ (AE F E)) r c := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_k]
  rw [dif_neg (fun h => hc h.2)]
theorem mem_out_k {r : Fin d.n ⊕ Fin d.n} (h : ¬ ∃ a, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a = r) :
    r ∈ ({Sum.inl L.i₀, Sum.inr L.i₀} : Set (Fin d.n ⊕ Fin d.n)) := by
  rcases r with i | i
  · by_cases hi : i = L.i₀
    · simp [hi]
    · obtain ⟨a, ha⟩ := (L.rng i).1 hi
      exact (h ⟨Sum.inl a, by simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k, ha]⟩).elim
  · by_cases hi : i = L.i₀
    · simp [hi]
    · obtain ⟨a, ha⟩ := (L.rng i).1 hi
      exact (h ⟨Sum.inr a, by simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k, ha]⟩).elim
theorem em_ne_k (a : Fin L.n) : L.em a ≠ L.i₀ := (L.rng (L.em a)).2 ⟨a, rfl⟩
theorem not_inl_k (i : Fin d.n) (hi : i = L.i₀) : ¬ ∃ a, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a = Sum.inl i := by
  rintro ⟨a | a, ha⟩
  · simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k, Sum.map_inl, Sum.inl.injEq] at ha
    exact _root_.PositivityTheory.SiegelWeilFormula.Act.C4.em_ne_k L a (ha.trans hi)
  · simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k] at ha
theorem not_inr_k (i : Fin d.n) (hi : i = L.i₀) : ¬ ∃ a, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a = Sum.inr i := by
  rintro ⟨a | a, ha⟩
  · simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k] at ha
  · simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k, Sum.map_inr, Sum.inr.injEq] at ha
    exact _root_.PositivityTheory.SiegelWeilFormula.Act.C4.em_ne_k L a (ha.trans hi)
theorem inFrame_j_k (g : G2 σ L.Y) : inFrame d.b (L.j g) = _root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_k L (inFrame L.b g) := by
  ext r c
  by_cases h : (∃ a, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a = r) ∧ ∃ a, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a = c
  · obtain ⟨⟨a, rfl⟩, ⟨a', rfl⟩⟩ := h
    rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_emS_k]
    have := congrFun (congrFun (L.j_in g) a) a'
    simpa [Matrix.submatrix_apply, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k] using this
  · rcases not_and_or.1 h with h1 | h1
    · rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_out_row_k L _ h1]
      exact (L.j_out g r (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.mem_out_k L h1) c).1
    · rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_out_col_k L _ r h1]
      exact (L.j_out g c (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.mem_out_k L h1) r).2
theorem sub_mem_nA_k (β : nA σ d.Y d.b) : β.1.submatrix L.em L.em ∈ nA σ L.Y L.b := by
  obtain ⟨⟨ε, hε⟩, -⟩ := d.ok.frame
  obtain ⟨⟨ε', hε'⟩, -⟩ := L.ok.frame
  have hee : ε = ε' := _root_.PositivityTheory.SiegelWeilFormula.Afc.eps_eq_k L hε hε'
  subst hee
  rw [kunf.mem_nA_iff hε']
  have h1 : β.1 ∈ kfour.nCond σ d.n ε := (kunf.mem_nA_iff hε β.1).1 β.2
  exact Afc.sub_nCond (σ := σ) L.em β.1 h1
def prj_k : nA σ d.Y d.b →+ nA σ L.Y L.b where
  toFun β := ⟨β.1.submatrix L.em L.em, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.sub_mem_nA_k L β⟩
  map_zero' := by
    apply Subtype.ext
    rfl
  map_add' β β' := by
    apply Subtype.ext
    rfl
theorem prj_val_k (β : nA σ d.Y d.b) : (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β).1 = β.1.submatrix L.em L.em := rfl
theorem continuous_prj_k : Continuous (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L) := by
  refine Continuous.subtype_mk ?_ _
  exact continuous_subtype_val.matrix_submatrix L.em L.em
theorem pad_matrix_lower_block_zero (M : Matrix (Fin L.n ⊕ Fin L.n) (Fin L.n ⊕ Fin L.n) (AE F E)) (hM : M.toBlocks₂₁ = 0) :
    (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_k L M).toBlocks₂₁ = 0 := by
  ext i k
  simp only [Matrix.toBlocks₂₁, Matrix.of_apply, Matrix.zero_apply]
  by_cases hi : i = L.i₀
  · rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_out_row_k L M (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.not_inr_k L i hi)]
    simp [Matrix.one_apply]
  · by_cases hk : k = L.i₀
    · rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_out_col_k L M _ (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.not_inl_k L k hk)]
      simp [Matrix.one_apply]
    · obtain ⟨a, rfl⟩ := (L.rng i).1 hi
      obtain ⟨a', rfl⟩ := (L.rng k).1 hk
      have h1 := _root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_emS_k L M (Sum.inr a) (Sum.inl a')
      simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k, Sum.map_inr, Sum.map_inl] at h1
      rw [h1]
      have h2 := congrFun (congrFun hM a) a'
      simpa [Matrix.toBlocks₂₁] using h2
theorem embedding_lower_block_zero {x : G2 σ L.Y} (hx : ∃ t, IsPar x t) : (inFrame d.b (L.j x)).toBlocks₂₁ = 0 := by
  obtain ⟨t, ht⟩ := hx
  obtain ⟨-, t₀, ht₀⟩ := L.ok.frame
  rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.inFrame_j_k]
  exact _root_.PositivityTheory.SiegelWeilFormula.Act.C4.pad_matrix_lower_block_zero L _ ((kunf.isPar_frame ht₀ x t).1 ht).1
theorem j_par_k {g : G2 σ L.Y} (h : g ∈ par2 σ L.Y) : L.j g ∈ par2 σ d.Y := by
  obtain ⟨t, ht⟩ := mem_parabolic_GL2_iff.1 h
  obtain ⟨-, t₁, ht₁⟩ := d.ok.frame
  set P := inFrame d.b (L.j g)
  set Q := inFrame d.b (L.j g⁻¹)
  have hP : P.toBlocks₂₁ = 0 := _root_.PositivityTheory.SiegelWeilFormula.Act.C4.embedding_lower_block_zero L ⟨t, ht⟩
  have hQ : Q.toBlocks₂₁ = 0 := _root_.PositivityTheory.SiegelWeilFormula.Act.C4.embedding_lower_block_zero L ⟨t⁻¹, ht.inv⟩
  have hPQ : P * Q = 1 := by
    rw [← GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, ← map_mul, mul_inv_cancel, map_one, GlobalTheory.EisBL.DoubledParabolic.inFrame_one]
  have hQP : Q * P = 1 := by
    rw [← GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, ← map_mul, inv_mul_cancel, map_one, GlobalTheory.EisBL.DoubledParabolic.inFrame_one]
  have e1 := upper_block_mul_of_lower_zero hQ hPQ
  have e2 := upper_block_mul_of_lower_zero hP hQP
  set T0 := incM F t₁.1
  set Ti := incM F (t₁⁻¹).1
  have hT : T0 * Ti = 1 := by
    show incM F t₁.1 * incM F (t₁⁻¹).1 = 1
    rw [← kunf.incM_mul', Units.mul_inv]; ext i j; simp [incM, Matrix.one_apply]
  have hT' : Ti * T0 = 1 := by
    show incM F (t₁⁻¹).1 * incM F t₁.1 = 1
    rw [← kunf.incM_mul', Units.inv_mul]; ext i j; simp [incM, Matrix.one_apply]
  let t' : GL (Fin d.n) (AE F E) := ⟨T0 * P.toBlocks₁₁ * Ti, T0 * Q.toBlocks₁₁ * Ti, by
      calc T0 * P.toBlocks₁₁ * Ti * (T0 * Q.toBlocks₁₁ * Ti) = T0 * (P.toBlocks₁₁ * (Ti * T0) * Q.toBlocks₁₁) * Ti := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hT', Matrix.mul_one, e1, Matrix.mul_one, hT], by
      calc T0 * Q.toBlocks₁₁ * Ti * (T0 * P.toBlocks₁₁ * Ti) = T0 * (Q.toBlocks₁₁ * (Ti * T0) * P.toBlocks₁₁) * Ti := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hT', Matrix.mul_one, e2, Matrix.mul_one, hT]⟩
  exact mem_parabolic_GL2_iff.2 ⟨t', (kunf.isPar_frame ht₁ (L.j g) t').2 ⟨hP, rfl⟩⟩
def padE_k (N : Matrix (Fin L.n ⊕ Fin L.n) (Fin L.n ⊕ Fin L.n) E) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E :=
  fun r c => if h : (∃ a, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a = r) ∧ ∃ a, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a = c then N h.1.choose h.2.choose
    else (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E) r c
theorem padM_incM_k (N : Matrix (Fin L.n ⊕ Fin L.n) (Fin L.n ⊕ Fin L.n) E) : _root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_k L (incM F N) = incM F (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padE_k L N) := by
  ext r c
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.padE_k, incM, Matrix.map_apply]
  split_ifs with h
  · rfl
  · rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
theorem j_rat_k {g : G2 σ L.Y} (h : g ∈ rat2 σ L.Y) : L.j g ∈ rat2 σ d.Y := by
  obtain ⟨γ, hγ⟩ := Subgroup.mem_subgroupOf.1 h
  have hm : mat2 g = incM F γ.1 := by
    show g.1.1 = _
    rw [← hγ]
    rfl
  have hf : inFrame L.b g = incM F ((L.b⁻¹).1 * γ.1 * L.b.1) := by
    rw [kunf.incM_mul', kunf.incM_mul', ← hm]
    rfl
  refine kunf.rat_of_inFrame (b := d.b) (M := _root_.PositivityTheory.SiegelWeilFormula.Act.C4.padE_k L ((L.b⁻¹).1 * γ.1 * L.b.1)) ?_
  rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.inFrame_j_k, hf, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_incM_k]
end PositivityTheory.SiegelWeilFormula.Act.C4
end
end
