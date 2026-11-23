import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.CtSplitOfParts
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.MatrixOfUnipotentFrame
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicFormCongruences.ExistsGlCol

noncomputable section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

set_option linter.unusedSectionVars false

namespace PositivityTheory.SiegelWeilFormula.Act.C4

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

variable {d : SD σ} (L : LD d)

def emS : Fin L.n ⊕ Fin L.n → Fin d.n ⊕ Fin d.n := Sum.map L.em L.em

def padM (M : Matrix (Fin L.n ⊕ Fin L.n) (Fin L.n ⊕ Fin L.n) (AE F E)) :
    Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E) :=
  fun r c => if h : (∃ a, emS L a = r) ∧ ∃ a, emS L a = c then M h.1.choose h.2.choose
    else (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) r c

theorem emS_inj : Function.Injective (emS L) := Sum.map_injective.2 ⟨L.inj, L.inj⟩

theorem padM_emS (M : Matrix (Fin L.n ⊕ Fin L.n) (Fin L.n ⊕ Fin L.n) (AE F E)) (a a' : Fin L.n ⊕ Fin L.n) :
    padM L M (emS L a) (emS L a') = M a a' := by
  have h : (∃ x, emS L x = emS L a) ∧ ∃ x, emS L x = emS L a' := ⟨⟨a, rfl⟩, ⟨a', rfl⟩⟩
  simp only [padM]
  rw [dif_pos h, emS_inj L h.1.choose_spec, emS_inj L h.2.choose_spec]

theorem padM_out_row (M : Matrix (Fin L.n ⊕ Fin L.n) (Fin L.n ⊕ Fin L.n) (AE F E)) {r : Fin d.n ⊕ Fin d.n}
    (hr : ¬ ∃ a, emS L a = r) (c : Fin d.n ⊕ Fin d.n) : padM L M r c = (1 : Matrix _ _ (AE F E)) r c := by
  simp only [padM]
  rw [dif_neg (fun h => hr h.1)]

theorem padM_out_col (M : Matrix (Fin L.n ⊕ Fin L.n) (Fin L.n ⊕ Fin L.n) (AE F E)) (r : Fin d.n ⊕ Fin d.n)
    {c : Fin d.n ⊕ Fin d.n} (hc : ¬ ∃ a, emS L a = c) : padM L M r c = (1 : Matrix _ _ (AE F E)) r c := by
  simp only [padM]
  rw [dif_neg (fun h => hc h.2)]

theorem mem_out {r : Fin d.n ⊕ Fin d.n} (h : ¬ ∃ a, emS L a = r) :
    r ∈ ({Sum.inl L.i₀, Sum.inr L.i₀} : Set (Fin d.n ⊕ Fin d.n)) := by
  rcases r with i | i
  · by_cases hi : i = L.i₀
    · simp [hi]
    · obtain ⟨a, ha⟩ := (L.rng i).1 hi
      exact (h ⟨Sum.inl a, by simp [emS, ha]⟩).elim
  · by_cases hi : i = L.i₀
    · simp [hi]
    · obtain ⟨a, ha⟩ := (L.rng i).1 hi
      exact (h ⟨Sum.inr a, by simp [emS, ha]⟩).elim

theorem em_ne (a : Fin L.n) : L.em a ≠ L.i₀ := (L.rng (L.em a)).2 ⟨a, rfl⟩

theorem not_inl (i : Fin d.n) (hi : i = L.i₀) : ¬ ∃ a, emS L a = Sum.inl i := by
  rintro ⟨a | a, ha⟩
  · simp only [emS, Sum.map_inl, Sum.inl.injEq] at ha
    exact em_ne L a (ha.trans hi)
  · simp [emS] at ha

theorem not_inr (i : Fin d.n) (hi : i = L.i₀) : ¬ ∃ a, emS L a = Sum.inr i := by
  rintro ⟨a | a, ha⟩
  · simp [emS] at ha
  · simp only [emS, Sum.map_inr, Sum.inr.injEq] at ha
    exact em_ne L a (ha.trans hi)

theorem inFrame_j (g : G2 σ L.Y) : inFrame d.b (L.j g) = padM L (inFrame L.b g) := by
  ext r c
  by_cases h : (∃ a, emS L a = r) ∧ ∃ a, emS L a = c
  · obtain ⟨⟨a, rfl⟩, ⟨a', rfl⟩⟩ := h
    rw [padM_emS]
    have := congrFun (congrFun (L.j_in g) a) a'
    simpa [Matrix.submatrix_apply, emS] using this
  · rcases not_and_or.1 h with h1 | h1
    · rw [padM_out_row L _ h1]
      exact (L.j_out g r (mem_out L h1) c).1
    · rw [padM_out_col L _ r h1]
      exact (L.j_out g c (mem_out L h1) r).2

theorem sub_mem_nA (β : nA σ d.Y d.b) : β.1.submatrix L.em L.em ∈ nA σ L.Y L.b := by
  obtain ⟨⟨ε, hε⟩, -⟩ := d.ok.frame
  obtain ⟨⟨ε', hε'⟩, -⟩ := L.ok.frame
  have hee : ε = ε' := Afc.eps_eq L hε hε'
  subst hee
  rw [kunf.mem_nA_iff hε']
  have h1 : β.1 ∈ kfour.nCond σ d.n ε := (kunf.mem_nA_iff hε β.1).1 β.2
  exact Afc.sub_nCond (σ := σ) L.em β.1 h1

def prj : nA σ d.Y d.b →+ nA σ L.Y L.b where
  toFun β := ⟨β.1.submatrix L.em L.em, sub_mem_nA L β⟩
  map_zero' := by
    apply Subtype.ext
    rfl
  map_add' β β' := by
    apply Subtype.ext
    rfl

theorem prj_val (β : nA σ d.Y d.b) : (prj L β).1 = β.1.submatrix L.em L.em := rfl

theorem continuous_prj : Continuous (prj L) := by
  refine Continuous.subtype_mk ?_ _
  exact continuous_subtype_val.matrix_submatrix L.em L.em

theorem pad_matrix_lower_block (M : Matrix (Fin L.n ⊕ Fin L.n) (Fin L.n ⊕ Fin L.n) (AE F E)) (hM : M.toBlocks₂₁ = 0) :
    (padM L M).toBlocks₂₁ = 0 := by
  ext i k
  simp only [Matrix.toBlocks₂₁, Matrix.of_apply, Matrix.zero_apply]
  by_cases hi : i = L.i₀
  · rw [padM_out_row L M (not_inr L i hi)]
    simp [Matrix.one_apply]
  · by_cases hk : k = L.i₀
    · rw [padM_out_col L M _ (not_inl L k hk)]
      simp [Matrix.one_apply]
    · obtain ⟨a, rfl⟩ := (L.rng i).1 hi
      obtain ⟨a', rfl⟩ := (L.rng k).1 hk
      have h1 := padM_emS L M (Sum.inr a) (Sum.inl a')
      simp only [emS, Sum.map_inr, Sum.map_inl] at h1
      rw [h1]
      have h2 := congrFun (congrFun hM a) a'
      simpa [Matrix.toBlocks₂₁] using h2

theorem upper_block_mul_of_lower_zero {k : ℕ} {P Q : Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) (AE F E)} (hQ : Q.toBlocks₂₁ = 0)
    (h : P * Q = 1) : P.toBlocks₁₁ * Q.toBlocks₁₁ = 1 := by
  have h1 := congrArg Matrix.toBlocks₁₁ h
  rw [← Matrix.fromBlocks_toBlocks P, ← Matrix.fromBlocks_toBlocks Q, Matrix.fromBlocks_multiply, hQ] at h1
  have h2 : (1 : Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) (AE F E)).toBlocks₁₁ = 1 := by
    ext i j; simp [Matrix.toBlocks₁₁, Matrix.one_apply]
  simpa [h2] using h1

theorem lower_block_embedded_parabolic {x : G2 σ L.Y} (hx : ∃ t, IsPar x t) : (inFrame d.b (L.j x)).toBlocks₂₁ = 0 := by
  obtain ⟨t, ht⟩ := hx
  obtain ⟨-, t₀, ht₀⟩ := L.ok.frame
  rw [inFrame_j]
  exact pad_matrix_lower_block L _ ((kunf.isPar_frame ht₀ x t).1 ht).1

theorem j_par {g : G2 σ L.Y} (h : g ∈ par2 σ L.Y) : L.j g ∈ par2 σ d.Y := by
  obtain ⟨t, ht⟩ := mem_parabolic_GL2_iff.1 h
  obtain ⟨-, t₁, ht₁⟩ := d.ok.frame
  set P := inFrame d.b (L.j g)
  set Q := inFrame d.b (L.j g⁻¹)
  have hP : P.toBlocks₂₁ = 0 := lower_block_embedded_parabolic L ⟨t, ht⟩
  have hQ : Q.toBlocks₂₁ = 0 := lower_block_embedded_parabolic L ⟨t⁻¹, ht.inv⟩
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

def padE (N : Matrix (Fin L.n ⊕ Fin L.n) (Fin L.n ⊕ Fin L.n) E) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E :=
  fun r c => if h : (∃ a, emS L a = r) ∧ ∃ a, emS L a = c then N h.1.choose h.2.choose
    else (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E) r c

theorem padM_incM (N : Matrix (Fin L.n ⊕ Fin L.n) (Fin L.n ⊕ Fin L.n) E) : padM L (incM F N) = incM F (padE L N) := by
  ext r c
  simp only [padM, padE, incM, Matrix.map_apply]
  split_ifs with h
  · rfl
  · rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp

theorem j_rat {g : G2 σ L.Y} (h : g ∈ rat2 σ L.Y) : L.j g ∈ rat2 σ d.Y := by
  obtain ⟨γ, hγ⟩ := Subgroup.mem_subgroupOf.1 h
  have hm : mat2 g = incM F γ.1 := by
    show g.1.1 = _
    rw [← hγ]
    rfl
  have hf : inFrame L.b g = incM F ((L.b⁻¹).1 * γ.1 * L.b.1) := by
    rw [kunf.incM_mul', kunf.incM_mul', ← hm]
    rfl
  refine kunf.rat_of_inFrame (b := d.b) (M := padE L ((L.b⁻¹).1 * γ.1 * L.b.1)) ?_
  rw [inFrame_j, hf, padM_incM]

end PositivityTheory.SiegelWeilFormula.Act.C4

end
