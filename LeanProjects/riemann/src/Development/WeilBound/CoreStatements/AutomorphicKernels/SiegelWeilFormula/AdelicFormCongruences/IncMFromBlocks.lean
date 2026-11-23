import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LowerRankDatum
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FourierCompactness.SigmaSigmaOfGood
import Development.WeilBound.ThetaLifts.LatticeBasics.IsCompactIntV

set_option linter.unusedSectionVars false

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw SiegelEisensteinSeries.Grp PositivityTheory.SiegelWeilFormula.kfour

namespace PositivityTheory.SiegelWeilFormula.Afc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {Y : Spc F E n}

abbrev QA (n : ℕ) (ε : ℤˣ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E) :=
  Matrix.fromBlocks 0 1 ((((ε : ℤ) : AE F E)) • 1) 0

theorem frame_form {b : GL (Fin n ⊕ Fin n) E} {ε : ℤˣ} (hb : FrameEq σ Y b ε) (x : G2 σ Y) :
    (inFrame b x)ᵀ * QA (F := F) (E := E) n ε * (inFrame b x).map (cA σ) = QA n ε := by
  have hF := frameEq_adelic (F := F) hb
  have hU : (mat2 x)ᵀ * dbl (incM F Y.J) * (mat2 x).map (cA σ) = dbl (incM F Y.J) := x.2
  have hM : incM F b.1 * inFrame b x = mat2 x * incM F b.1 := by
    rw [matrix_eq_frame_conjugate b x]
    simp only [Matrix.mul_assoc]
    rw [SiegelEisensteinSeries.Grp.incM_inv_mul, Matrix.mul_one]
  have key : (incM F b.1 * inFrame b x)ᵀ * dbl (incM F Y.J) * (incM F b.1 * inFrame b x).map (cA σ) = QA n ε := by
    rw [hM, Matrix.transpose_mul, map_cA_mul]
    calc (incM F b.1)ᵀ * (mat2 x)ᵀ * dbl (incM F Y.J) * ((mat2 x).map (cA σ) * (incM F b.1).map (cA σ))
        = (incM F b.1)ᵀ * ((mat2 x)ᵀ * dbl (incM F Y.J) * (mat2 x).map (cA σ)) * (incM F b.1).map (cA σ) := by
          simp only [Matrix.mul_assoc]
      _ = QA n ε := by rw [hU, hF]
  rw [Matrix.transpose_mul, map_cA_mul] at key
  have hQ : QA (F := F) (E := E) n ε = (incM F b.1)ᵀ * dbl (incM F Y.J) * (incM F b.1).map (cA σ) := hF.symm
  conv_lhs => rw [hQ]
  simpa only [Matrix.mul_assoc] using key

theorem blk_form (ε : ℤˣ) (A D : Matrix (Fin n) (Fin n) (AE F E)) :
    (Matrix.fromBlocks A 0 0 D)ᵀ * QA (F := F) (E := E) n ε * (Matrix.fromBlocks A 0 0 D).map (cA σ) =
      Matrix.fromBlocks 0 (Aᵀ * D.map (cA σ)) ((((ε : ℤ) : AE F E)) • (Dᵀ * A.map (cA σ))) 0 := by
  rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, QA, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp [Matrix.map_zero _ (map_zero _)]

theorem blk_rel {b : GL (Fin n ⊕ Fin n) E} (hb : IsFrame2 σ Y b) (x : G2 σ Y)
    {A D : Matrix (Fin n) (Fin n) (AE F E)} (h : inFrame b x = Matrix.fromBlocks A 0 0 D) :
    Aᵀ * D.map (cA σ) = 1 ∧ Dᵀ * A.map (cA σ) = 1 := by
  obtain ⟨⟨ε, hε⟩, -⟩ := hb
  have h1 := frame_form (F := F) hε x
  rw [h, blk_form] at h1
  obtain ⟨-, h2, h3, -⟩ := Matrix.fromBlocks_inj.1 h1
  refine ⟨h2, ?_⟩
  have h4 := congrArg (fun M => (((ε : ℤ) : AE F E)) • M) h3
  simp only [smul_smul, eps_sq, one_smul] at h4
  exact h4

theorem blk_form_one {ε : ℤˣ} {A D : Matrix (Fin n) (Fin n) (AE F E)} (h1 : Aᵀ * D.map (cA σ) = 1)
    (h2 : Dᵀ * A.map (cA σ) = 1) :
    (Matrix.fromBlocks A 0 0 D)ᵀ * QA (F := F) (E := E) n ε * (Matrix.fromBlocks A 0 0 D).map (cA σ) = QA n ε := by
  rw [blk_form, h1, h2]

theorem incM_map_cA {p q : Type} (M : Matrix p q E) : (incM F M).map (cA σ) = incM F (M.map σ) := by
  ext i j; rfl

theorem incM_transpose {p q : Type} (M : Matrix p q E) : (incM F M)ᵀ = incM F Mᵀ := by
  ext i j; rfl

theorem incM_fromBlocks (A B C D : Matrix (Fin n) (Fin n) E) :
    incM F (Matrix.fromBlocks A B C D) = Matrix.fromBlocks (incM F A) (incM F B) (incM F C) (incM F D) := by
  simp only [incM, Matrix.fromBlocks_map]

def ptOf (b : GL (Fin n ⊕ Fin n) E) (M M' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) (h1 : M * M' = 1)
    (h2 : M' * M = 1) : GL (Fin n ⊕ Fin n) (AE F E) where
  val := incM F b.1 * M * incM F (b⁻¹).1
  inv := incM F b.1 * M' * incM F (b⁻¹).1
  val_inv := (conj_mul_conj b _ _).trans (by rw [h1, Matrix.mul_one, SiegelEisensteinSeries.Grp.incM_mul_inv])
  inv_val := (conj_mul_conj b _ _).trans (by rw [h2, Matrix.mul_one, SiegelEisensteinSeries.Grp.incM_mul_inv])

theorem ptOf_mem {b : GL (Fin n ⊕ Fin n) E} {ε : ℤˣ} (hb : FrameEq σ Y b ε)
    {M M' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)} (h1 : M * M' = 1) (h2 : M' * M = 1)
    (hM : Mᵀ * QA (F := F) (E := E) n ε * M.map (cA σ) = QA n ε) :
    ptOf b M M' h1 h2 ∈ UG (cA σ) (dbl (incM F Y.J)) := by
  have hF : (incM F b.1)ᵀ * dbl (incM F Y.J) * (incM F b.1).map (cA σ) = QA (F := F) (E := E) n ε :=
    frameEq_adelic (F := F) hb
  have e1 : (incM F (b⁻¹).1)ᵀ * (incM F b.1)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, SiegelEisensteinSeries.Grp.incM_mul_inv, Matrix.transpose_one]
  have e2 : (incM F b.1).map (cA σ) * (incM F (b⁻¹).1).map (cA σ) = 1 := by
    rw [← map_cA_mul, SiegelEisensteinSeries.Grp.incM_mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  show (incM F b.1 * M * incM F (b⁻¹).1)ᵀ * dbl (incM F Y.J) *
    (incM F b.1 * M * incM F (b⁻¹).1).map (cA σ) = dbl (incM F Y.J)
  rw [map_cA_mul, map_cA_mul, Matrix.transpose_mul, Matrix.transpose_mul]
  calc (incM F (b⁻¹).1)ᵀ * (Mᵀ * (incM F b.1)ᵀ) * dbl (incM F Y.J) *
        ((incM F b.1).map (cA σ) * M.map (cA σ) * (incM F (b⁻¹).1).map (cA σ))
      = (incM F (b⁻¹).1)ᵀ * (Mᵀ * ((incM F b.1)ᵀ * dbl (incM F Y.J) * (incM F b.1).map (cA σ)) *
          M.map (cA σ)) * (incM F (b⁻¹).1).map (cA σ) := by simp only [Matrix.mul_assoc]
    _ = (incM F (b⁻¹).1)ᵀ * ((incM F b.1)ᵀ * dbl (incM F Y.J) * (incM F b.1).map (cA σ)) *
          (incM F (b⁻¹).1).map (cA σ) := by rw [hF, hM, ← hF]
    _ = ((incM F (b⁻¹).1)ᵀ * (incM F b.1)ᵀ) * dbl (incM F Y.J) *
          ((incM F b.1).map (cA σ) * (incM F (b⁻¹).1).map (cA σ)) := by simp only [Matrix.mul_assoc]
    _ = dbl (incM F Y.J) := by rw [e1, e2, Matrix.one_mul, Matrix.mul_one]

theorem inFrame_ptOf {b : GL (Fin n ⊕ Fin n) E} {M M' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)}
    (h1 : M * M' = 1) (h2 : M' * M = 1) (h : ptOf b M M' h1 h2 ∈ UG (cA σ) (dbl (incM F Y.J))) :
    inFrame (σ := σ) (Y := Y) b ⟨ptOf b M M' h1 h2, h⟩ = M := by
  show incM F (b⁻¹).1 * (incM F b.1 * M * incM F (b⁻¹).1) * incM F b.1 = M
  simp only [Matrix.mul_assoc]
  rw [SiegelEisensteinSeries.Grp.incM_inv_mul, Matrix.mul_one, ← Matrix.mul_assoc, SiegelEisensteinSeries.Grp.incM_inv_mul, Matrix.one_mul]

theorem incM_one' {p : Type} [DecidableEq p] : incM F (1 : Matrix p p E) = 1 := by
  ext i j
  simp only [incM, Matrix.map_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem rat_of {b : GL (Fin n ⊕ Fin n) E} (g : G2 σ Y) (M M' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) E)
    (hM : inFrame b g = incM F M) (hM' : inFrame b g⁻¹ = incM F M') : g ∈ rat2 σ Y := by
  have hMM : M * M' = 1 := by
    apply kfour.incM_injective (F := F)
    rw [kfour.incM_mul' (F := F), ← hM, ← hM', ← inFrame_mul, mul_inv_cancel,
      inFrame_one, incM_one']
  have hMM' : M' * M = 1 := mul_eq_one_comm.1 hMM
  let gE : GL (Fin n ⊕ Fin n) E :=
    ⟨b.1 * M * (b⁻¹).1, b.1 * M' * (b⁻¹).1, by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (b⁻¹).1 b.1, Units.inv_mul, Matrix.one_mul, ← Matrix.mul_assoc M, hMM, Matrix.one_mul,
        Units.mul_inv], by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (b⁻¹).1 b.1, Units.inv_mul, Matrix.one_mul, ← Matrix.mul_assoc M', hMM', Matrix.one_mul,
        Units.mul_inv]⟩
  refine Subgroup.mem_subgroupOf.2 ⟨gE, Units.ext ?_⟩
  show (b.1 * M * (b⁻¹).1).map (inclR (F := F) (AF F)) = mat2 g
  rw [matrix_eq_frame_conjugate b, hM]
  show incM F (b.1 * M * (b⁻¹).1) = _
  rw [kfour.incM_mul', kfour.incM_mul']

theorem mapσ_mul {p : Type} [Fintype p] (X Z : Matrix p p E) : (X * Z).map σ = X.map σ * Z.map σ :=
  Matrix.map_mul (f := (σ : E →+* E))

theorem mapσ_mapσ (hσ : ∀ a, σ (σ a) = a) {p q : Type} (X : Matrix p q E) : (X.map σ).map σ = X := by
  ext i j; simp [hσ]

theorem mapσ_one {p : Type} [DecidableEq p] : (1 : Matrix p p E).map σ = 1 :=
  Matrix.map_one _ (map_zero σ) (map_one σ)

theorem levi_ex (hσ : ∀ a, σ (σ a) = a) {b : GL (Fin n ⊕ Fin n) E} (hb : IsFrame2 σ Y b) (a : GL (Fin n) E) :
    ∃ g : G2 σ Y, g ∈ rat2 σ Y ∧ inFrame b g = Matrix.fromBlocks (incM F a.1) 0 0 (incM F (((a⁻¹).1)ᵀ.map σ)) := by
  obtain ⟨⟨ε, hε⟩, -⟩ := hb
  set M0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) E := Matrix.fromBlocks a.1 0 0 (((a⁻¹).1)ᵀ.map σ) with hM0
  set M1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) E := Matrix.fromBlocks (a⁻¹).1 0 0 ((a.1)ᵀ.map σ) with hM1
  have hd : ((a⁻¹).1)ᵀ.map σ * (a.1)ᵀ.map σ = 1 := by
    rw [← mapσ_mul, ← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one, mapσ_one]
  have hd' : (a.1)ᵀ.map σ * ((a⁻¹).1)ᵀ.map σ = 1 := by
    rw [← mapσ_mul, ← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one, mapσ_one]
  have h01 : M0 * M1 = 1 := by
    rw [hM0, hM1, Matrix.fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Units.mul_inv, hd, Matrix.fromBlocks_one]
  have h10 : M1 * M0 = 1 := by
    rw [hM0, hM1, Matrix.fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Units.inv_mul, hd', Matrix.fromBlocks_one]
  have i01 : incM F M0 * incM F M1 = 1 := by rw [← kfour.incM_mul', h01, incM_one']
  have i10 : incM F M1 * incM F M0 = 1 := by rw [← kfour.incM_mul', h10, incM_one']
  have r1 : (incM F a.1)ᵀ * (incM F (((a⁻¹).1)ᵀ.map σ)).map (cA σ) = 1 := by
    rw [incM_map_cA, mapσ_mapσ hσ, incM_transpose, ← kfour.incM_mul', ← Matrix.transpose_mul, Units.inv_mul,
      Matrix.transpose_one, incM_one']
  have r2 : (incM F (((a⁻¹).1)ᵀ.map σ))ᵀ * (incM F a.1).map (cA σ) = 1 := by
    rw [incM_map_cA, incM_transpose, ← kfour.incM_mul', Matrix.transpose_map, Matrix.transpose_transpose, ← mapσ_mul,
      Units.inv_mul, mapσ_one, incM_one']
  have hM : incM F M0 = Matrix.fromBlocks (incM F a.1) 0 0 (incM F (((a⁻¹).1)ᵀ.map σ)) := by
    rw [hM0, incM_fromBlocks, show incM F (0 : Matrix (Fin n) (Fin n) E) = 0 from kfour.incM_zero]
  have hmem := ptOf_mem (F := F) (Y := Y) hε i01 i10 (by rw [hM]; exact blk_form_one r1 r2)
  set g : G2 σ Y := ⟨ptOf b _ _ i01 i10, hmem⟩
  have hg : inFrame b g = incM F M0 := inFrame_ptOf i01 i10 hmem
  have hg' : inFrame b g⁻¹ = incM F M1 := by
    have e : inFrame b g⁻¹ * inFrame b g = 1 := by rw [← inFrame_mul, inv_mul_cancel, inFrame_one]
    calc inFrame b g⁻¹ = inFrame b g⁻¹ * (incM F M0 * incM F M1) := by rw [i01, Matrix.mul_one]
      _ = (inFrame b g⁻¹ * inFrame b g) * incM F M1 := by rw [hg, Matrix.mul_assoc]
      _ = incM F M1 := by rw [e, Matrix.one_mul]
  exact ⟨g, rat_of g M0 M1 hg hg', hg.trans hM⟩

theorem rat_frame {b : GL (Fin n ⊕ Fin n) E} (g : G2 σ Y) (hg : g ∈ rat2 σ Y) :
    ∃ G0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) E, inFrame b g = incM F G0 := by
  obtain ⟨u, hu⟩ := Subgroup.mem_subgroupOf.1 hg
  refine ⟨(b⁻¹).1 * u.1 * b.1, ?_⟩
  have h : mat2 g = incM F u.1 := by
    show g.1.1 = _
    rw [← hu]
    rfl
  show incM F (b⁻¹).1 * mat2 g * incM F b.1 = _
  rw [h, kfour.incM_mul', kfour.incM_mul']

theorem rat_blocks {b : GL (Fin n ⊕ Fin n) E} (g : G2 σ Y) (hg : g ∈ rat2 σ Y) {A D : Matrix (Fin n) (Fin n) (AE F E)}
    (hAD : inFrame b g = Matrix.fromBlocks A 0 0 D) : ∃ A0 D0 : Matrix (Fin n) (Fin n) E, A = incM F A0 ∧ D = incM F D0 := by
  obtain ⟨G0, hG⟩ := rat_frame (b := b) g hg
  refine ⟨G0.toBlocks₁₁, G0.toBlocks₂₂, ?_, ?_⟩
  · have := congrArg Matrix.toBlocks₁₁ (hAD.symm.trans hG)
    rw [Matrix.toBlocks_fromBlocks₁₁] at this
    exact this
  · have := congrArg Matrix.toBlocks₂₂ (hAD.symm.trans hG)
    rw [Matrix.toBlocks_fromBlocks₂₂] at this
    exact this

variable (σ Y) in

def cNA (b : GL (Fin n ⊕ Fin n) E) (P Q P' Q' : Matrix (Fin n) (Fin n) (AE F E))
    (h : ∀ β : nA σ Y b, P * β.1 * Q ∈ nA σ Y b) (h' : ∀ β : nA σ Y b, P' * β.1 * Q' ∈ nA σ Y b)
    (e1 : P' * P = 1) (e2 : Q * Q' = 1) (e3 : P * P' = 1) (e4 : Q' * Q = 1) : nA σ Y b ≃ₜ+ nA σ Y b where
  toFun β := ⟨P * β.1 * Q, h β⟩
  invFun β := ⟨P' * β.1 * Q', h' β⟩
  left_inv β := Subtype.ext (by
    show P' * (P * β.1 * Q) * Q' = β.1
    simp only [← Matrix.mul_assoc]
    rw [e1, Matrix.one_mul, Matrix.mul_assoc, e2, Matrix.mul_one])
  right_inv β := Subtype.ext (by
    show P * (P' * β.1 * Q') * Q = β.1
    simp only [← Matrix.mul_assoc]
    rw [e3, Matrix.one_mul, Matrix.mul_assoc, e4, Matrix.mul_one])
  map_add' β γ := Subtype.ext (by
    show P * (β.1 + γ.1) * Q = P * β.1 * Q + P * γ.1 * Q
    rw [Matrix.mul_add, Matrix.add_mul])
  continuous_toFun := ((continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const).subtype_mk _
  continuous_invFun := ((continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const).subtype_mk _

theorem trace_incM {p : Type} [Fintype p] (M : Matrix p p E) :
    (incM F M).trace = inclR (F := F) (AF F) M.trace := by
  simp [Matrix.trace, incM, map_sum]

theorem psi_rat_trace {ψ : AddChar (AF F) ℂ} (hψ : ∀ x : F, ψ (algebraMap F (AF F) x) = 1) (M : Matrix (Fin n) (Fin n) E) :
    ψ (-(Algebra.trace (AF F) (AE F E) (incM F M).trace)) = 1 := by
  rw [trace_incM, kfour.inclR_eq, GlobalTheory.ThK.Dbl.Dense.trace_tmul, one_mul, ← map_neg]
  exact hψ _

theorem cNA_pres (hσ : ∀ a, σ (σ a) = a) {b : GL (Fin n ⊕ Fin n) E} (hb : IsFrame2 σ Y b) {lam : Measure (nA σ Y b)}
    {𝓖 : Set (nA σ Y b)} (hlam : lam.IsAddHaarMeasure) (h𝓖 : IsAddFundamentalDomain (nF σ Y b) 𝓖 lam) (h1 : lam 𝓖 = 1)
    (τ : nA σ Y b ≃ₜ+ nA σ Y b) (hτ : ∀ γ : nA σ Y b, γ ∈ nF σ Y b → τ γ ∈ nF σ Y b)
    (hτ' : ∀ γ : nA σ Y b, γ ∈ nF σ Y b → τ.symm γ ∈ nF σ Y b) :
    MeasurePreserving τ lam lam ∧ IsAddFundamentalDomain (nF σ Y b) (τ '' 𝓖) lam := by
  obtain ⟨hlc, hsc, ht2, hbo⟩ := nA_top hσ hb
  have := hlc; have := hsc; have := hbo
  have hm : Measurable τ := τ.continuous.measurable
  have hm' : Measurable τ.symm := τ.symm.continuous.measurable
  have : (lam.map τ).IsAddHaarMeasure := τ.isAddHaarMeasure_map lam
  have : (lam.map τ.symm).IsAddHaarMeasure := τ.symm.isAddHaarMeasure_map lam
  have e1 := Measure.isAddLeftInvariant_eq_smul (lam.map τ) lam
  have e2 := Measure.isAddLeftInvariant_eq_smul (lam.map τ.symm) lam
  have hq : Measure.QuasiMeasurePreserving τ.symm lam lam := ⟨hm', by
    rw [e2]
    exact Measure.AbsolutelyContinuous.rfl.smul_left _⟩
  let eF : nF σ Y b ≃ nF σ Y b :=
    { toFun := fun γ => ⟨τ.symm γ.1, hτ' _ γ.2⟩
      invFun := fun γ => ⟨τ γ.1, hτ _ γ.2⟩
      left_inv := fun γ => Subtype.ext (τ.apply_symm_apply γ.1)
      right_inv := fun γ => Subtype.ext (τ.symm_apply_apply γ.1) }
  have hfd : IsAddFundamentalDomain (nF σ Y b) (τ '' 𝓖) lam :=
    h𝓖.image_of_equiv τ.toEquiv hq eF fun γ x => by
      show τ (τ.symm γ.1 + x) = γ.1 + τ x
      rw [map_add, τ.apply_symm_apply]
  refine ⟨⟨hm, ?_⟩, hfd⟩
  have hmeas : lam (τ '' 𝓖) = 1 := (hfd.measure_eq h𝓖).trans h1
  let τm : nA σ Y b ≃ᵐ nA σ Y b := τ.toHomeomorph.toMeasurableEquiv
  have hmap : (lam.map τ) (τ '' 𝓖) = 1 := by
    have : lam.map τ = lam.map τm := rfl
    rw [this, MeasurableEquiv.map_apply]
    have hpre : τm ⁻¹' (τ '' 𝓖) = 𝓖 := Set.preimage_image_eq _ τ.injective
    rw [hpre, h1]
  rw [e1] at hmap ⊢
  rw [Measure.smul_apply, hmeas] at hmap
  have hc : (lam.map τ).addHaarScalarFactor lam = 1 := by
    have h2 : (((lam.map τ).addHaarScalarFactor lam : ℝ≥0) : ENNReal) = 1 := by
      rw [← hmap, ENNReal.smul_def, smul_eq_mul, mul_one]
    exact_mod_cast h2
  rw [hc, one_smul]

theorem fc_levi (hσ : ∀ a, σ (σ a) = a) {b : GL (Fin n ⊕ Fin n) E} (hb : IsFrame2 σ Y b) {ψ : AddChar (AF F) ℂ}
    (hψ : ∀ x : F, ψ (algebraMap F (AF F) x) = 1) {nb : nA σ Y b → G2 σ Y} {lam : Measure (nA σ Y b)}
    {𝓖 : Set (nA σ Y b)} (hc : CoefData (σ := σ) (Y := Y) b nb lam 𝓖) (g : G2 σ Y) (hg : g ∈ rat2 σ Y)
    {A D : Matrix (Fin n) (Fin n) (AE F E)} (hAD : inFrame b g = Matrix.fromBlocks A 0 0 D) (T T₁ : nF σ Y b)
    (hT : (A.map (cA σ))ᵀ * T.1.1 * A = T₁.1.1) (φ : G2 σ Y → ℂ) (hφ : ∀ γ ∈ rat2 σ Y, ∀ x, φ (γ * x) = φ x)
    (x : G2 σ Y) : fc ψ b nb lam 𝓖 φ T (g * x) = fc ψ b nb lam 𝓖 φ T₁ x := by
  have hn := hc.1
  obtain ⟨r1, r2⟩ := blk_rel hb g hAD
  have s1 : (D.map (cA σ))ᵀ * A = 1 := by
    have := congrArg Matrix.transpose r1
    rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at this
  have s2 : A * (D.map (cA σ))ᵀ = 1 := mul_eq_one_comm.1 s1
  have s3 : (A.map (cA σ))ᵀ * D = 1 := by
    have := congrArg Matrix.transpose r2
    rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at this
  have s4 : D * (A.map (cA σ))ᵀ = 1 := mul_eq_one_comm.1 s3
  set Dc := (D.map (cA σ))ᵀ with hDc
  set Ac := (A.map (cA σ))ᵀ with hAc
  have hinv : inFrame b g⁻¹ = Matrix.fromBlocks Dc 0 0 Ac := by
    have e : inFrame b g⁻¹ * inFrame b g = 1 := by rw [← inFrame_mul, inv_mul_cancel, inFrame_one]
    have e'' : Matrix.fromBlocks A 0 0 D * Matrix.fromBlocks Dc 0 0 Ac = 1 := by
      rw [Matrix.fromBlocks_multiply]
      simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, s2, s4, Matrix.fromBlocks_one]
    calc inFrame b g⁻¹ = inFrame b g⁻¹ * (Matrix.fromBlocks A 0 0 D * Matrix.fromBlocks Dc 0 0 Ac) := by
          rw [e'', Matrix.mul_one]
      _ = (inFrame b g⁻¹ * inFrame b g) * Matrix.fromBlocks Dc 0 0 Ac := by rw [hAD, Matrix.mul_assoc]
      _ = _ := by rw [e, Matrix.one_mul]
  have hmem : ∀ β : nA σ Y b, Dc * β.1 * D ∈ nA σ Y b := fun β => AddSubgroup.subset_closure ⟨g⁻¹ * nb β * g, by
    rw [inFrame_mul, inFrame_mul, hinv, hn β, hAD, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one, s1, s3]⟩
  have hmem' : ∀ β : nA σ Y b, A * β.1 * Ac ∈ nA σ Y b := fun β => AddSubgroup.subset_closure ⟨g * nb β * g⁻¹, by
    rw [inFrame_mul, inFrame_mul, hinv, hn β, hAD, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one, s2, s4]⟩
  let τ := cNA σ Y b Dc D A Ac hmem hmem' s2 s4 s1 s3
  have hτv : ∀ β : nA σ Y b, (τ β).1 = Dc * β.1 * D := fun β => rfl
  have hτv' : ∀ β : nA σ Y b, (τ.symm β).1 = A * β.1 * Ac := fun β => rfl
  have key : ∀ β, nb β * g = g * nb (τ β) := fun β => inFrame_injective b (by
    rw [inFrame_mul, inFrame_mul, hn, hn (τ β), hAD, hτv, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one, Matrix.one_mul]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, s2, Matrix.one_mul])
  obtain ⟨A0, D0, hA0, hD0⟩ := rat_blocks g hg hAD
  have hτF : ∀ γ : nA σ Y b, γ ∈ nF σ Y b → τ γ ∈ nF σ Y b := fun γ h => by
    obtain ⟨S, hS⟩ := (mem_nF_iff γ).1 h
    refine (mem_nF_iff _).2 ⟨(D0.map σ)ᵀ * S * D0, ?_⟩
    rw [hτv, hS, hDc, hD0, incM_map_cA, incM_transpose, kfour.incM_mul', kfour.incM_mul']
  have hτF' : ∀ γ : nA σ Y b, γ ∈ nF σ Y b → τ.symm γ ∈ nF σ Y b := fun γ h => by
    obtain ⟨S, hS⟩ := (mem_nF_iff γ).1 h
    refine (mem_nF_iff _).2 ⟨A0 * S * (A0.map σ)ᵀ, ?_⟩
    rw [hτv', hS, hAc, hA0, incM_map_cA, incM_transpose, kfour.incM_mul', kfour.incM_mul']
  obtain ⟨hpres, hfd⟩ := cNA_pres hσ hb hc.2.1 hc.2.2.1 hc.2.2.2 τ hτF hτF'
  obtain ⟨hlc, hsc, ht2, hbo⟩ := nA_top hσ hb
  have := hbo
  let H : nA σ Y b → ℂ := fun β =>
    φ (nb β * x) * ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T₁.1.1 * β.1))))
  have hint : ∀ β : nA σ Y b, φ (nb β * (g * x)) * ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 * β.1)))) =
      H (τ β) := fun β => by
    show _ = φ (nb (τ β) * x) * ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T₁.1.1 * (τ β).1))))
    rw [← mul_assoc, key, mul_assoc, hφ g hg, hτv, ← hT]
    congr 4
    calc Matrix.trace (T.1.1 * β.1) = Matrix.trace (Ac * (T.1.1 * (β.1 * D))) := by
          rw [Matrix.trace_mul_comm Ac, Matrix.mul_assoc, Matrix.mul_assoc, s4, Matrix.mul_one]
      _ = Matrix.trace (Ac * T.1.1 * A * (Dc * β.1 * D)) := by
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc A Dc, s2, Matrix.one_mul]
  have hH : ∀ (γ : nF σ Y b) (β : nA σ Y b), H (γ +ᵥ β) = H β := fun γ β => by
    show φ (nb (γ.1 + β) * x) * ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T₁.1.1 * (γ.1.1 + β.1))))) = H β
    rw [nb_add hn, mul_assoc, hφ _ (nb_rat hn γ.1 γ.2)]
    congr 1
    obtain ⟨S, hS⟩ := (mem_nF_iff γ.1).1 γ.2
    obtain ⟨T1', hT1'⟩ := (mem_nF_iff T₁.1).1 T₁.2
    rw [Matrix.mul_add, Matrix.trace_add, map_add, neg_add, AddChar.map_add_eq_mul, hT1', hS, ← kfour.incM_mul',
      psi_rat_trace hψ, one_mul]
  have := hc.2.1
  unfold fc
  simp only [hint]
  rw [← hpres.setIntegral_image_emb τ.toHomeomorph.toMeasurableEquiv.measurableEmbedding H 𝓖]
  exact hfd.setIntegral_eq hc.2.2.1 hH

end PositivityTheory.SiegelWeilFormula.Afc

end
