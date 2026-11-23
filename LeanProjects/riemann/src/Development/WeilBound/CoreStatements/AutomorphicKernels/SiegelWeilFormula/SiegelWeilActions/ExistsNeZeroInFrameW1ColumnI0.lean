import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.PartialDerivativeAlgebra

noncomputable section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
open PositivityTheory.SiegelWeilFormula.Act.C4

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace PositivityTheory.SiegelWeilFormula.Act.C6

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : SD σ} {L : LD d}
variable {nb : nA σ d.Y d.b → d.G} {uM : (Fin L.n → AE F E) → d.G} {nb' : nA σ L.Y L.b → G2 σ L.Y} {w₁ : d.G}
  {cM : (Fin L.n → AE F E) × AF F → d.G} {δ : E}

namespace N

theorem fix_of_col {w x : d.G}
    (hc : ∀ r, inFrame d.b x r (Sum.inl L.i₀) = inFrame d.b w r (Sum.inl L.i₀)) : Fix L (w⁻¹ * x) := by
  intro k
  rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, Matrix.mul_apply]
  simp_rw [hc]
  rw [← Matrix.mul_apply, ← GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, inv_mul_cancel, GlobalTheory.EisBL.DoubledParabolic.inFrame_one]

theorem exists_ne_zero_inFrame_w1_column_i0 (h : Hyp L nb uM nb' w₁ cM δ) : ∃ b₀ : E, b₀ ≠ 0 ∧ ∀ r, inFrame d.b w₁ r (Sum.inl L.i₀) =
    inclR (F := F) (AF F) ((Pi.single (Sum.inr L.i₀) b₀ : Fin d.n ⊕ Fin d.n → E) r) := by
  obtain ⟨a, b, -, hb, hw⟩ := h.wf
  refine ⟨b, hb, fun r => ?_⟩
  rw [hw]
  rcases r with i | i <;> by_cases hi : i = L.i₀
  · subst hi; simp [Matrix.single_apply, Matrix.one_apply, Pi.single_apply]
  · simp [Matrix.single_apply, Matrix.one_apply, Pi.single_apply, hi, Ne.symm hi]
  · subst hi; simp [Matrix.single_apply, Matrix.one_apply, Pi.single_apply]
  · simp [Matrix.single_apply, Matrix.one_apply, Pi.single_apply, hi, Ne.symm hi]

theorem nCond_of_E {n : ℕ} (ε : ℤˣ) {β0 : Matrix (Fin n) (Fin n) E}
    (hβ : β0ᵀ = -((((ε : ℤ) : E)) • β0.map σ)) : incM F β0 ∈ kfour.nCond σ n ε := by
  show (incM F β0)ᵀ = -((((ε : ℤ) : AE F E)) • (incM F β0).map (cA σ))
  ext r c
  have := congrFun (congrFun hβ r) c
  simp only [Matrix.transpose_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul] at this ⊢
  simp only [incM, Matrix.map_apply]
  rw [kfour.cA_inclR', this, map_neg, map_mul, kfour.inclR_int]

theorem exists_E {n : ℕ} (i₀ : Fin n) (hσ : ∀ a, σ (σ a) = a) (ε : ℤˣ)
    {G0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) E} (hform : G0ᵀ * Bq.QE n ε * G0.map σ = Bq.QE n ε)
    {b₀ : E} (hb : b₀ ≠ 0) (hy : (fun k => G0 (Sum.inr k) (Sum.inl i₀)) ≠ 0) :
    ∃ (A : GL (Fin n) E) (β0 : Matrix (Fin n) (Fin n) E), β0ᵀ = -((((ε : ℤ) : E)) • β0.map σ) ∧
      ∀ r, ((Matrix.fromBlocks 1 β0 0 1 * Matrix.fromBlocks A.1 0 0 (((A⁻¹).1)ᵀ.map σ) * G0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) E) r (Sum.inl i₀)) = (Pi.single (Sum.inr i₀) b₀ : Fin n ⊕ Fin n → E) r := by
  set vx : Fin n → E := fun k => G0 (Sum.inl k) (Sum.inl i₀) with hvx
  set vy : Fin n → E := fun k => G0 (Sum.inr k) (Sum.inl i₀) with hvy
  set εE : E := ((ε : ℤ) : E) with hεE
  have hσε : σ εE = εE := map_intCast _ _
  have hεε : εE * εE = 1 := by
    rw [hεE, ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  have hσb : σ b₀ ≠ 0 := fun h0 => hb (by rw [← hσ b₀, h0, map_zero])
  set w : Fin n → E := fun k => σ (vy k) / σ b₀ with hw_def
  have hw0 : w ≠ 0 := by
    intro h0
    apply hy
    funext k
    have h1 := congrFun h0 k
    simp only [hw_def, Pi.zero_apply, div_eq_zero_iff, hσb, or_false] at h1
    rw [Pi.zero_apply, ← hσ (vy k), h1, map_zero]
  obtain ⟨a0, ha0⟩ := Bq.exists_gl_col i₀ w hw0
  have hdet : (a0.1ᵀ).det ≠ 0 := by
    rw [Matrix.det_transpose]
    exact (Matrix.isUnits_det_units a0).ne_zero
  set A : GL (Fin n) E := Matrix.GeneralLinearGroup.mkOfDetNeZero a0.1ᵀ hdet with hA_def
  have hArow : ∀ k, A.1 i₀ k = w k := fun k => ha0 k
  have hw : ∀ k, σ (vy k) = σ b₀ * A.1 i₀ k := fun k => by
    rw [hArow, hw_def]
    field_simp
  have hvyA : ∀ k, vy k = b₀ * σ (A.1 i₀ k) := fun k => by
    have h1 := congrArg σ (hw k)
    rw [hσ, map_mul, hσ] at h1
    exact h1
  set X : Fin n → E := A.1 *ᵥ vx with hX
  have hXi : X i₀ = ∑ j, A.1 i₀ j * vx j := rfl
  have hiso0 : ∑ j, vx j * σ (vy j) + εE * ∑ j, vy j * σ (vx j) = 0 := by
    have h1 := congrFun (congrFun hform (Sum.inl i₀)) (Sum.inl i₀)
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Bq.QE, Matrix.one_apply, Finset.mul_sum] at h1
    have e1 : ∑ j, vx j * σ (vy j) = ∑ x, G0 (Sum.inl x) (Sum.inl i₀) * σ (G0 (Sum.inr x) (Sum.inl i₀)) := rfl
    have e2 : εE * ∑ j, vy j * σ (vx j) =
        ∑ x, G0 (Sum.inr x) (Sum.inl i₀) * ((ε : ℤ) : E) * σ (G0 (Sum.inl x) (Sum.inl i₀)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [hvx, hvy, hεE]
      ring
    rw [e1, e2, add_comm]
    exact h1
  have hiso : σ b₀ * X i₀ + εE * (b₀ * σ (X i₀)) = 0 := by
    have e1 : ∑ j, vx j * σ (vy j) = σ b₀ * X i₀ := by
      rw [hXi, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hw]
      ring
    have e2 : ∑ j, vy j * σ (vx j) = b₀ * σ (X i₀) := by
      rw [hXi, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hvyA, map_mul]
      ring
    rw [← e1, ← e2]
    exact hiso0
  set col : Fin n → E := fun k => -(X k) / b₀ with hcol
  have hcol0 : col i₀ = -(εE * σ (col i₀)) := by
    simp only [hcol, map_div₀, map_neg]
    field_simp
    linear_combination (-1 : E) * hiso
  set β0 : Matrix (Fin n) (Fin n) E :=
    Matrix.of fun r c => if c = i₀ then col r else if r = i₀ then -(εE * σ (col c)) else 0 with hβ0
  refine ⟨A, β0, ?_, ?_⟩
  · ext r c
    simp only [hβ0, Matrix.transpose_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.map_apply, Matrix.of_apply,
      smul_eq_mul]
    by_cases hr : r = i₀ <;> by_cases hc : c = i₀
    · subst hr; subst hc; simp only [if_true]; exact hcol0
    · subst hr; simp only [if_true, hc, if_false, map_neg, map_mul, hσε, hσ]
      rw [mul_neg, neg_neg, ← mul_assoc, hεε, one_mul]
    · subst hc; simp [hr]
    · simp [hr, hc]
  · have hD : (((A⁻¹).1)ᵀ.map σ) *ᵥ vy = (Pi.single i₀ b₀ : Fin n → E) := by
      funext k
      calc ((((A⁻¹).1)ᵀ.map σ) *ᵥ vy) k = ∑ l, σ ((A⁻¹).1 l k) * vy l := rfl
        _ = b₀ * σ (∑ l, A.1 i₀ l * (A⁻¹).1 l k) := by
          rw [map_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [hvyA, map_mul]
          ring
        _ = b₀ * σ ((A.1 * (A⁻¹).1) i₀ k) := rfl
        _ = (Pi.single i₀ b₀ : Fin n → E) k := by
          rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
          by_cases hk : k = i₀
          · subst hk; simp
          · rw [Matrix.one_apply_ne (Ne.symm hk), Pi.single_eq_of_ne hk, map_zero, mul_zero]
    have hv : (fun m => G0 m (Sum.inl i₀)) = Sum.elim vx vy := by
      funext m
      rcases m with m | m <;> rfl
    intro r
    have hcolM : ∀ (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) E) r,
        (M * G0) r (Sum.inl i₀) = (M *ᵥ fun m => G0 m (Sum.inl i₀)) r := fun M r => rfl
    rw [hcolM, ← Matrix.mulVec_mulVec, hv]
    simp only [Matrix.fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr, Matrix.zero_mulVec, Matrix.one_mulVec,
      add_zero, zero_add, hD, ← hX, Matrix.mulVec_single]
    have hcb : ∀ k, col k * b₀ = -X k := fun k => div_mul_cancel₀ _ hb
    rcases r with i | i
    · simp only [Sum.elim_inl, Pi.add_apply, Pi.smul_apply, Matrix.col_apply, hβ0, Matrix.of_apply, if_true,
        op_smul_eq_mul, smul_eq_mul]
      rw [hcb, add_neg_cancel, Pi.single_eq_of_ne (by simp)]
    · simp only [Sum.elim_inr, Pi.smul_apply, Matrix.col_apply, op_smul_eq_mul]
      by_cases hi : i = i₀
      · subst hi; simp
      · rw [Matrix.one_apply_ne hi, zero_mul, Pi.single_eq_of_ne (by simp [hi])]

theorem normalize (h : Hyp L nb uM nb' w₁ cM δ) {γ : d.G} (hγ : γ ∈ rat2 σ d.Y) (hn : ¬ LagrangianCondition L γ) :
    ∃ p ∈ par2 σ d.Y, p ∈ rat2 σ d.Y ∧ Fix L (w₁⁻¹ * (p * γ)) := by
  have hσ := kfour.sigma_sigma_of_good d.ok.good
  obtain ⟨⟨ε, hε⟩, -⟩ := d.ok.frame
  obtain ⟨G0, hG0⟩ := Afc.rat_frame (b := d.b) γ hγ
  have hform := Bq.form_E hε γ hG0
  obtain ⟨b₀, hb₀, hw1⟩ := exists_ne_zero_inFrame_w1_column_i0 h
  have hy : (fun k => G0 (Sum.inr k) (Sum.inl L.i₀)) ≠ 0 := by
    intro h0
    apply hn
    intro i
    rw [hG0]
    show inclR (F := F) (AF F) (G0 (Sum.inr i) (Sum.inl L.i₀)) = 0
    rw [congrFun h0 i, Pi.zero_apply, map_zero]
  obtain ⟨A, β0, hβ, hcol⟩ := exists_E L.i₀ hσ ε hform hb₀ hy
  obtain ⟨pm, hpmr, hpm⟩ := Afc.levi_ex hσ d.ok.frame A
  have hpmP : pm ∈ par2 σ d.Y :=
    (ComplexParameterFamilyContinuity.mem_stabiliser_iff_frame_lower_block d.ok.frame pm).2 (by rw [hpm, Matrix.toBlocks_fromBlocks₂₁])
  have hβA : incM F β0 ∈ nA σ d.Y d.b := (kfour.mem_nA_iff hσ hε _).2 (nCond_of_E ε hβ)
  set pn := nb ⟨incM F β0, hβA⟩ with hpn_def
  have hpn : inFrame d.b pn = Matrix.fromBlocks 1 (incM F β0) 0 1 := h.nb _
  have hpnP : pn ∈ par2 σ d.Y :=
    (ComplexParameterFamilyContinuity.mem_stabiliser_iff_frame_lower_block d.ok.frame pn).2 (by rw [hpn, Matrix.toBlocks_fromBlocks₂₁])
  have hpnr : pn ∈ rat2 σ d.Y :=
    kunf.rat_of_inFrame (M := Matrix.fromBlocks 1 β0 0 1) (by rw [hpn, kfour.incM_nM]; rfl)
  refine ⟨pn * pm, mul_mem hpnP hpmP, mul_mem hpnr hpmr, fix_of_col fun r => ?_⟩
  have hF : inFrame d.b (pn * pm * γ) =
      incM F (Matrix.fromBlocks 1 β0 0 1 * Matrix.fromBlocks A.1 0 0 (((A⁻¹).1)ᵀ.map σ) * G0) := by
    rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, hpn, hpm, hG0, kfour.incM_mul', kfour.incM_mul',
      kfour.incM_nM, Afc.incM_fromBlocks, kfour.incM_zero]
    rfl
  rw [hF, hw1 r]
  show inclR (F := F) (AF F) _ = _
  rw [hcol r]

end N

end PositivityTheory.SiegelWeilFormula.Act.C6

end
