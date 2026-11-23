import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LowerRankDatum
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FourierCompactness.SigmaSigmaOfGood
import Development.WeilBound.ThetaLifts.LatticeBasics.IsCompactIntV
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicFormCongruences.ExistsGlCol
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicFormCongruences.IncMFromBlocks

set_option linter.unusedSectionVars false

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw SiegelEisensteinSeries.Grp PositivityTheory.SiegelWeilFormula.kfour

namespace PositivityTheory.SiegelWeilFormula.Afc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

omit [NumberField E] in
theorem incM_mapc {p q : Type} (X : Matrix p q E) : (incM F X).map (cA σ) = incM F (X.map σ) := by
  ext i j; rfl

omit [NumberField E] in
theorem incM_tr {p q : Type} (X : Matrix p q E) : (incM F X)ᵀ = incM F Xᵀ := rfl

theorem cong_unip {d : SD σ} (L : LD d) (M : Matrix (Fin d.n) (Fin d.n) (AE F E))
    (h0 : ∀ i, M L.i₀ i = 0 ∧ M i L.i₀ = 0) (u : Fin L.n → AE F E) :
    ((1 + ∑ j, Matrix.single L.i₀ (L.em j) (u j)).map (cA σ))ᵀ * M * (1 + ∑ j, Matrix.single L.i₀ (L.em j) (u j)) = M := by
  have h1 : M * (∑ j, Matrix.single L.i₀ (L.em j) (u j)) = 0 := by
    ext r s
    simp only [Matrix.mul_apply, Matrix.sum_apply, Matrix.single_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : L.i₀ = k
    · subst hk; simp [(h0 r).2]
    · simp [hk]
  have h2 : ((∑ j, Matrix.single L.i₀ (L.em j) (u j)).map (cA σ))ᵀ * M = 0 := by
    ext r s
    simp only [Matrix.mul_apply, Matrix.sum_apply, Matrix.single_apply, Matrix.zero_apply, Matrix.transpose_apply,
      Matrix.map_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : L.i₀ = k
    · subst hk; simp [(h0 s).1]
    · simp [hk]
  rw [Matrix.map_add _ (map_add _), Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_add,
    Matrix.transpose_one, Matrix.add_mul, Matrix.one_mul, h2, add_zero, Matrix.mul_add, Matrix.mul_one, h1, add_zero]

theorem fc_U {d : SD σ} (L : LD d) {nb : nA σ d.Y d.b → d.G} {lam : Measure (nA σ d.Y d.b)} {𝓖 : Set (nA σ d.Y d.b)}
    (hc : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) {uM : (Fin L.n → AE F E) → d.G}
    {ν : Measure (Fin L.n → AE F E)} {𝓤 : Set (Fin L.n → AE F E)} (hU : L.UData uM ν 𝓤) (T : nF σ d.Y d.b)
    (T' : nF σ L.Y L.b) (hs : L.IsSub T T') (φ : d.G → ℂ) (hφ : ∀ γ' ∈ rat2 σ d.Y, ∀ g, φ (γ' * g) = φ g)
    (u : Fin L.n → AE F E) (hu : u ∈ L.ratV) (x : d.G) :
    fc d.B.ψ d.b nb lam 𝓖 φ T (uM u * x) = fc d.B.ψ d.b nb lam 𝓖 φ T x := by
  have hσ := sigma_sigma_of_good d.ok.good
  have hb : IsFrame2 σ d.Y d.b := d.ok.frame
  have hψ : ∀ z : F, d.B.ψ (algebraMap F (AF F) z) = 1 := d.ok.good.std.2.1
  have hcc : ∀ z, cA σ (cA σ z) = z := GlobalTheory.EisBL.DoubledUnipotentRadical.cA_cA σ hσ
  obtain ⟨v, rfl⟩ := (mem_ratV_iff L u).1 hu
  obtain ⟨a', ha'⟩ := hU.1 (GlobalTheory.ThK.incV F v)
  set N0 : Matrix (Fin d.n) (Fin d.n) E := ∑ j, Matrix.single L.i₀ (L.em j) (v j) with hN0
  have hne : ∀ j, L.em j ≠ L.i₀ := fun j => (L.rng (L.em j)).2 ⟨j, rfl⟩
  have hN2 : N0 * N0 = 0 := by
    rw [hN0, Finset.sum_mul]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_eq_zero fun j' _ => ?_
    ext r s
    simp only [Matrix.mul_apply, Matrix.single_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : L.i₀ = k
    · subst hk; simp [hne j]
    · simp [hk]
  let a : GL (Fin d.n) E := ⟨1 + N0, 1 - N0, by
      rw [mul_sub, mul_one, add_mul, one_mul, hN2, add_zero, add_sub_cancel_right], by
      rw [mul_add, mul_one, sub_mul, one_mul, hN2, sub_zero, sub_add_cancel]⟩
  obtain ⟨g, hg, hgf⟩ := levi_ex hσ hb a
  have hA : (1 + ∑ j, Matrix.single L.i₀ (L.em j) (GlobalTheory.ThK.incV F v j)) = incM F (1 + N0) := by
    ext r s
    simp [hN0, incM, Matrix.sum_apply, Matrix.single_apply, GlobalTheory.ThK.incV, Matrix.one_apply, apply_ite]
  rw [hA] at ha'
  have hgu : uM (GlobalTheory.ThK.incV F v) = g := by
    apply inFrame_injective d.b
    rw [ha', hgf]
    have r1 := (blk_rel hb _ ha').1
    have r2 := (blk_rel hb _ hgf).1
    have r1' := (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _)).1 r1
    have e1 : a'.map (cA σ) = (incM F (((a⁻¹).1)ᵀ.map σ)).map (cA σ) := by
      calc a'.map (cA σ) = a'.map (cA σ) * ((incM F (a.1))ᵀ * (incM F (((a⁻¹).1)ᵀ.map σ)).map (cA σ)) := by
            rw [r2, Matrix.mul_one]
        _ = (a'.map (cA σ) * (incM F (a.1))ᵀ) * (incM F (((a⁻¹).1)ᵀ.map σ)).map (cA σ) := by rw [Matrix.mul_assoc]
        _ = _ := by rw [r1', Matrix.one_mul]
    have e2 : a' = incM F (((a⁻¹).1)ᵀ.map σ) := by
      have := congrArg (fun M => M.map (cA σ)) e1
      simpa [Matrix.map_map, Function.comp_def, hcc] using this
    rw [e2]
  have hgm : uM (GlobalTheory.ThK.incV F v) ∈ rat2 σ d.Y := hgu ▸ hg
  refine fc_levi hσ hb hψ hc _ hgm ha' T T ?_ φ hφ x
  rw [← hA]
  exact cong_unip L T.1.1 hs.1 _

omit [NumberField E] in
theorem mapσ_mul' {p q r : Type} [Fintype q] (X : Matrix p q E) (Z : Matrix q r E) :
    (X * Z).map σ = X.map σ * Z.map σ :=
  Matrix.map_mul (f := (σ : E →+* E))

theorem nCond_rat {n : ℕ} {ε : ℤˣ} (T0 : Matrix (Fin n) (Fin n) E) (h : incM F T0 ∈ nCond σ n ε) (i j : Fin n) :
    T0 j i = -(((ε : ℤ) : E) * σ (T0 i j)) := by
  have h' : (incM F T0)ᵀ = -((((ε : ℤ) : AE F E)) • (incM F T0).map (cA σ)) := h
  have := congrFun (congrFun h' i) j
  simp only [Matrix.transpose_apply, incM, Matrix.map_apply, Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul] at this
  apply kfour.inclR_injective (F := F)
  rw [this, map_neg, map_mul, map_intCast, GlobalTheory.EisBL.DoubledUnipotentRadical.cA_inclR]

theorem fc_deg {d : SD σ} (L : LD d) {nb : nA σ d.Y d.b → d.G} {lam : Measure (nA σ d.Y d.b)} {𝓖 : Set (nA σ d.Y d.b)}
    (hc : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) (T : nF σ d.Y d.b) (hT : ¬ IsND T) :
    ∃ γ ∈ rat2 σ d.Y, ∃ T₀ T', L.IsSub T₀ T' ∧ ∀ φ : d.G → ℂ, Continuous φ →
      (∀ γ' ∈ rat2 σ d.Y, ∀ g, φ (γ' * g) = φ g) → ∀ x,
        fc d.B.ψ d.b nb lam 𝓖 φ T x = fc d.B.ψ d.b nb lam 𝓖 φ T₀ (γ * x) := by
  have hσ := sigma_sigma_of_good d.ok.good
  have hb : IsFrame2 σ d.Y d.b := d.ok.frame
  have hψ : ∀ z : F, d.B.ψ (algebraMap F (AF F) z) = 1 := d.ok.good.std.2.1
  obtain ⟨ε, hε⟩ := hb.1
  obtain ⟨ε', hε'⟩ := L.ok.frame.1
  have hee := eps_eq L hε hε'
  obtain ⟨T0, hT0⟩ := (mem_nF_iff T.1).1 T.2
  have hC : incM F T0 ∈ nCond σ d.n ε := hT0 ▸ (mem_nA_iff hσ hε T.1.1).1 T.1.2
  have hdet : T0.det = 0 := by
    have h1 : T.1.1.det = 0 := not_not.1 hT
    rw [hT0, incM, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at h1
    exact kfour.inclR_injective (F := F) (h1.trans (map_zero _).symm)
  obtain ⟨v, hv0, hTv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  obtain ⟨a', ha'⟩ := exists_gl_col v hv0 L.i₀
  obtain ⟨γ, hγ, hγf⟩ := levi_ex hσ hb a'⁻¹
  set M0 : Matrix (Fin d.n) (Fin d.n) E := (a'.1.map σ)ᵀ * T0 * a'.1 with hM0
  have hMc : incM F M0 = ((incM F a'.1).map (cA σ))ᵀ * incM F T0 * incM F a'.1 := by
    rw [incM_mapc, incM_tr, hM0, incM_mul', incM_mul']
  have hM0C : incM F M0 ∈ nCond σ d.n ε := hMc ▸ cong_nCond hσ _ _ hC
  have hM0A : incM F M0 ∈ nA σ d.Y d.b := (mem_nA_iff hσ hε _).2 hM0C
  let T₀ : nF σ d.Y d.b := ⟨⟨incM F M0, hM0A⟩, (mem_nF_iff _).2 ⟨M0, rfl⟩⟩
  have hsubC : (incM F M0).submatrix L.em L.em ∈ nCond σ L.n ε' := hee ▸ sub_nCond L.em _ hM0C
  let T' : nF σ L.Y L.b := ⟨⟨(incM F M0).submatrix L.em L.em, (mem_nA_iff hσ hε' _).2 hsubC⟩,
    (mem_nF_iff _).2 ⟨M0.submatrix L.em L.em, rfl⟩⟩
  have hcol : ∀ k, M0 k L.i₀ = 0 := fun k => by
    have e1 : M0 k L.i₀ = (((a'.1.map σ)ᵀ * T0) *ᵥ v) k := by
      simp only [hM0, Matrix.mul_apply, Matrix.mulVec, dotProduct, ha']
    rw [e1, ← Matrix.mulVec_mulVec, hTv, Matrix.mulVec_zero, Pi.zero_apply]
  have hrow : ∀ k, M0 L.i₀ k = 0 := fun k => by
    have e0 : ∀ l, ∑ p, σ (v p) * T0 p l = 0 := fun l => by
      have h1 := congrArg σ (congrFun hTv l)
      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Pi.zero_apply, map_zero] at h1
      calc ∑ p, σ (v p) * T0 p l = ∑ p, σ (v p) * -(((ε : ℤ) : E) * σ (T0 l p)) :=
            Finset.sum_congr rfl fun p _ => by rw [nCond_rat T0 hC l p]
        _ = -(((ε : ℤ) : E) * ∑ p, σ (T0 l p) * σ (v p)) := by
            rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
            exact Finset.sum_congr rfl fun p _ => by ring
        _ = 0 := by rw [h1, mul_zero, neg_zero]
    simp only [hM0, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, ha']
    simp only [e0, zero_mul, Finset.sum_const_zero]
  refine ⟨γ, hγ, T₀, T', ⟨fun i => ⟨?_, ?_⟩, rfl⟩, fun φ _ hφ x => ?_⟩
  · show inclR (F := F) (AF F) (M0 L.i₀ i) = 0
    rw [hrow, map_zero]
  · show inclR (F := F) (AF F) (M0 i L.i₀) = 0
    rw [hcol, map_zero]
  refine (fc_levi hσ hb hψ hc γ hγ hγf T₀ T ?_ φ hφ x).symm
  show ((incM F (a'⁻¹).1).map (cA σ))ᵀ * incM F M0 * incM F (a'⁻¹).1 = T.1.1
  rw [hT0, incM_mapc, incM_tr, ← incM_mul', ← incM_mul', hM0]
  congr 1
  have ha : a'.1 * (a'⁻¹).1 = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  calc ((a'⁻¹).1.map σ)ᵀ * ((a'.1.map σ)ᵀ * T0 * a'.1) * (a'⁻¹).1
      = ((a'.1 * (a'⁻¹).1).map σ)ᵀ * T0 * (a'.1 * (a'⁻¹).1) := by
        rw [mapσ_mul', Matrix.transpose_mul]
        simp only [Matrix.mul_assoc]
    _ = T0 := by rw [ha, Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]

theorem fcConj_of : AuxiliaryPrimeFunction → FcConj := fun _ _F _E _ _ _ _ _ _σ d L _nb _lam _𝓖 hc =>
  ⟨fun T hT => fc_deg L hc T hT, fun _uM _ν _𝓤 hU T T' hs φ _ hφ u hu x => fc_U L hc hU T T' hs φ hφ u hu x⟩

end PositivityTheory.SiegelWeilFormula.Afc

end
