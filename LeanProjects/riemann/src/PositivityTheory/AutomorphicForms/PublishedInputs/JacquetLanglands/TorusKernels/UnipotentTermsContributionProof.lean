import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.MultivariableReproducingFormula

noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal ComplexConjugate

namespace UpperTheory.Esk.UnipotentTermsContribution

open UpperTheory.Esk

theorem diag {F : Type} [Field F] (g : GL (Fin 2) F) (s : Fin 2 → F) (c : F)
    (hs : s ᵥ* (g : Matrix (Fin 2) (Fin 2) F) = c • s)
    (hd : (g : Matrix (Fin 2) (Fin 2) F).trace ^ 2 ≠ 4 * (g : Matrix (Fin 2) (Fin 2) F).det)
    (δ1 : GL (Fin 2) F) (h1 : ![0, 1] ᵥ* (δ1 : Matrix (Fin 2) (Fin 2) F) = s) :
    ∃ δ : GL (Fin 2) F, (δ * g * δ⁻¹) 0 1 = 0 ∧ (δ * g * δ⁻¹) 1 0 = 0 := by
  obtain ⟨h, hh⟩ : ∃ h : GL (Fin 2) F, h = δ1 * g * δ1⁻¹ := ⟨_, rfl⟩
  have hv : ![0, 1] ᵥ* (h : Matrix (Fin 2) (Fin 2) F) = c • ![0, 1] := by
    rw [hh, Units.val_mul, Units.val_mul, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul, h1, hs,
      Matrix.smul_vecMul, ← h1, Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.vecMul_one]
  have e10 : h 1 0 = 0 := by
    have := congrFun hv 0
    simpa [Matrix.vecMul, dotProduct, Fin.sum_univ_two] using this
  have htr : (h : Matrix (Fin 2) (Fin 2) F).trace = (g : Matrix (Fin 2) (Fin 2) F).trace := by
    rw [hh, Units.val_mul, Units.val_mul, Matrix.trace_mul_cycle, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, Matrix.one_mul]
  have hdet : (h : Matrix (Fin 2) (Fin 2) F).det = (g : Matrix (Fin 2) (Fin 2) F).det := by
    rw [hh, Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, mul_right_comm, ← Matrix.det_mul,
      ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one, one_mul]
  have hne : h 0 0 - h 1 1 ≠ 0 := by
    intro e
    apply hd
    rw [← htr, ← hdet, Matrix.trace_fin_two, Matrix.det_fin_two]
    change (h 0 0 + h 1 1) ^ 2 = 4 * (h 0 0 * h 1 1 - h 0 1 * h 1 0)
    rw [e10]
    linear_combination (h 0 0 - h 1 1) * e
  obtain ⟨t, ht0⟩ : ∃ t : F, t = h 0 1 / (h 0 0 - h 1 1) := ⟨_, rfl⟩
  have ht : t * (h 0 0 - h 1 1) = h 0 1 := by rw [ht0]; exact div_mul_cancel₀ _ hne
  obtain ⟨u, hu, hu'⟩ : ∃ u : GL (Fin 2) F, (u : Matrix (Fin 2) (Fin 2) F) = !![1, t; 0, 1] ∧
      ((u⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![1, -t; 0, 1] :=
    ⟨⟨!![1, t; 0, 1], !![1, -t; 0, 1], by simp [Matrix.one_fin_two], by simp [Matrix.one_fin_two]⟩, rfl, rfl⟩
  have hc : u * δ1 * g * (u * δ1)⁻¹ = u * h * u⁻¹ := by rw [hh]; group
  have hM : ((u * δ1 * g * (u * δ1)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      !![1, t; 0, 1] * !![h 0 0, h 0 1; 0, h 1 1] * !![1, -t; 0, 1] := by
    rw [hc, Units.val_mul, Units.val_mul, hu, hu', Matrix.eta_fin_two (h : Matrix (Fin 2) (Fin 2) F), e10]
    rfl
  refine ⟨u * δ1, ?_, ?_⟩
  · rw [hM]
    simp
    linear_combination -ht
  · rw [hM]
    simp

variable {F I Gf : Type} [Field F] [Group Gf] [Fintype I] (D : Dat F I Gf)

theorem transport (hP : Pres (PG F) (volume : Measure D.Xs))
    {ι : Type} [Fintype ι] (k : I → ℕ) (a : ι → Gf) (T : ℝ)
    (hkk : ∀ (δ γ : PG F) y, D.kk k a (δ * γ * δ⁻¹) (δ • y) = D.kk k a γ y)
    (hLam : ∀ (γ δ : PG F) y, δ • y ∈ D.LamF T (δ * γ * δ⁻¹) ↔ y ∈ D.LamF T γ)
    (γ : PG F) (ω : D.Om) (δ γ' : PG F) (hγ' : δ * γ * δ⁻¹ = γ')
    (h : ∀ β : D.Xs → ℝ, IsCut (MulAction.stabilizer (PG F) ((γ', δ • ω) : D.Cj × D.Om)) β →
      Integrable (fun z => β z • (D.LamF T γ').indicator (D.kk k a γ') (δ • ω, z)) →
      ∫ z, β z • (D.LamF T γ').indicator (D.kk k a γ') (δ • ω, z) = 0)
    (β : D.Xs → ℝ) (hβ : IsCut (MulAction.stabilizer (PG F) ((γ, ω) : D.Cj × D.Om)) β)
    (hint : Integrable (fun z => β z • (D.LamF T γ).indicator (D.kk k a γ) (ω, z))) :
    ∫ z, β z • (D.LamF T γ).indicator (D.kk k a γ) (ω, z) = 0 := by
  subst hγ'
  set p : D.Cj × D.Om := (γ, ω) with hp
  have hq : δ • p = ((δ * γ * δ⁻¹ : PG F), δ • ω) := rfl
  have mem : ∀ g : PG F, g ∈ MulAction.stabilizer (PG F) (δ • p) ↔ δ⁻¹ * g * δ ∈ MulAction.stabilizer (PG F) p := by
    intro g
    simp only [MulAction.mem_stabilizer_iff, mul_smul]
    rw [inv_smul_eq_iff]
  let φ : MulAction.stabilizer (PG F) p ≃ MulAction.stabilizer (PG F) (δ • p) :=
    { toFun := fun x => ⟨δ * x * δ⁻¹, (mem _).2 (by
        have e : δ⁻¹ * (δ * (x : PG F) * δ⁻¹) * δ = x := by group
        rw [e]; exact x.2)⟩
      invFun := fun g => ⟨δ⁻¹ * g * δ, (mem _).1 g.2⟩
      left_inv := fun x => Subtype.ext (by change δ⁻¹ * (δ * (x : PG F) * δ⁻¹) * δ = x; group)
      right_inv := fun g => Subtype.ext (by change δ * (δ⁻¹ * (g : PG F) * δ) * δ⁻¹ = g; group) }
  let e : D.Xs ≃ᵐ D.Xs :=
    { toEquiv := MulAction.toPerm δ⁻¹
      measurable_toFun := (hP δ⁻¹).measurable
      measurable_invFun := (hP δ⁻¹⁻¹).measurable }
  have hme : MeasurePreserving e volume volume := hP δ⁻¹
  have he : ∀ w, e w = δ⁻¹ • w := fun _ => rfl
  set f : D.Xs → ℂ := fun z => β z • (D.LamF T γ).indicator (D.kk k a γ) (ω, z) with hf
  have key : ∀ w, f (e w) = β (δ⁻¹ • w) • (D.LamF T (δ * γ * δ⁻¹)).indicator (D.kk k a (δ * γ * δ⁻¹)) (δ • ω, w) := by
    intro w
    have hy : ((δ • ω, w) : D.Y) = δ • ((ω, δ⁻¹ • w) : D.Y) := by
      rw [Prod.smul_mk, smul_inv_smul]
    rw [hy, hf, he]
    beta_reduce
    congr 1
    by_cases hm : ((ω, δ⁻¹ • w) : D.Y) ∈ D.LamF T γ
    · rw [Set.indicator_of_mem hm, Set.indicator_of_mem ((hLam γ δ _).2 hm), hkk]
    · rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem (fun h' => hm ((hLam γ δ _).1 h'))]
  let β' : D.Xs → ℝ := fun w => β (δ⁻¹ • w)
  have hβ' : IsCut (MulAction.stabilizer (PG F) (δ • p)) β' := by
    refine ⟨hβ.meas.comp (hP δ⁻¹).measurable, fun w => hβ.nonneg _, fun w => ?_⟩
    rw [← φ.hasSum_iff]
    convert hβ.sum (δ⁻¹ • w) using 2 with x
    change β (δ⁻¹ • (δ * (x : PG F) * δ⁻¹) • w) = β ((x : PG F) • δ⁻¹ • w)
    simp only [smul_smul, show δ⁻¹ * (δ * (x : PG F) * δ⁻¹) = (x : PG F) * δ⁻¹ by group]
  have hint' : Integrable (fun w => β' w • (D.LamF T (δ * γ * δ⁻¹)).indicator (D.kk k a (δ * γ * δ⁻¹)) (δ • ω, w)) := by
    have := (hme.integrable_comp_emb e.measurableEmbedding).2 hint
    refine this.congr (Filter.Eventually.of_forall fun w => ?_)
    exact key w
  have h0 := h β' (hq ▸ hβ') hint'
  rw [← hme.integral_comp' f]
  rw [← h0]
  exact integral_congr_ae (Filter.Eventually.of_forall key)

end UpperTheory.Esk.UnipotentTermsContribution

open UpperTheory.Esk.UnipotentTermsContribution in
theorem UpperTheory.Esk.unipotent_terms_contribution_proof : UpperTheory.Esk.C1 → UpperTheory.Esk.E0a → UpperTheory.Esk.KernelTermsInvariantBounded → UpperTheory.Esk.E0d → UpperTheory.Esk.DiagonalTruncatedIntegralZero → UpperTheory.Esk.F6 := by
  intro _ hE0a hE0c hE0d hF6b F I Gf ι _ _ _ _ D k a hH T hT γ ω hγ β hβ hint
  by_cases hTe : D.Te a γ.out (D.rep ω) = 0
  · have hz : ∀ z, β z • (D.LamF T γ).indicator (D.kk k a γ) (ω, z) = 0 := by
      intro z
      simp [Dat.kk, Dat.kt, hTe]
    simp [hz]
  obtain ⟨-, -, hP, -⟩ := hE0a F I Gf D hH.ax
  obtain ⟨-, hkk, -, -, h5, h6⟩ := hE0c F I Gf ι D k a hH
  obtain ⟨-, -, -, -, -, -, -, hLamF, -, hex, -⟩ := hE0d F I Gf D hH.ax
  obtain ⟨i, hi⟩ := h5 γ ω hTe
  obtain ⟨-, hdisc⟩ := h6 γ ω i hi
  simp only [IsEll, not_forall, not_not] at hγ
  obtain ⟨s, hs0, c, hc⟩ := hγ
  obtain ⟨δ1, hδ1⟩ := hex s hs0
  obtain ⟨δ0, h01, h10⟩ := diag γ.out s c hc hdisc δ1 hδ1
  refine transport D hP k a T hkk (fun γ δ y => (hLamF T γ).2 δ y) γ ω (δ0 : PG F)
    ((δ0 * γ.out * δ0⁻¹ : GL (Fin 2) F) : PG F) ?_ ?_ β hβ hint
  · rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.out_eq']
  · intro β' hβ' hint'
    exact hF6b F I Gf ι D k a hH T hT (δ0 * γ.out * δ0⁻¹) ((δ0 : PG F) • ω) h01 h10 β' hβ' hint'
