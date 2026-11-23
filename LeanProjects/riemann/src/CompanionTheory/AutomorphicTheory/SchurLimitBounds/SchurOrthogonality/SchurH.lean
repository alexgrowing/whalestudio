import CompanionTheory.AutomorphicTheory.SchurLimitBounds.SchurOrthogonality.SchurOrthogonality
import Formalism.HermitianCurvature.BesselNonvanishingReduction

noncomputable section

namespace CompanionTheory.LimBd.SchurHpk

open MeasureTheory Matrix Topology PI.UpqRep CompanionTheory.LimBd.URep
open scoped InnerProductSpace ENNReal

theorem exists_eq_smul_haar {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (ν μ : Measure G)
    [SigmaFinite ν] [ν.IsMulLeftInvariant] (hν : ν ≠ 0) [μ.IsHaarMeasure] :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧ ν = c • μ := by
  obtain ⟨K₀⟩ : Nonempty (TopologicalSpace.PositiveCompacts G) := inferInstance
  have e := measure_eq_div_smul ν μ (s := K₀) (Measure.measure_pos_of_nonempty_interior μ K₀.interior_nonempty).ne'
    K₀.isCompact.measure_ne_top
  refine ⟨_, fun h0 => hν (by rw [e, h0, zero_smul]), fun hT => ?_, e⟩
  rw [hT] at e
  have h1 : ∀ n, μ (spanningSets ν n) = 0 := by
    intro n
    by_contra hn
    have h3 := measure_spanningSets_lt_top ν n
    have h4 := congrArg (fun m : Measure G => m (spanningSets ν n)) e
    simp only [Measure.smul_apply, smul_eq_mul, ENNReal.top_mul hn] at h4
    exact h3.ne h4
  have h2 : μ Set.univ = 0 := by
    rw [← iUnion_spanningSets ν]
    exact measure_iUnion_null h1
  exact (isOpen_univ.measure_pos μ Set.univ_nonempty).ne' h2

variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}

theorem inv_mul_P (hP : IsCayley k r ε P) : P⁻¹ * P = 1 :=
  Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hP.1)

theorem P_mul_inv (hP : IsCayley k r ε P) : P * P⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP.1)

theorem back_forth (hP : IsCayley k r ε P) (x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    P⁻¹ * (P * x * P⁻¹) * P = x := by
  calc P⁻¹ * (P * x * P⁻¹) * P = (P⁻¹ * P) * x * (P⁻¹ * P) := by simp only [Matrix.mul_assoc]
    _ = x := by rw [inv_mul_P hP, Matrix.one_mul, Matrix.mul_one]

theorem forth_back (hP : IsCayley k r ε P) (x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    P * (P⁻¹ * x * P) * P⁻¹ = x := by
  calc P * (P⁻¹ * x * P) * P⁻¹ = (P * P⁻¹) * x * (P * P⁻¹) := by simp only [Matrix.mul_assoc]
    _ = x := by rw [P_mul_inv hP, Matrix.one_mul, Matrix.mul_one]

theorem back_mul (hP : IsCayley k r ε P) (a b : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    P⁻¹ * (a * b) * P = (P⁻¹ * a * P) * (P⁻¹ * b * P) := by
  calc P⁻¹ * (a * b) * P = P⁻¹ * a * (P * P⁻¹) * b * P := by
        rw [P_mul_inv hP]; simp only [Matrix.mul_assoc, Matrix.one_mul]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem forth_mul (hP : IsCayley k r ε P) (a b : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    P * (a * b) * P⁻¹ = (P * a * P⁻¹) * (P * b * P⁻¹) := by
  calc P * (a * b) * P⁻¹ = P * a * (P⁻¹ * P) * b * P⁻¹ := by
        rw [inv_mul_P hP]; simp only [Matrix.mul_assoc, Matrix.one_mul]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem back_mem (hP : IsCayley k r ε P) {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : g ∈ UJset ε) : P⁻¹ * g * P ∈ UH (Hpk k r) := by
  have hg' : gᴴ * Jm ε * g = Jm ε := hg
  have h1 : P⁻¹ᴴ * Pᴴ = 1 := by rw [← Matrix.conjTranspose_mul, P_mul_inv hP, Matrix.conjTranspose_one]
  show (P⁻¹ * g * P)ᴴ * Hpk k r * (P⁻¹ * g * P) = Hpk k r
  rw [← hP.2]
  calc (P⁻¹ * g * P)ᴴ * (Pᴴ * Jm ε * P) * (P⁻¹ * g * P)
      = Pᴴ * (gᴴ * (P⁻¹ᴴ * Pᴴ) * Jm ε * (P * P⁻¹) * g) * P := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Pᴴ * Jm ε * P := by rw [h1, P_mul_inv hP, Matrix.mul_one, Matrix.mul_one, hg']

theorem forth_mem (hP : IsCayley k r ε P) {x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hx : x ∈ UH (Hpk k r)) : P * x * P⁻¹ ∈ UJset ε := by
  have hx' : xᴴ * (Pᴴ * Jm ε * P) * x = Pᴴ * Jm ε * P := by rw [hP.2]; exact hx
  have h1 : P⁻¹ᴴ * Pᴴ = 1 := by rw [← Matrix.conjTranspose_mul, P_mul_inv hP, Matrix.conjTranspose_one]
  show (P * x * P⁻¹)ᴴ * Jm ε * (P * x * P⁻¹) = Jm ε
  calc (P * x * P⁻¹)ᴴ * Jm ε * (P * x * P⁻¹) = P⁻¹ᴴ * (xᴴ * (Pᴴ * Jm ε * P) * x) * P⁻¹ := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = (P⁻¹ᴴ * Pᴴ) * Jm ε * (P * P⁻¹) := by rw [hx']; simp only [Matrix.mul_assoc]
    _ = Jm ε := by rw [h1, P_mul_inv hP, Matrix.one_mul, Matrix.mul_one]

def iota (P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (g : UJ ε) : Formalism.QuantumDeterminants.Mt k r :=
  P⁻¹ * umat g * P

theorem umat_mem (g : UJ ε) : umat g ∈ UJset ε := g.2

theorem iota_mem (hP : IsCayley k r ε P) (g : UJ ε) : Matrix.of (iota P g) ∈ UH (Hpk k r) :=
  back_mem hP (umat_mem g)

theorem exists_iota_eq (hP : IsCayley k r ε P) {x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hx : x ∈ UH (Hpk k r)) : ∃ g : UJ ε, Matrix.of (iota P g) = x := by
  have h : P * x * P⁻¹ ∈ Set.range (coeMatrixAlt ε) := by rw [range_coeMatrix]; exact forth_mem hP hx
  obtain ⟨g, hg⟩ := h
  refine ⟨g, ?_⟩
  show P⁻¹ * coeMatrixAlt ε g * P = x
  rw [hg, back_forth hP]

theorem iota_mul (hP : IsCayley k r ε P) (g h : UJ ε) :
    Matrix.of (iota P (g * h)) = Matrix.of (iota P g) * Matrix.of (iota P h) :=
  back_mul hP (umat g) (umat h)

theorem iota_one (hP : IsCayley k r ε P) : Matrix.of (iota P (1 : UJ ε)) = 1 := by
  show P⁻¹ * 1 * P = 1
  rw [Matrix.mul_one, inv_mul_P hP]

theorem iota_closedEmb (hP : IsCayley k r ε P) : IsClosedEmbedding (iota (ε := ε) P) := by
  let φ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ ≃ₜ
      Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ :=
    { toFun := fun x => P⁻¹ * x * P
      invFun := fun x => P * x * P⁻¹
      left_inv := forth_back hP
      right_inv := back_forth hP
      continuous_toFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
      continuous_invFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const }
  exact φ.isClosedEmbedding.comp (isClosedEmbeddingMatrix _ ε).1

theorem iota_measEmb (hP : IsCayley k r ε P) : MeasurableEmbedding (iota (ε := ε) P) :=
  (iota_closedEmb hP).measurableEmbedding

theorem exists_map_iota (hP : IsCayley k r ε P) {μG : Measure (Formalism.QuantumDeterminants.Mt k r)}
    (hμ : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) μG) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧ μG = Measure.map (iota (ε := ε) P) (c • muG ε) := by
  obtain ⟨hσ, h0, hnull, hinv⟩ := hμ
  have hE := iota_measEmb hP
  set ν : Measure (UJ ε) := Measure.comap (iota P) μG with hν
  have hmap : Measure.map (iota P) ν = μG := by
    rw [hν, hE.map_comap]
    refine Measure.restrict_eq_self_of_ae_mem ?_
    rw [ae_iff]
    refine measure_mono_null (fun x hx => ?_) hnull
    intro hxS
    exact hx (exists_iota_eq hP hxS)
  have : SigmaFinite ν := SigmaFinite.of_map ν hE.measurable.aemeasurable (by rw [hmap]; exact hσ)
  have : ν.IsMulLeftInvariant := by
    refine ⟨fun g => ?_⟩
    have hl : Measurable (Formalism.QuantumDeterminants.lmulM (k := k) (r := r) (Matrix.of (iota P g))) :=
      (show Measurable fun x : Formalism.QuantumDeterminants.Mt k r =>
        (fun i j => ∑ l, iota P g i l * x l j : Formalism.QuantumDeterminants.Mt k r) by fun_prop)
    have e : Measure.map (iota P) (Measure.map (g * ·) ν) = Measure.map (iota P) ν := by
      rw [Measure.map_map hE.measurable (measurable_const_mul g),
        show iota P ∘ (g * ·) = Formalism.QuantumDeterminants.lmulM (Matrix.of (iota P g)) ∘ iota P from
          funext fun h => iota_mul hP g h,
        ← Measure.map_map hl hE.measurable, hmap]
      exact hinv _ (iota_mem hP g)
    rw [← hE.comap_map (Measure.map (g * ·) ν), e, hE.comap_map]
  have hν0 : ν ≠ 0 := fun h => h0 (by rw [← hmap, h, Measure.map_zero])
  obtain ⟨c, hc0, hcT, e⟩ := exists_eq_smul_haar ν (muG ε) hν0
  exact ⟨c, hc0, hcT, by rw [← e, hmap]⟩

section Rep

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']

def toURep (hP : IsCayley k r ε P) (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H))
    (hσ : IsURepOn (UH (Hpk k r)) σ) : UnitaryRep (UJ ε) H :=
  have hmul : ∀ g h : UJ ε, σ (Matrix.of (iota P (g * h))) =
      (σ (Matrix.of (iota P g))).comp (σ (Matrix.of (iota P h))) := fun g h => by
    rw [iota_mul hP, hσ.1.2 _ (iota_mem hP g) _ (iota_mem hP h)]
  have hone : σ (Matrix.of (iota P (1 : UJ ε))) = 1 := by rw [iota_one hP, hσ.1.1]
  UnitaryRep.ofLinearIsometryEquiv
    { toFun := fun g => LinearIsometryEquiv.ofSurjective
        ⟨(σ (Matrix.of (iota P g)) : H →ₗ[ℂ] H), hσ.2.1 _ (iota_mem hP g)⟩
        (fun v => ⟨σ (Matrix.of (iota P g⁻¹)) v, by
          have := congrArg (fun T : H →L[ℂ] H => T v) (hmul g g⁻¹)
          simp only [mul_inv_cancel, hone] at this
          exact this.symm⟩)
      map_one' := by
        ext v
        exact congrArg (fun T : H →L[ℂ] H => T v) hone
      map_mul' := fun g h => by
        ext v
        exact congrArg (fun T : H →L[ℂ] H => T v) (hmul g h) }
    (fun v => (hσ.2.2 v).comp_continuous (f := fun g : UJ ε => Matrix.of (iota P g))
      (iota_closedEmb hP).continuous (iota_mem hP))

theorem toURep_irred (hP : IsCayley k r ε P)
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H))
    (hσ : IsURepOn (UH (Hpk k r)) σ) [Nontrivial H] (hi : IsIrredOn (UH (Hpk k r)) σ) :
    (toURep hP σ hσ).IsIrreducible := by
  refine ⟨inferInstance, fun V hV hinv => hi V hV fun x hx v hv => ?_⟩
  obtain ⟨g, rfl⟩ := exists_iota_eq hP hx
  exact hinv g v hv

omit [CompleteSpace H] in
theorem isURepOn_of_ds {lam : Fin (2 * r + k + 1) → ℝ}
    {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)} (h : IsDSHpk k r ε lam σ) :
    IsURepOn (UH (Hpk k r)) σ := by
  obtain ⟨P, ⟨hP, -⟩, -, -, ⟨⟨h1, hm⟩, hn, hc⟩, -⟩ := h
  refine ⟨⟨?_, fun a ha b hb => ?_⟩, fun x hx v => ?_, fun v => ?_⟩
  · simpa [inv_mul_P hP] using h1
  · have := hm _ (forth_mem hP ha) _ (forth_mem hP hb)
    simp only [← forth_mul hP, back_forth hP] at this
    exact this
  · have := hn _ (forth_mem hP hx) v
    simpa only [back_forth hP] using this
  · have := (hc v).comp (f := fun x => P * x * P⁻¹) (s := UH (Hpk k r))
      ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).continuousOn
      (fun x hx => forth_mem hP hx)
    simpa only [Function.comp_def, back_forth hP] using this

omit [CompleteSpace H] in
theorem isIrredOn_of_ds {lam : Fin (2 * r + k + 1) → ℝ}
    {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)} (h : IsDSHpk k r ε lam σ) :
    IsIrredOn (UH (Hpk k r)) σ := by
  obtain ⟨P, ⟨hP, -⟩, -, -, -, hi, -⟩ := h
  exact fun S hS hinv => hi S hS fun g hg v hv => hinv _ (back_mem hP hg) v hv

omit [CompleteSpace H] in
theorem memLp_of_ds {lam : Fin (2 * r + k + 1) → ℝ}
    {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)} (h : IsDSHpk k r ε lam σ)
    {μG : Measure (Formalism.QuantumDeterminants.Mt k r)}
    (hμ : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) μG) (v w : H) :
    MemLp (fun x : Formalism.QuantumDeterminants.Mt k r => ⟪w, σ (Matrix.of x) v⟫_ℂ) 2 μG := by
  obtain ⟨P, ⟨hP, -⟩, -, -, -, -, hsq, -⟩ := h
  obtain ⟨c, -, hcT, rfl⟩ := exists_map_iota hP hμ
  rw [(iota_measEmb hP).memLp_map_measure_iff]
  exact (hsq v w).smul_measure hcT

end Rep

theorem threeDimData_schurH : Formalism.FourierDecayAlt.ThreeDimData.SchurH := by
  intro k r ε lam H _ _ _ σ μG _ hds hμ
  have hU := isURepOn_of_ds hds
  have hI := isIrredOn_of_ds hds
  have hL := memLp_of_ds hds hμ
  obtain ⟨P, ⟨hP, -⟩, -, hnt, -⟩ := hds
  obtain ⟨c, hc0, hcT, e⟩ := exists_map_iota hP hμ
  have : (c • muG ε).IsHaarMeasure := Measure.IsHaarMeasure.smul _ hc0 hcT
  have hsq : SqInt (c • muG ε) (toURep hP σ hU) := fun v w => by
    have := hL v w
    rw [e, (iota_measEmb hP).memLp_map_measure_iff] at this
    exact this
  obtain ⟨d, hd, h⟩ := schur_orthogonality (toURep_irred hP σ hU hI) hsq
  refine ⟨d, hd, fun v w v' w' => ⟨(hL v w).integrable_mul (hL v' w').star, ?_⟩⟩
  rw [e, (iota_measEmb hP).integral_map]
  exact h v w v' w'

theorem schur_inequiv {k r : ℕ} {ε ε' : Fin (2 * r + k + 1) → Bool} {lam lam' : Fin (2 * r + k + 1) → ℝ}
    {H H' : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
    {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)}
    {σ' : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H' →L[ℂ] H')}
    (hds : IsDSHpk k r ε lam σ) (hds' : IsDSHpk k r ε' lam' σ')
    (hne : ¬ ∃ U : H ≃ₗᵢ[ℂ] H', ∀ g ∈ UH (Hpk k r), ∀ v, U (σ g v) = σ' g (U v))
    {μG : Measure (Formalism.QuantumDeterminants.Mt k r)}
    (hμ : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) μG) (v w : H) (v' w' : H') :
    Integrable (fun x : Formalism.QuantumDeterminants.Mt k r => ⟪w, σ (Matrix.of x) v⟫_ℂ * star ⟪w', σ' (Matrix.of x) v'⟫_ℂ) μG ∧
      ∫ x, ⟪w, σ (Matrix.of x) v⟫_ℂ * star ⟪w', σ' (Matrix.of x) v'⟫_ℂ ∂μG = 0 := by
  have hU := isURepOn_of_ds hds
  have hI := isIrredOn_of_ds hds
  have hL := memLp_of_ds hds hμ
  have hU' := isURepOn_of_ds hds'
  have hI' := isIrredOn_of_ds hds'
  have hL' := memLp_of_ds hds' hμ
  obtain ⟨-, -, -, hnt', -⟩ := hds'
  obtain ⟨P, ⟨hP, -⟩, -, hnt, -⟩ := hds
  obtain ⟨c, hc0, hcT, e⟩ := exists_map_iota hP hμ
  have : (c • muG ε).IsHaarMeasure := Measure.IsHaarMeasure.smul _ hc0 hcT
  have hsq : SqInt (c • muG ε) (toURep hP σ hU) := fun v w => by
    have := hL v w
    rw [e, (iota_measEmb hP).memLp_map_measure_iff] at this
    exact this
  have hsq' : SqInt (c • muG ε) (toURep hP σ' hU') := fun v w => by
    have := hL' v w
    rw [e, (iota_measEmb hP).memLp_map_measure_iff] at this
    exact this
  refine ⟨(hL v w).integrable_mul (hL' v' w').star, ?_⟩
  rw [e, (iota_measEmb hP).integral_map]
  refine pairing_eq_zero (toURep_irred hP σ hU hI) (toURep_irred hP σ' hU' hI') hsq hsq' ?_ v w v' w'
  rintro ⟨E⟩
  refine hne ⟨E.toLinearIsometryEquiv, fun x hx u => ?_⟩
  obtain ⟨g, rfl⟩ := exists_iota_eq hP hx
  exact E.map_apply' g u

end CompanionTheory.LimBd.SchurHpk
