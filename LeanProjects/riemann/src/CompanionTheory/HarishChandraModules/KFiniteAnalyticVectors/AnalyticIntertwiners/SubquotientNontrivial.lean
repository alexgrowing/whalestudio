import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AnalyticIntertwiners.Clause1
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.FinalAll
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.IteratedDerivOrbit

open Matrix

noncomputable section

namespace CompanionTheory.D.gk.HC

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem mem_smD_of_isKFin [CompleteSpace H] (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ)
    (hirr : Formalism.MainNotions.S.IsIrredOn (Formalism.MainNotions.S.UJset ε) σ) {v : H} (hv : Formalism.MainNotions.S.IsKFin ε σ v) : v ∈ smD ε σ := by
  exact (mem_smD_iff ε σ v).mpr (CompanionTheory.D.gk.admitted.kFin_smooth n ε H σ hσ hirr v hv)

theorem Jm_conjTranspose_self : (Jm ε)ᴴ = Jm ε := by
  rw [Jm, Matrix.diagonal_conjTranspose]
  congr 1
  funext a
  by_cases h : ε a = true <;> simp [h]

theorem UJset_mul_mem {a b : Matrix (Fin n) (Fin n) ℂ} (ha : a ∈ Formalism.MainNotions.S.UJset ε) (hb : b ∈ Formalism.MainNotions.S.UJset ε) :
    a * b ∈ Formalism.MainNotions.S.UJset ε := by
  have ha' : aᴴ * Formalism.REAL.Jm ε * a = Formalism.REAL.Jm ε := ha
  have hb' : bᴴ * Formalism.REAL.Jm ε * b = Formalism.REAL.Jm ε := hb
  show (a * b)ᴴ * Formalism.REAL.Jm ε * (a * b) = Formalism.REAL.Jm ε
  rw [Matrix.conjTranspose_mul]
  calc bᴴ * aᴴ * Formalism.REAL.Jm ε * (a * b) = bᴴ * (aᴴ * Formalism.REAL.Jm ε * a) * b := by
        simp only [Matrix.mul_assoc]
    _ = Formalism.REAL.Jm ε := by rw [ha', hb']

theorem conjTranspose_mem_kset_and_inv_eq {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Formalism.REAL.Kset ε) :
    kᴴ ∈ Formalism.REAL.Kset ε ∧ k⁻¹ = kᴴ := by
  have hk' : k ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ k * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * k := hk
  obtain ⟨hu, hc⟩ := hk'
  have hJ : (Formalism.REAL.Jm ε)ᴴ = Formalism.REAL.Jm ε := Jm_conjTranspose_self
  have h1 : kᴴ * k = 1 := by
    have := Matrix.mem_unitaryGroup_iff'.mp hu
    rwa [Matrix.star_eq_conjTranspose] at this
  refine ⟨?_, Matrix.inv_eq_left_inv h1⟩
  show kᴴ ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ kᴴ * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * kᴴ
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
    exact h1
  · have := congrArg Matrix.conjTranspose hc
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hJ] at this
    exact this.symm

theorem inG_conj_of_mem_kset {k X : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Formalism.REAL.Kset ε) (hX : inG ε X) :
    inG ε (k * X * k⁻¹) := by
  obtain ⟨hks, hinv⟩ := conjTranspose_mem_kset_and_inv_eq hk
  have hk' : k ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ k * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * k := hk
  have hks' : kᴴ ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ kᴴ * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * kᴴ := hks
  have hc : k * Jm ε = Jm ε * k := hk'.2
  have hcs : kᴴ * Jm ε = Jm ε * kᴴ := hks'.2
  have hX' : Xᴴ * Jm ε + Jm ε * X = 0 := hX
  show (k * X * k⁻¹)ᴴ * Jm ε + Jm ε * (k * X * k⁻¹) = 0
  rw [hinv, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have e1 : k * (Xᴴ * kᴴ) * Jm ε = k * (Xᴴ * Jm ε) * kᴴ := by
    simp only [Matrix.mul_assoc]
    rw [hcs]
  have e2 : Jm ε * (k * X * kᴴ) = k * (Jm ε * X) * kᴴ := by
    simp only [← Matrix.mul_assoc]
    rw [← hc]
  rw [e1, e2, ← add_mul, ← mul_add, hX', mul_zero, zero_mul]

theorem mem_UJset_of_mem_kset {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Formalism.REAL.Kset ε) : k ∈ Formalism.MainNotions.S.UJset ε := by
  have hk' : k ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ k * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * k := hk
  obtain ⟨hu, hc⟩ := hk'
  have h1 : kᴴ * k = 1 := by
    have := Matrix.mem_unitaryGroup_iff'.mp hu
    rwa [Matrix.star_eq_conjTranspose] at this
  show kᴴ * Formalism.REAL.Jm ε * k = Formalism.REAL.Jm ε
  rw [Matrix.mul_assoc, ← hc, ← Matrix.mul_assoc, h1, Matrix.one_mul]

private theorem exp_smul_mem_UJset_of_inG {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inG ε Y) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • Y) ∈ Formalism.MainNotions.S.UJset ε := by
  have hJJ : Jm ε * Jm ε = 1 := by
    rw [Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    by_cases h : ε a = true <;> simp [h]
  have hJu : IsUnit (Jm ε) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_det_of_left_inverse hJJ)
  have hJinv : (Jm ε)⁻¹ = Jm ε := Matrix.inv_eq_left_inv hJJ
  have hY' : Yᴴ * Jm ε + Jm ε * Y = 0 := hY
  have hYh : Yᴴ = Jm ε * (-Y) * (Jm ε)⁻¹ := by
    rw [hJinv]
    have h1 : Yᴴ * Jm ε = -(Jm ε * Y) := eq_neg_of_add_eq_zero_left hY'
    calc Yᴴ = Yᴴ * Jm ε * Jm ε := by rw [Matrix.mul_assoc, hJJ, Matrix.mul_one]
      _ = Jm ε * (-Y) * Jm ε := by rw [h1, Matrix.mul_neg, Matrix.neg_mul]
  have hs : star (t : ℂ) = t := Complex.conj_ofReal t
  have hAh : ((t : ℂ) • Y)ᴴ = Jm ε * (-((t : ℂ) • Y)) * (Jm ε)⁻¹ := by
    rw [Matrix.conjTranspose_smul, hs, hYh, ← smul_neg, Matrix.mul_smul, Matrix.smul_mul]
  show (NormedSpace.exp ((t : ℂ) • Y))ᴴ * Jm ε * NormedSpace.exp ((t : ℂ) • Y) = Jm ε
  rw [← Matrix.exp_conjTranspose, hAh, Matrix.exp_conj _ _ hJu, hJinv, Matrix.exp_neg]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Jm ε) (Jm ε), hJJ, Matrix.one_mul,
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.isUnit_exp _)), Matrix.mul_one]

theorem sigma_dS_conj (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) {k : Matrix (Fin n) (Fin n) ℂ}
    (hk : k ∈ Formalism.REAL.Kset ε) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (v : smD ε σ) :
    σ k (dS σ X v) = dS σ (k * X * k⁻¹) (σ k v) := by
  have hσ' : ReciprocityTheory.ChartRestriction.DS.IsURepOn (ReciprocityTheory.ChartRestriction.DS.UJset ε) σ := hσ
  obtain ⟨⟨_, hmul⟩, -, -⟩ := hσ
  have hkU : k ∈ Formalism.MainNotions.S.UJset ε := mem_UJset_of_mem_kset hk
  have hk' : k ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ k * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * k := hk
  have h1 : kᴴ * k = 1 := by
    have := Matrix.mem_unitaryGroup_iff'.mp hk'.1
    rwa [Matrix.star_eq_conjTranspose] at this
  have hku : IsUnit k := (Matrix.isUnit_iff_isUnit_det k).mpr (Matrix.isUnit_det_of_left_inverse h1)
  have hXc : inG ε (k * X * k⁻¹) := inG_conj_of_mem_kset hk hX
  have hfun : (fun t : ℝ => σ k (σ (NormedSpace.exp ((t : ℂ) • X)) (v : H))) =
      fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • (k * X * k⁻¹))) (σ k v) := by
    funext t
    have e : NormedSpace.exp ((t : ℂ) • (k * X * k⁻¹)) * k = k * NormedSpace.exp ((t : ℂ) • X) := by
      rw [show (t : ℂ) • (k * X * k⁻¹) = k * ((t : ℂ) • X) * k⁻¹ by rw [Matrix.mul_smul, Matrix.smul_mul]]
      rw [Matrix.exp_conj _ _ hku, Matrix.mul_assoc,
        Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det k).mp hku), Matrix.mul_one]
    have hE : NormedSpace.exp ((t : ℂ) • X) ∈ Formalism.MainNotions.S.UJset ε := exp_smul_mem_UJset_of_inG hX t
    have hE' : NormedSpace.exp ((t : ℂ) • (k * X * k⁻¹)) ∈ Formalism.MainNotions.S.UJset ε := exp_smul_mem_UJset_of_inG hXc t
    calc σ k (σ (NormedSpace.exp ((t : ℂ) • X)) (v : H))
        = (σ (k * NormedSpace.exp ((t : ℂ) • X))) (v : H) := by rw [hmul k hkU _ hE, ContinuousLinearMap.comp_apply]
      _ = (σ (NormedSpace.exp ((t : ℂ) • (k * X * k⁻¹)) * k)) (v : H) := by rw [e]
      _ = σ (NormedSpace.exp ((t : ℂ) • (k * X * k⁻¹))) (σ k v) := by rw [hmul _ hE' k hkU, ContinuousLinearMap.comp_apply]
  have hd : HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) (v : H))
      (((actM (smE ε σ) X) v : smD ε σ) : H) 0 := (isDerivedOn_smE hσ').deriv X hX v
  show σ k (deriv (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) (v : H)) 0) =
    deriv (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • (k * X * k⁻¹))) (σ k v)) 0
  rw [← hfun, hd.deriv]
  exact (((σ k).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd).deriv.symm

def derivedActionSpan (S : Submodule ℂ H) (hS : ∀ x ∈ S, x ∈ smD ε σ) : Submodule ℂ H :=
  ⨆ c, ⨆ d, LinearMap.range ((smD ε σ).subtype ∘ₗ smE ε σ c d ∘ₗ
    LinearMap.codRestrict (smD ε σ) S.subtype fun x => hS x x.2)

theorem derivedActionSpan_finiteDimensional (S : Submodule ℂ H) [FiniteDimensional ℂ S] (hS : ∀ x ∈ S, x ∈ smD ε σ) :
    FiniteDimensional ℂ (derivedActionSpan S hS) := by
  unfold derivedActionSpan
  infer_instance

theorem smE_mem_derivedActionSpan (S : Submodule ℂ H) (hS : ∀ x ∈ S, x ∈ smD ε σ) (c d : Fin n) {x : H} (hx : x ∈ S) :
    ((smE ε σ c d ⟨x, hS x hx⟩ : smD ε σ) : H) ∈ derivedActionSpan S hS := by
  unfold derivedActionSpan
  exact Submodule.mem_iSup_of_mem c (Submodule.mem_iSup_of_mem d (LinearMap.mem_range.mpr ⟨⟨x, hx⟩, rfl⟩))

theorem actM_mem_derivedActionSpan (S : Submodule ℂ H) (hS : ∀ x ∈ S, x ∈ smD ε σ) (Y : Matrix (Fin n) (Fin n) ℂ) {x : H}
    (hx : x ∈ S) : ((actM (smE ε σ) Y ⟨x, hS x hx⟩ : smD ε σ) : H) ∈ derivedActionSpan S hS := by
  have he : ((actM (smE ε σ) Y ⟨x, hS x hx⟩ : smD ε σ) : H) =
      ∑ a, ∑ b, Y a b • ((smE ε σ a b ⟨x, hS x hx⟩ : smD ε σ) : H) := by
    simp [actM]
  rw [he]
  exact Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ =>
    Submodule.smul_mem _ _ (smE_mem_derivedActionSpan S hS a b hx)

private theorem inG_first_chart_piece (Z : Matrix (Fin n) (Fin n) ℂ) : inG ε (ReciprocityTheory.ChartRestriction.DS.S7.cpart1 ε Z) := by
  have hJJ : Jm ε * Jm ε = 1 := by
    rw [Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    by_cases h : ε a = true <;> simp [h]
  have hJh : (Jm ε)ᴴ = Jm ε := Jm_conjTranspose_self
  have key : (Jm ε * Zᴴ * Jm ε)ᴴ = Jm ε * Z * Jm ε := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hJh, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc]
  have a1 : Jm ε * Z * Jm ε * Jm ε = Jm ε * Z := by
    rw [Matrix.mul_assoc (Jm ε * Z), hJJ, Matrix.mul_one]
  have a2 : Jm ε * (Jm ε * Zᴴ * Jm ε) = Zᴴ * Jm ε := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hJJ, Matrix.one_mul]
  have hs : star (1 / 2 : ℂ) = 1 / 2 := by
    rw [star_div₀, star_one, star_ofNat]
  show ((1 / 2 : ℂ) • (Z - Jm ε * Zᴴ * Jm ε))ᴴ * Jm ε + Jm ε * ((1 / 2 : ℂ) • (Z - Jm ε * Zᴴ * Jm ε)) = 0
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, key, hs, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.sub_mul, Matrix.mul_sub, a1, a2, ← smul_add, sub_add_sub_cancel, sub_self, smul_zero]

private theorem inG_second_chart_piece (Z : Matrix (Fin n) (Fin n) ℂ) : inG ε (ReciprocityTheory.ChartRestriction.DS.S7.cpart2 ε Z) := by
  have hJJ : Jm ε * Jm ε = 1 := by
    rw [Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    by_cases h : ε a = true <;> simp [h]
  have hJh : (Jm ε)ᴴ = Jm ε := Jm_conjTranspose_self
  have key : (Jm ε * Zᴴ * Jm ε)ᴴ = Jm ε * Z * Jm ε := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hJh, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc]
  have a1 : Jm ε * Z * Jm ε * Jm ε = Jm ε * Z := by
    rw [Matrix.mul_assoc (Jm ε * Z), hJJ, Matrix.mul_one]
  have a2 : Jm ε * (Jm ε * Zᴴ * Jm ε) = Zᴴ * Jm ε := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hJJ, Matrix.one_mul]
  have hs : star (1 / (2 * Complex.I)) = -(1 / (2 * Complex.I)) := by
    rw [star_div₀, star_one, star_mul', star_ofNat, Complex.star_def, Complex.conj_I, mul_neg, div_neg]
  show ((1 / (2 * Complex.I)) • (Z + Jm ε * Zᴴ * Jm ε))ᴴ * Jm ε +
    Jm ε * ((1 / (2 * Complex.I)) • (Z + Jm ε * Zᴴ * Jm ε)) = 0
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, key, hs, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.add_mul, Matrix.mul_add, a1, a2, add_comm (Jm ε * Z), neg_smul, neg_add_cancel]

theorem derivedActionSpan_isKStableOn (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) (S : Submodule ℂ H)
    (hS : ∀ x ∈ S, x ∈ smD ε σ) (hK : Formalism.MainNotions.S.IsKStableOn ε σ S) :
    Formalism.MainNotions.S.IsKStableOn ε σ (derivedActionSpan S hS) := by
  have hσ' : ReciprocityTheory.ChartRestriction.DS.IsURepOn (ReciprocityTheory.ChartRestriction.DS.UJset ε) σ := hσ
  have hKS : ∀ g ∈ Formalism.REAL.Kset ε, ∀ v ∈ S, σ g v ∈ S := hK
  have hD := isDerivedOn_smE hσ'
  intro g hg y hy
  have part : ∀ (Y : Matrix (Fin n) (Fin n) ℂ), inG ε Y → ∀ (w : H) (hw : w ∈ S),
      σ g (dS σ Y w) ∈ derivedActionSpan S hS := by
    intro Y hY w hw
    have hgw : σ g w ∈ S := hKS g hg w hw
    have e1 : σ g (dS σ Y w) = dS σ (g * Y * g⁻¹) (σ g w) := sigma_dS_conj hσ hg hY ⟨w, hS w hw⟩
    have e2 : dS σ (g * Y * g⁻¹) (σ g w) =
        ((actM (smE ε σ) (g * Y * g⁻¹) ⟨σ g w, hS _ hgw⟩ : smD ε σ) : H) :=
      dS_eq_actM hD (inG_conj_of_mem_kset hg hY) ⟨σ g w, hS _ hgw⟩
    rw [e1, e2]
    exact actM_mem_derivedActionSpan S hS _ hgw
  have key : ∀ (c d : Fin n) (w : H) (hw : w ∈ S),
      σ g ((smE ε σ c d ⟨w, hS w hw⟩ : smD ε σ) : H) ∈ derivedActionSpan S hS := by
    intro c d w hw
    have e : ((smE ε σ c d ⟨w, hS w hw⟩ : smD ε σ) : H) =
        dS σ (ReciprocityTheory.ChartRestriction.DS.S7.cpart1 ε (Matrix.single c d 1)) w +
          Complex.I • dS σ (ReciprocityTheory.ChartRestriction.DS.S7.cpart2 ε (Matrix.single c d 1)) w :=
      smE_apply hσ' ⟨w, hS w hw⟩ c d
    rw [e, map_add, map_smul]
    exact add_mem (part _ (inG_first_chart_piece _) w hw) (Submodule.smul_mem _ _ (part _ (inG_second_chart_piece _) w hw))
  have hle : derivedActionSpan S hS ≤ (derivedActionSpan S hS).comap ((σ g : H →L[ℂ] H) : H →ₗ[ℂ] H) := by
    refine iSup_le fun c => iSup_le fun d => ?_
    rintro _ ⟨⟨w, hw⟩, rfl⟩
    exact key c d w hw
  exact hle hy

theorem K_finite_smooth_vectors : KFSm := by
  intro n ε H _ _ _ σ hσ hirr
  refine ⟨fun v hv => mem_smD_of_isKFin hσ hirr hv, ?_⟩
  intro a b v hv
  obtain ⟨S, hfd, hvS, hK⟩ := hv
  have hS : ∀ x ∈ S, x ∈ smD ε σ := fun x hx => mem_smD_of_isKFin hσ hirr (Exists.intro S ⟨hfd, hx, hK⟩)
  exact Exists.intro (derivedActionSpan S hS)
    ⟨derivedActionSpan_finiteDimensional S hS, smE_mem_derivedActionSpan S hS a b hvS, derivedActionSpan_isKStableOn hσ S hS hK⟩

end CompanionTheory.D.gk.HC
