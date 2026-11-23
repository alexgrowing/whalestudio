import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.PsiDatum

noncomputable section

open Finset Matrix
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

open ReciprocityTheory.ChartRestriction.DS

theorem psiDatum_std {n : ℕ} (ε : Fin n → Bool) (lam : Fin n → ℝ) (h : ℝ)
    (T : S7.KType ε (lowK ε lam)) (μ : Fin n → ℤ) (hlam : S7.IsHCParam lam) (hgap : GapAtLeast ε lam h)
    (hstd : StdGap ε lam) (h8 : 8 * (n : ℝ) * S7.q0 ε < h) (hq : 1 ≤ S7.q0 ε) (hμ : S7.IsMu lam μ) :
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H)
      (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H)
      (E : Fin n → Fin n → Module.End ℂ D) (V : Submodule ℂ D) (ι : V ≃ₗ[ℂ] T.V),
      IsURepOn (UJset ε) σ ∧ IsDerivedOn ε σ D E ∧ IsKIrrHW ε E (lowK ε lam) V ∧
      (∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v) ∧
      (∀ k' ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k' v) ∧
      ∀ g ∈ UJset ε, ∀ v v' : V,
        ⟪((v' : D) : H), σ g ((v : D) : H)⟫_ℂ = ⟪ι v', S7.PsiM T μ g (ι v)⟫_ℂ := by
  have hP := S7.isPsiFor_psiM ε lam h T μ hlam hμ hgap hq h8
  set Ψ := S7.PsiM T μ with hΨ
  replace hP : IsPsiFor ε lam T Ψ := by first | exact hP | exact hP.1
  have hv₀ : T.w ≠ 0 := fun h0 => by
    have h1 := T.w_norm
    rw [h0, norm_zero] at h1
    exact zero_ne_one h1
  have hN0 : ‖uniformisationL2 ε Ψ T.w T.w‖ ≠ 0 := norm_ne_zero_iff.mpr (datumEmbedding_highest_ne_zero hstd hP hv₀)
  set c : ℂ := ((‖uniformisationL2 ε Ψ T.w T.w‖⁻¹ : ℝ) : ℂ) with hc
  have hc0 : c ≠ 0 := by rw [hc]; exact_mod_cast inv_ne_zero hN0
  let j : T.V →ₗ[ℂ] datumV ε Ψ T.w :=
    { toFun := fun v => ⟨⟨uniformisationL2 ε Ψ T.w (c • v), datumEmbedding_mem_smooth hP T.w _⟩,
        (mem_datumV_iff hP T.w _).2 ⟨c • v, rfl⟩⟩
      map_add' := fun v v' => Subtype.ext (Subtype.ext (by
        show uniformisationL2 ε Ψ T.w (c • (v + v')) = uniformisationL2 ε Ψ T.w (c • v) + uniformisationL2 ε Ψ T.w (c • v')
        rw [smul_add, datumEmbedding_add hP]))
      map_smul' := fun a v => Subtype.ext (Subtype.ext (by
        show uniformisationL2 ε Ψ T.w (c • (a • v)) = a • uniformisationL2 ε Ψ T.w (c • v)
        rw [smul_comm, datumEmbedding_smul hP])) }
  have hj : Function.Bijective j := by
    refine ⟨fun v v' hv => ?_, fun x => ?_⟩
    · have : uniformisationL2 ε Ψ T.w (c • v) = uniformisationL2 ε Ψ T.w (c • v') :=
        congrArg (fun x : datumV ε Ψ T.w => ((x : smD ε (rreg ε)) : L2 ε)) hv
      exact smul_right_injective _ hc0 (uniformisationL2_injective hP hv₀ this)
    · obtain ⟨v, hv⟩ := (mem_datumV_iff hP T.w x).1 x.2
      refine ⟨c⁻¹ • v, Subtype.ext (Subtype.ext ?_)⟩
      show uniformisationL2 ε Ψ T.w (c • c⁻¹ • v) = _
      rw [smul_smul, mul_inv_cancel₀ hc0, one_smul, hv]
  let e := LinearEquiv.ofBijective j hj
  refine ⟨L2 ε, inferInstance, inferInstance, inferInstance, rreg ε, smD ε (rreg ε), smE ε (rreg ε),
    datumV ε Ψ T.w, e.symm, rreg_isURepOn ε, isDerivedOn_smE (rreg_isURepOn ε),
    datumV_isKIrrHW hP hv₀, datumV_casimir hP T.w, datumV_kStable hP T.w, fun g hgm v v' => ?_⟩
  obtain ⟨x, rfl⟩ := e.surjective v
  obtain ⟨x', rfl⟩ := e.surjective v'
  rw [e.symm_apply_apply, e.symm_apply_apply]
  show ⟪uniformisationL2 ε Ψ T.w (c • x'), rreg ε g (uniformisationL2 ε Ψ T.w (c • x))⟫_ℂ = _
  have key : ((‖uniformisationL2 ε Ψ T.w T.w‖ ^ 2 : ℝ) : ℂ) * (starRingEnd ℂ c * c) = 1 := by
    rw [hc, Complex.conj_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_one]
    congr 1
    rw [pow_two, mul_mul_mul_comm, mul_inv_cancel₀ hN0, one_mul]
  rw [formulaF hstd hP hv₀ hgm, map_smul, inner_smul_left, inner_smul_right]
  linear_combination ⟪x', Ψ g x⟫_ℂ * key

theorem datum_link_std {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ} {h : ℝ}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
    {E : Fin n → Fin n → Module.End ℂ D} {V : Submodule ℂ D}
    (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v)
    (hlam : S7.IsHCParam lam) (hgap : GapAtLeast ε lam h) (hstd : StdGap ε lam)
    (h8 : 8 * (n : ℝ) * S7.q0 ε < h) (hq : 1 ≤ S7.q0 ε)
    (T : S7.KType ε (lowK ε lam)) {μ : Fin n → ℤ} (hμ : S7.IsMu lam μ) :
    ∃ ι : V ≃ₗ[ℂ] T.V,
      (∀ g ∈ UJset ε, ∀ v v' : V,
        ⟪((v' : D) : H), σ g ((v : D) : H)⟫_ℂ = ⟪ι v', S7.PsiM T μ g (ι v)⟫_ℂ) ∧
      (∀ v v' : V, ⟪ι v', ι v⟫_ℂ = ⟪((v' : D) : H), ((v : D) : H)⟫_ℂ) ∧
      ∀ (k : S7.KG ε) (v w : V), ((w : D) : H) = σ (S7.toMK k) ((v : D) : H) →
        ι w = T.op k (ι v) := by
  obtain ⟨H₂, _, _, _, σ₂, D₂, E₂, V₂, ι₂, hσ₂, hD₂, hV₂, hc₂, hVK₂, hco⟩ :=
    psiDatum_std ε lam h T μ hlam hgap hstd h8 hq hμ
  obtain ⟨φ, hφK, hφI⟩ := KTypeIsomorphism.exists_phi hσ hD hV hσ₂ hD₂ hV₂
  obtain ⟨ψ, -, hψI⟩ := KTypeIsomorphism.exists_phi hσ₂ hD₂ hV₂ hσ hD hV
  have := hV.1
  have := hV₂.1
  have hφi : Function.Injective φ := (injective_iff_map_eq_zero φ).mpr fun v hv => by
    have h1 := hφI v v
    rw [hv] at h1
    simpa using h1.symm
  have hψi : Function.Injective ψ := (injective_iff_map_eq_zero ψ).mpr fun v hv => by
    have h1 := hψI v v
    rw [hv] at h1
    simpa using h1.symm
  have hrk : Module.finrank ℂ V = Module.finrank ℂ V₂ :=
    le_antisymm (LinearMap.finrank_le_finrank_of_injective hφi)
      (LinearMap.finrank_le_finrank_of_injective hψi)
  let e : V ≃ₗ[ℂ] V₂ := φ.linearEquivOfInjective hφi hrk
  have hU := rigid_universal hσ hD hV hc hVK hσ₂ hD₂ hV₂ hc₂ hVK₂ hstd φ hφK hφI
  have h1J : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ UJset ε := by
    show (1 : Matrix (Fin n) (Fin n) ℂ)ᴴ * Jm ε * 1 = Jm ε
    simp
  have hcoef : ∀ g ∈ UJset ε, ∀ v v' : V, ⟪((v' : D) : H), σ g ((v : D) : H)⟫_ℂ =
      ⟪(e.trans ι₂) v', S7.PsiM T μ g ((e.trans ι₂) v)⟫_ℂ := fun g hgm v v' => by
    rw [← hU g hgm v v', hco g hgm]; rfl
  have hiso : ∀ v v' : V, ⟪(e.trans ι₂) v', (e.trans ι₂) v⟫_ℂ =
      ⟪((v' : D) : H), ((v : D) : H)⟫_ℂ := fun v v' => by
    have := hcoef 1 h1J v v'
    rw [hσ.1.1, S7.psiM_one] at this
    exact this.symm
  refine ⟨e.trans ι₂, hcoef, hiso, fun k v w hw => ?_⟩
  have hk : S7.PsiM T μ (S7.toMK k) = T.op k := by
    have := S7.psiM_equiv T μ k 1 (g := 1) h1J
    rwa [S7.toMK_one', Matrix.mul_one, Matrix.mul_one, S7.psiM_one, S7.op_one', mul_one, mul_one] at this
  refine ext_inner_left ℂ fun x => ?_
  obtain ⟨v', rfl⟩ := (e.trans ι₂).surjective x
  rw [hiso, hw, hcoef _ k.1.2, hk]

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
