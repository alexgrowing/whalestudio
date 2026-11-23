import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SigLamEquivData
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SigLamLeOfKTypes
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.ArbitraryB

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section One

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem exists_datum_of_isKTypeOf (hσ : IsURepOn (UJset ε) σ) {Λ : Fin n → ℝ} {S : Submodule ℂ H}
    (hS : Formalism.MainNotions.S.IsKTypeOf ε σ Λ S) :
    ∃ V : Submodule ℂ (smD ε σ), IsKIrrHW ε (smE ε σ) Λ V ∧ V ≠ ⊥ ∧
      (∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) ∧
      V.map (smD ε σ).subtype ≤ sSup {S' : Submodule ℂ H | Formalism.MainNotions.S.IsKTypeOf ε σ Λ S'} := by
  haveI : FiniteDimensional ℂ S := hS.1
  obtain ⟨α, hadd, hsmul, hαK, hαsm, hαS⟩ := exists_moll_data hσ S
  let A : H →ₗ[ℂ] H := { toFun := opConv ε σ α, map_add' := hadd, map_smul' := hsmul }
  have hAv : ∀ v, A v = opConv ε σ α v := fun v => rfl
  have hinj : ∀ w ∈ S, A w = 0 → w = 0 := by
    intro w hw h0
    have h1 := hαS w hw
    rw [← hAv, h0, zero_sub, norm_neg] at h1
    have h2 : ‖w‖ ≤ 0 := by linarith
    exact norm_le_zero_iff.1 h2
  have hcomm : ∀ k ∈ Kset ε, ∀ v, σ k (A v) = A (σ k v) := fun k hk v => hαK k hk v
  have hsm : ∀ v, A v ∈ smD ε σ := fun v => (mem_smD_iff ε σ _).2 (hαsm v)
  set S₁ : Submodule ℂ H := S.map A with hS₁
  have hS₁D : S₁ ≤ smD ε σ := by
    rintro _ ⟨w, _, rfl⟩
    exact hsm w
  have hirr : ∀ S' : Submodule ℂ H, S' ≤ S₁ → Formalism.MainNotions.S.IsKStableOn ε σ S' → S' = ⊥ ∨ S' = S₁ := by
    intro S' hS' hK'
    have hTK : Formalism.MainNotions.S.IsKStableOn ε σ (S ⊓ S'.comap A) := by
      intro g hg v hv
      rw [Submodule.mem_inf] at hv ⊢
      refine ⟨hS.2.1 g hg v hv.1, ?_⟩
      show A (σ g v) ∈ S'
      rw [← hcomm g hg v]
      exact hK' g hg _ hv.2
    rcases hS.2.2.1 (S ⊓ S'.comap A) inf_le_left hTK with h | h
    · left
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨w, hw, rfl⟩ := hS' hx
      have hwT : w ∈ S ⊓ S'.comap A := Submodule.mem_inf.2 ⟨hw, hx⟩
      rw [h] at hwT
      rw [(Submodule.mem_bot ℂ).1 hwT, map_zero]
      exact Submodule.zero_mem _
    · right
      refine le_antisymm hS' ?_
      rintro _ ⟨w, hw, rfl⟩
      have hwT : w ∈ S ⊓ S'.comap A := by rw [h]; exact hw
      exact (Submodule.mem_inf.1 hwT).2
  have hS₁K : Formalism.MainNotions.S.IsKTypeOf ε σ Λ S₁ := by
    refine ⟨inferInstance, ?_, hirr, ?_, ?_⟩
    · rintro g hg _ ⟨w, hw, rfl⟩
      exact ⟨σ g w, hS.2.1 g hg w hw, (hcomm g hg w).symm⟩
    · obtain ⟨v, hv, hv0, hwt⟩ := hS.2.2.2.1
      refine ⟨A v, ⟨v, hv, rfl⟩, fun h => hv0 (hinj v hv h), ?_⟩
      intro θ hθ
      rw [hcomm _ hθ, hwt θ hθ, map_smul]
    · rintro μ _ ⟨w, hw, rfl⟩ hne hwt
      refine hS.2.2.2.2 μ w hw (fun h => hne (by rw [h, map_zero])) ?_
      intro θ hθ
      have h1 : A (σ (Matrix.diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I))) w -
          Complex.exp (((∑ a, μ a * θ a : ℝ) : ℂ) * Complex.I) • w) = 0 := by
        rw [map_sub, map_smul, ← hcomm _ hθ, hwt θ hθ, sub_self]
      have h2 := hinj _ (Submodule.sub_mem _ (hS.2.1 _ hθ w hw) (Submodule.smul_mem _ _ hw)) h1
      exact sub_eq_zero.1 h2
  let V : Submodule ℂ (smD ε σ) := S₁.comap (smD ε σ).subtype
  have hVmap : V.map (smD ε σ).subtype = S₁ := by
    rw [Submodule.map_comap_subtype]
    exact inf_eq_right.2 hS₁D
  haveI hVfin : FiniteDimensional ℂ V :=
    LinearEquiv.finiteDimensional (Submodule.comapSubtypeEquivOfLe hS₁D).symm
  have hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v := by
    intro k hk v hv
    have hmem : σ k (v : H) ∈ S₁ := hS₁K.2.1 k hk _ hv
    exact ⟨⟨σ k v, hS₁D hmem⟩, hmem, rfl⟩
  have hD := isDerivedOn_smE hσ
  have hKsub : IsKStableSub ε (smE ε σ) V := isKStableSub_of_kStable hσ hD V hVfin hVK
  obtain ⟨w₀, hw₀S, hw₀, hw₀HW⟩ := exists_isKHWVec_of_isKTypeOf hσ hD hS₁K hS₁D
  refine ⟨V, ⟨hVfin, hKsub, ?_, w₀, hw₀S, hw₀, hw₀HW⟩, ?_, hVK, ?_⟩
  · intro S' hS'V hS'k
    haveI : FiniteDimensional ℂ S' := Submodule.finiteDimensional_of_le hS'V
    have hK' := kStable_of_isKStableSub hσ hD S' inferInstance hS'k
    rcases hirr (S'.map (smD ε σ).subtype) ((Submodule.map_mono hS'V).trans hVmap.le) (by
        rintro g hg _ ⟨x, hx, rfl⟩
        obtain ⟨y, hy, hyx⟩ := hK' g hg x hx
        exact ⟨y, hy, hyx⟩) with h | h
    · left
      exact Submodule.map_injective_of_injective (smD ε σ).injective_subtype (by rw [h, Submodule.map_bot])
    · right
      exact Submodule.map_injective_of_injective (smD ε σ).injective_subtype (by rw [h, hVmap])
  · intro h
    have hw₀V : w₀ ∈ V := hw₀S
    rw [h] at hw₀V
    exact hw₀ ((Submodule.mem_bot ℂ).1 hw₀V)
  · rw [hVmap]
    exact le_sSup hS₁K

variable {lam : Fin n → ℝ}

theorem arb_datum (hDS : Formalism.MainNotions.S.IsDS ε lam σ) (hcas : CasOnSmooth ε lam σ) :
    ∃ V : Submodule ℂ (smD ε σ), IsKIrrHW ε (smE ε σ) (lowK ε lam) V ∧ V ≠ ⊥ ∧
      (∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) ∧
      (∀ v ∈ V, casimir (smE ε σ) v = (casVal lam : ℂ) • v) := by
  have hσ : IsURepOn (UJset ε) σ := hDS.2.2.1
  obtain ⟨S, hS⟩ := hDS.2.2.2.2.2.1
  obtain ⟨V, hV, hV0, hVK, -⟩ := exists_datum_of_isKTypeOf hσ hS
  refine ⟨V, hV, hV0, hVK, fun v _ => ?_⟩
  apply Subtype.ext
  rw [← casU_eq_casimir (isDerivedOn_smE hσ) v]
  exact hcas _ ((mem_smD_iff ε σ _).1 v.2)

theorem lowKMultOne_of_cas (hDS : Formalism.MainNotions.S.IsDS ε lam σ) (hgap : StdGap ε lam) (hcas : CasOnSmooth ε lam σ)
    (S S' : Submodule ℂ H) (hS : Formalism.MainNotions.S.IsKTypeOf ε σ (Formalism.QuantumDeterminants.lowK ε lam) S)
    (hS' : Formalism.MainNotions.S.IsKTypeOf ε σ (Formalism.QuantumDeterminants.lowK ε lam) S') : S = S' := by
  have hσ : IsURepOn (UJset ε) σ := hDS.2.2.1
  obtain ⟨V, hV, hV0, hVK, hc⟩ := arb_datum hDS hcas
  have htop := data_closGen_eq_top hgap hσ (isDerivedOn_smE hσ) hV hc hVK hDS.2.2.2.1 hV0
  rw [data_lowK_eq hgap hσ (isDerivedOn_smE hσ) hV hc hVK S (htop ▸ le_top) hS,
    data_lowK_eq hgap hσ (isDerivedOn_smE hσ) hV hc hVK S' (htop ▸ le_top) hS']

theorem equiv_sigLam_of_cas (hDS : Formalism.MainNotions.S.IsDS ε lam σ) (hgap : StdGap ε lam) (hcas : CasOnSmooth ε lam σ)
    {T : S7.KType ε (lowK ε lam)} {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {v₀ : T.V}
    (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0) :
    ∃ U : Hlam ε Ψ v₀ ≃ₗᵢ[ℂ] H, ∀ g ∈ UJset ε, ∀ x : Hlam ε Ψ v₀, U (sigLam ε Ψ v₀ g x) = σ g (U x) := by
  have hσ : IsURepOn (UJset ε) σ := hDS.2.2.1
  obtain ⟨V, hV, hV0, hVK, hc⟩ := arb_datum hDS hcas
  have htop := data_closGen_eq_top hgap hσ (isDerivedOn_smE hσ) hV hc hVK hDS.2.2.2.1 hV0
  obtain ⟨U, hU⟩ := sigLam_equiv_data hgap hP hv₀ hσ (isDerivedOn_smE hσ) hV hc hVK hV0
  refine ⟨U.trans (LinearIsometryEquiv.ofTop _ _ htop), fun g hg x => ?_⟩
  simp only [LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.ofTop_apply]
  exact hU g hg x

end One

theorem dsUnique_of_cas {ε : Fin n → Bool} {lam : Fin n → ℝ} (hgap : StdGap ε lam)
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hDS : Formalism.MainNotions.S.IsDS ε lam σ) (hcas : CasOnSmooth ε lam σ)
    {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
    {σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')} (hDS' : Formalism.MainNotions.S.IsDS ε lam σ')
    (hcas' : CasOnSmooth ε lam σ') :
    ∃ U : H ≃ₗᵢ[ℂ] H', ∀ g ∈ UJset ε, ∀ x : H, U (σ g x) = σ' g (U x) := by
  have hσ : IsURepOn (UJset ε) σ := hDS.2.2.1
  have hσ' : IsURepOn (UJset ε) σ' := hDS'.2.2.1
  obtain ⟨V, hV, hV0, hVK, hc⟩ := arb_datum hDS hcas
  obtain ⟨V', hV', hV0', hVK', hc'⟩ := arb_datum hDS' hcas'
  have htop := data_closGen_eq_top hgap hσ (isDerivedOn_smE hσ) hV hc hVK hDS.2.2.2.1 hV0
  have htop' := data_closGen_eq_top hgap hσ' (isDerivedOn_smE hσ') hV' hc' hVK' hDS'.2.2.2.1 hV0'
  obtain ⟨U, hU⟩ := data_unitary_equiv hgap hσ (isDerivedOn_smE hσ) hV hc hVK hV0
    hσ' (isDerivedOn_smE hσ') hV' hc' hVK' hV0'
  refine ⟨((LinearIsometryEquiv.ofTop _ _ htop).symm.trans U).trans (LinearIsometryEquiv.ofTop _ _ htop'),
    fun g hg x => ?_⟩
  simp only [LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.ofTop_apply]
  apply hU g hg
  simp only [LinearIsometryEquiv.ofTop_symm_apply_coe]

end ReciprocityTheory.ChartRestriction.DS
