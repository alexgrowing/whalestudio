import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AnalyticIntertwiners.Clause1
import CompanionTheory.AutomorphicTheory.HarishChandraMultiplicity.HCMult
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.BridgeExpK
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Unitary
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCPX

open Matrix
open scoped InnerProductSpace

noncomputable section

namespace CompanionTheory.D.gk.HC

open ReciprocityTheory.ChartRestriction.DS

section

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem mem_of_forall_orthogonalComplement_inner_eq_zero (T : Submodule ℂ H) [FiniteDimensional ℂ T] {x : H} (h : ∀ y ∈ Tᗮ, ⟪y, x⟫_ℂ = 0) : x ∈ T := by
  rw [← Submodule.orthogonal_orthogonal T]
  exact (Submodule.mem_orthogonal' _ _).2 fun y hy => by rw [← inner_conj_symm, h y hy, map_zero]

theorem exists_sub_B (hK : KFSm) (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ)
    (hirr : Formalism.MainNotions.S.IsIrredOn (Formalism.MainNotions.S.UJset ε) σ) {v : smD ε σ} (hv : v ∈ KF ε σ) :
    ∃ S : Submodule ℂ (smD ε σ), FiniteDimensional ℂ S ∧ v ∈ S ∧ (S : Set (smD ε σ)) ⊆ KF ε σ ∧
      IsKStableSub ε (smE ε σ) S ∧ ∀ k ∈ Kset ε, ∀ w ∈ S, ∃ w' ∈ S, (w' : H) = σ k w := by
  obtain ⟨S, hSf, hvS, hSK⟩ := hv
  let S' : Submodule ℂ (smD ε σ) := S.comap (smD ε σ).subtype
  have hmap : S'.map (smD ε σ).subtype ≤ S := Submodule.map_comap_le _ _
  have hS'f : FiniteDimensional ℂ S' := by
    have e := Submodule.equivMapOfInjective (smD ε σ).subtype Subtype.val_injective S'
    have : FiniteDimensional ℂ (S'.map (smD ε σ).subtype) := Submodule.finiteDimensional_of_le hmap
    exact LinearEquiv.finiteDimensional e.symm
  have hKF : (S' : Set (smD ε σ)) ⊆ KF ε σ := fun w hw => ⟨S, hSf, hw, hSK⟩
  have hS'K : ∀ k ∈ Kset ε, ∀ w ∈ S', ∃ w' ∈ S', (w' : H) = σ k w := by
    intro k hk w hw
    have h1 : σ k w ∈ S := hSK k hk w hw
    have h2 : σ k w ∈ smD ε σ := (hK _ ε H σ hσ hirr).1 _ ⟨S, hSf, h1, hSK⟩
    exact ⟨⟨_, h2⟩, h1, rfl⟩
  exact ⟨S', hS'f, hvS, hKF, isKStableSub_of_kStable hσ (isDerivedOn_smE hσ) S' hS'f hS'K, hS'K⟩

theorem kavg_mem_B (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) {e : Formalism.REAL.KG ε → ℂ} (he : Continuous e)
    (T : Submodule ℂ H) [FiniteDimensional ℂ T] {x : H} (hx : ∀ k : Formalism.REAL.KG ε, σ (Formalism.REAL.toMK k) x ∈ T) :
    Formalism.MainNotions.BridgeCPX.kavg hσ he x ∈ T := by
  refine mem_of_forall_orthogonalComplement_inner_eq_zero T fun y hy => ?_
  rw [show Formalism.MainNotions.BridgeCPX.kavg hσ he x = _ from Formalism.MainNotions.BridgeCPX.kavg_apply hσ he x, ← integral_inner (Formalism.MainNotions.BridgeCPX.kavg_integrable hσ he x)]
  refine MeasureTheory.integral_eq_zero_of_ae (Filter.Eventually.of_forall fun k => ?_)
  simp only [inner_smul_right, Pi.zero_apply]
  rw [Submodule.inner_left_of_mem_orthogonal (hx k) hy, mul_zero]

end

theorem uIrr_of (hK : KFSm) (hC : CasScal) : UIrr := by
  intro n ε H _ _ _ σ hσ hirr N hNK hNst
  have hD := isDerivedOn_smE hσ
  obtain ⟨c, hc⟩ := hC n ε H σ hσ hirr
  by_cases hN : N = ⊥
  · exact Or.inl hN
  right
  obtain ⟨v, hvN, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hN
  obtain ⟨S, hSf, hvS, -, hSst, -⟩ := exists_sub_B hK hσ hirr (hNK hvN)
  let V := N ⊓ S
  have hVf : FiniteDimensional ℂ V := Submodule.finiteDimensional_of_le inf_le_right
  have hVK : IsKStableSub ε (smE ε σ) V := fun a b hab w hw => ⟨hNst a b w hw.1, hSst a b hab w hw.2⟩
  have hgen : genSub (smE ε σ) V ≤ N := sInf_le ⟨inf_le_left, fun a b w hw => hNst a b w hw⟩
  set C := ((genSub (smE ε σ) V).map (smD ε σ).subtype).topologicalClosure with hCdef
  have hvC : (v : H) ∈ C := Submodule.le_topologicalClosure _
    (Submodule.mem_map_of_mem (Submodule.mem_sInf.2 fun T hT => hT.1 ⟨hvN, hvS⟩))
  have hCtop : C = ⊤ := by
    rcases hirr C (Submodule.isClosed_topologicalClosure _)
      (closure_genSub_stable hσ hD hVf hVK fun w _ => hc w) with h | h
    · exfalso
      rw [h, Submodule.mem_bot] at hvC
      exact hv0 (Subtype.ext hvC)
    · exact h
  refine Set.Subset.antisymm hNK fun u hu => ?_
  obtain ⟨e, T, he, hTf, hrange, hfix⟩ :=
    Formalism.MainNotions.BridgeCPX.HCAdm_of_mult CompanionTheory.HCMult.harish_chandra_multiplicity n ε H σ hσ hirr (u : H) hu
  set P := Formalism.MainNotions.BridgeCPX.kavg hσ he
  let NT : Submodule ℂ H := N.map (smD ε σ).subtype ⊓ T
  have : FiniteDimensional ℂ NT := Submodule.finiteDimensional_of_le inf_le_right
  have hPN : ∀ w ∈ N, P w ∈ NT := by
    intro w hw
    obtain ⟨S₁, hS₁f, hwS₁, -, hS₁st, -⟩ := exists_sub_B hK hσ hirr (hNK hw)
    let V₁ := N ⊓ S₁
    have hV₁f : FiniteDimensional ℂ V₁ := Submodule.finiteDimensional_of_le inf_le_right
    have hV₁K : IsKStableSub ε (smE ε σ) V₁ := fun a b hab x hx => ⟨hNst a b x hx.1, hS₁st a b hab x hx.2⟩
    have hKst := kStable_of_isKStableSub hσ hD V₁ hV₁f hV₁K
    let W₁ : Submodule ℂ H := V₁.map (smD ε σ).subtype
    have : FiniteDimensional ℂ W₁ := Module.Finite.map V₁ _
    have h1 : P w ∈ W₁ := kavg_mem_B hσ he W₁ fun k => by
      obtain ⟨x, hx, hxe⟩ := hKst _ k.2 w ⟨hw, hwS₁⟩
      exact ⟨x, hx, hxe⟩
    obtain ⟨x, hx, hxe⟩ := Submodule.mem_map.1 h1
    refine ⟨Submodule.mem_map.2 ⟨x, hx.1, hxe⟩, ?_⟩
    exact hrange w
  have hclosed : IsClosed (NT : Set H) := Submodule.closed_of_finiteDimensional NT
  have hsub : (P '' ((genSub (smE ε σ) V).map (smD ε σ).subtype : Set H)) ⊆ NT := by
    rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    exact hPN w (hgen hw)
  have huC : (u : H) ∈ closure ((genSub (smE ε σ) V).map (smD ε σ).subtype : Set H) := by
    rw [← Submodule.topologicalClosure_coe, ← hCdef, hCtop]; trivial
  have h1 : P u ∈ NT := (hclosed.closure_subset_iff.2 hsub) (image_closure_subset_closure_image P.continuous
    ⟨_, huC, rfl⟩)
  have hPu : P u = u := hfix
  rw [hPu] at h1
  obtain ⟨x, hx, hxe⟩ := Submodule.mem_map.1 h1.1
  have : x = u := Subtype.ext hxe
  exact this ▸ hx

end CompanionTheory.D.gk.HC
