import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.HarishChandraDescent.Commutant
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.PropsEquiv
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Arbitrary
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.CFPrime
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.HarishChandraMultiplicityBound

noncomputable section

open Finset Matrix
open scoped InnerProductSpace

namespace PositivityTheory.RgHe3

open ReciprocityTheory.ChartRestriction.DS

namespace IdentityBound

theorem npq_le (n : ℕ) (ε : Fin n → Bool) : (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) ≤ (n : ℝ) ^ 3 := by
  have hp : pOf ε ≤ n := (Finset.card_filter_le _ _).trans (by simp)
  have hq : qOf ε ≤ n := (Finset.card_filter_le _ _).trans (by simp)
  have hp' : (pOf ε : ℝ) ≤ n := by exact_mod_cast hp
  have hq' : (qOf ε : ℝ) ≤ n := by exact_mod_cast hq
  have h0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h1 : (0 : ℝ) ≤ pOf ε := Nat.cast_nonneg _
  have h2 : (0 : ℝ) ≤ qOf ε := Nat.cast_nonneg _
  calc (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) ≤ (n : ℝ) * n * n := by gcongr
    _ = (n : ℝ) ^ 3 := by ring

end IdentityBound

theorem identity_holds : Ident := by
  intro n ε H _ _ _ ρ hρ mu h hmu hgap hh V hV hNo H' _ _ _ σ hσ
  have hD := isDerivedOn_smE hρ
  have hE : IsGlRep (smE ε ρ) := hD.glRep
  have hU : IsInfUnitary ε (smE ε ρ) := isInfUnitary_of_isDerivedOn hρ hD
  have h0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hstd : StdGap ε mu := ⟨hmu.1, h, hgap, by
    have := IdentityBound.npq_le n ε
    nlinarith⟩
  have hc₁ : ∀ v ∈ V, casimir (smE ε ρ) v = (casVal mu : ℂ) • v :=
    casimir_eq_casVal_of_no hmu.1 hE hU hV hNo
  have hVK₁ : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = ρ k v :=
    kStable_of_isKStableSub hρ hD V hV.1 hV.2.1
  have hV₁0 : V ≠ ⊥ := by
    obtain ⟨w, hw, hw0, -⟩ := hV.2.2.2
    intro hb
    rw [hb, Submodule.mem_bot] at hw
    exact hw0 hw
  have hσU : IsURepOn (UJset ε) σ := hσ.2.2.1
  have hcas : CasOnSmooth ε mu σ := by
    have h2n : 2 * (n : ℝ) < h := by nlinarith [pow_nonneg h0 3]
    exact (ReciprocityTheory.ChartRestriction.DS.G2.discrete_series_props_large_gap n ε mu hmu h ((mir_gapAtLeast_iff ε mu h).2 hgap) h2n H' σ hσ).1
  obtain ⟨V₂, hV₂, hV₂0, hVK₂, hc₂⟩ := arb_datum hσ hcas
  have hD₂ := isDerivedOn_smE hσU
  obtain ⟨Uq, hUq⟩ := data_unitary_equiv hstd hρ hD hV hc₁ hVK₁ hV₁0 hσU hD₂ hV₂ hc₂ hVK₂ hV₂0
  have htop : closGen (smE ε σ) V₂ = ⊤ :=
    data_closGen_eq_top hstd hσU hD₂ hV₂ hc₂ hVK₂ hσ.2.2.2.1 hV₂0

  let e₂ : H' ≃ₗᵢ[ℂ] closGen (smE ε σ) V₂ := (LinearIsometryEquiv.ofTop (p := closGen (smE ε σ) V₂) (hp := htop)).symm
  let j : H' →L[ℂ] H := (closGen (smE ε ρ) V).subtypeL.comp (Uq.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    e₂.toContinuousLinearEquiv.toContinuousLinearMap)
  have hj : ∀ x, j x = ((Uq.symm (e₂ x) : closGen (smE ε ρ) V) : H) := fun x => rfl
  have he₂ : ∀ x, ((e₂ x : closGen (smE ε σ) V₂) : H') = x := fun x => by
    show (((LinearIsometryEquiv.ofTop (p := closGen (smE ε σ) V₂) (hp := htop)).symm x : closGen (smE ε σ) V₂) : H') = x
    have := (LinearIsometryEquiv.ofTop (p := closGen (smE ε σ) V₂) (hp := htop)).apply_symm_apply x
    exact this
  refine ⟨j, ?_, ?_⟩
  · intro hj0
    have := hσ.2.1
    obtain ⟨x, hx⟩ := exists_ne (0 : H')
    apply hx
    have h1 : j x = 0 := by rw [hj0]; rfl
    rw [hj] at h1
    have h2 : Uq.symm (e₂ x) = 0 := Subtype.ext h1
    have h3 : e₂ x = 0 := by simpa using congrArg Uq h2
    have h4 := congrArg (fun y : closGen (smE ε σ) V₂ => (y : H')) h3
    simpa [he₂] using h4
  · intro g hg x

    set y : closGen (smE ε ρ) V := Uq.symm (e₂ x) with hy
    have hmem : ρ g (y : H) ∈ closGen (smE ε ρ) V :=
      closGen_stable hstd hρ hD hV hc₁ hVK₁ g hg _ y.2
    let y' : closGen (smE ε ρ) V := ⟨ρ g (y : H), hmem⟩
    have key := hUq g hg y' y rfl
    have e1 : ((Uq y : closGen (smE ε σ) V₂) : H') = x := by
      rw [hy, LinearIsometryEquiv.apply_symm_apply, he₂]
    rw [e1] at key
    have e2 : e₂ (σ g x) = Uq y' := Subtype.ext (by rw [he₂, key])
    rw [hj, hj, e2, LinearIsometryEquiv.symm_apply_apply]

end PositivityTheory.RgHe3
