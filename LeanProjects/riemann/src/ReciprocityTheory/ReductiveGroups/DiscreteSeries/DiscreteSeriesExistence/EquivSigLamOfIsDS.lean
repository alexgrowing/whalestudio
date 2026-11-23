import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Arbitrary
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Compact
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.CFPrime
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.VNormSqLowKSubRootLt
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.CompactIsDSUniqueOfCas
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.CFCore
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.SpectralGap.VogDrop

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section Datum

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ε : Fin n → Bool}
  {lam : Fin n → ℝ} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D} {V : Submodule ℂ D}

theorem cf_no_of_vogan (hgap : StdGap ε lam) (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v)
    (hvog : ∀ (μ : Fin n → ℝ) (S : Submodule ℂ H), Formalism.MainNotions.S.IsKTypeOf ε σ μ S →
      Formalism.MainNotions.S.vNormSq ε (Formalism.QuantumDeterminants.lowK ε lam) ≤ Formalism.MainNotions.S.vNormSq ε μ) :
    ∀ a b : Fin n, a < b → ε a ≠ ε b → ∀ w ∈ layer ε E V 1,
      IsKHWVec ε E (lowK ε lam - root a b) w → w = 0 := by
  intro a b hab hne w hw hkhw
  exact cfa_no_of_vogan hgap hσ hD hV hVK hvog a b hab hne w hw hkhw

theorem casOnDatum_of_isDS (hDS : Formalism.MainNotions.S.IsDS ε lam σ) (hgap : StdGap ε lam) (hD : IsDerivedOn ε σ D E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) :
    ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v := by
  have hσ : IsURepOn (UJset ε) σ := hDS.2.2.1
  exact casimir_eq_casVal_of_no hgap.1 hD.glRep (isInfUnitary_of_isDerivedOn hσ hD) hV
    (cf_no_of_vogan hgap hσ hD hV hVK hDS.2.2.2.2.2.2)

end Datum

section Arbitrary

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ε : Fin n → Bool}
  {lam : Fin n → ℝ} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem casOnSmooth_of_isDS (hDS : Formalism.MainNotions.S.IsDS ε lam σ) (hgap : StdGap ε lam) : CasOnSmooth ε lam σ := by
  exact casOnSmooth_of_copies hDS hgap
    (fun V hV hVK => casOnDatum_of_isDS hDS hgap (isDerivedOn_smE hDS.2.2.1) hV hVK)

theorem equiv_sigLam_of_isDS (hDS : Formalism.MainNotions.S.IsDS ε lam σ) (hgap : StdGap ε lam)
    {T : S7.KType ε (lowK ε lam)} {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {v₀ : T.V}
    (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0) :
    ∃ U : Hlam ε Ψ v₀ ≃ₗᵢ[ℂ] H, ∀ g ∈ UJset ε, ∀ x : Hlam ε Ψ v₀, U (sigLam ε Ψ v₀ g x) = σ g (U x) := by
  exact equiv_sigLam_of_cas hDS hgap (casOnSmooth_of_isDS hDS hgap) hP hv₀

theorem compact_isDS_unique (hpq : pOf ε = 0 ∨ qOf ε = 0) (hlam : S7.IsHCParam lam) (hDS : Formalism.MainNotions.S.IsDS ε lam σ)
    (T : S7.KType ε (lowK ε lam)) :
    CasOnSmooth ε lam σ ∧ (∀ S : Submodule ℂ H, Formalism.MainNotions.S.IsKTypeOf ε σ (Formalism.QuantumDeterminants.lowK ε lam) S → S = ⊤) ∧
      ∃ U : T.V ≃ₗᵢ[ℂ] H, ∀ k : S7.KG ε, ∀ v : T.V, U (T.op k v) = σ (S7.toMK k) (U v) := by
  have hcas := casOnSmooth_of_isDS hDS (cf_stdGap_of_pq hpq hlam.1)
  exact ⟨hcas, compact_isDS_unique_of_cas hpq hlam hDS hcas T⟩

end Arbitrary

theorem isDS_props_of_gap :
    ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam →
      ∀ h : ℝ, Formalism.QuantumDeterminants.GapAtLeast ε lam h → (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1 < h →
      ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.MainNotions.S.IsDS ε lam σ →
        CasOnSmooth ε lam σ ∧
        (∀ S S' : Submodule ℂ H, Formalism.MainNotions.S.IsKTypeOf ε σ (Formalism.QuantumDeterminants.lowK ε lam) S →
          Formalism.MainNotions.S.IsKTypeOf ε σ (Formalism.QuantumDeterminants.lowK ε lam) S' → S = S') ∧
        (∀ μ : Fin n → ℝ, FiniteDimensional ℂ (sSup {S : Submodule ℂ H | Formalism.MainNotions.S.IsKTypeOf ε σ μ S} :
          Submodule ℂ H)) ∧
        (∀ S : Submodule ℂ H, FiniteDimensional ℂ S → Formalism.MainNotions.S.IsKStableOn ε σ S →
          ∀ v ∈ S, IsSmoothVecU ε σ v) ∧
        ∀ (H' : Type) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
          (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')), Formalism.MainNotions.S.IsDS ε lam σ' →
          ∃ U : H ≃ₗᵢ[ℂ] H', ∀ g ∈ Formalism.MainNotions.S.UJset ε, ∀ x : H, U (σ g x) = σ' g (U x) := by
  intro n ε lam hlam h hh hbig H _ _ _ σ hDS
  have hgap : StdGap ε lam := ⟨hlam.1, h, hh, hbig⟩
  exact isDS_props_of_copies hlam hh hbig (fun H' _ _ _ σ' hDS' V hV hVK =>
    casOnDatum_of_isDS hDS' hgap (isDerivedOn_smE hDS'.2.2.1) hV hVK) H σ hDS

end ReciprocityTheory.ChartRestriction.DS
