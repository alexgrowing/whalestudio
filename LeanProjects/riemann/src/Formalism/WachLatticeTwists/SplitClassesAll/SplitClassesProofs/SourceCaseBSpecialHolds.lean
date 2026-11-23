import Formalism.WachLatticeTwists.SplitClassesAll.SourceTwoCasesOrSubfield
import Formalism.WachLatticeTwists.SplitClassesAll.SplitClassesProofs.SrcNO
import Formalism.WachLatticeTwists.HerrComplexInjectivity.HerrComplexProofs.LiftCaseAHerrSources

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.SplitClassesAll

open Formalism.CoboundaryTransfers Formalism.RepresentationBoundsCohomology.N1 Formalism.RepresentationBoundsCohomology.N2 Formalism.RepresentationBoundsCohomology.JL Formalism.RepresentationBoundsCohomology.JN

set_option maxHeartbeats 4000000 in
theorem srcNA : StatSrcNA := by
  intro ℓ _ H₁ H₂ _ _ _ _ Hf₁ Hf₂ g e hS
  obtain ⟨hℓ2, hS⟩ := hS
  refine hS _ ?_
  intro A A₀ _ _ _ _ S B Δ _ _ _ IB ι _ pr D₀ D₁ D₂ _ _ _ _ _ _ _ _ _ _ _ _ W₀ W₁ W₂ E M h M₀ H
    ρ₀ ρ₁ ρ₂ D₀' D₁' D₂' _ _ _ _ _ _ _ _ _ _ _ _ j₀ j₁ j₂ φ₀ γ₀ φ₁ γ₁ φ₂ γ₂ u jumps hℓ hs hc hu hR hD
    a0 a1 a2 b0 b1 b2 c0 c1 c2 hP6 hM hH hp hcard hΔ hmodπ hcap hreg hQL hdiv hjac i0 i1 i2 d0 d1 d2
    hι hπ hnt hGal hrat he
  obtain ⟨V₀, V₁, V₂, Sq, J₀, J₁, J₂, e0, e1, e2, hSι, hSπ, -⟩ := lift_case_a_odd_prime ℓ hℓ2 A A₀ S B Δ IB ι
    pr D₀ D₁ D₂ W₀ W₁ W₂ E M h M₀ H ρ₀ ρ₁ ρ₂ D₀' D₁' D₂' j₀ j₁ j₂ φ₀ γ₀ φ₁ γ₁ φ₂ γ₂ u jumps hℓ hs hc hu
    hR hD a0 a1 a2 b0 b1 b2 c0 c1 c2 hP6 hM hH hp hcard hΔ hmodπ hcap hreg hQL hdiv hjac i0 i1 i2 d0 d1
    d2 hι hπ hnt
  obtain ⟨δ, R, P, ρ, κ, _, _, _, _, _, _, _, L, cl₁, cl₂, _, hδ, hP4, hj, hnat, hc1, hc2, hinj, he1, he2⟩ :=
    hGal V₀ V₁ V₂ Sq J₀ J₁ J₂ e0 e1 e2 hSι hSπ
  obtain ⟨n1, -⟩ := delta_basis_holds ℤ_[ℓ] A S Δ ι pr D₁ W₁ ρ₁ hR (card_unit' ℓ A _ hcard) d1
  obtain ⟨s2, -, -, -, -⟩ := d2
  obtain ⟨-, -, -, y4, y5, -⟩ := i1
  obtain ⟨-, -, -, z4, z5, -⟩ := i2
  obtain ⟨e1j, e1φ, e1γ⟩ := e1
  obtain ⟨e2j, e2φ, e2γ⟩ := e2
  have k1 : J₁.Compat := ⟨by rw [e1j, e1φ]; exact y4, by rw [e1j, e1γ]; exact y5⟩
  have k2 : J₂.Compat := ⟨by rw [e2j, e2φ]; exact z4, by rw [e2j, e2γ]; exact z5⟩
  obtain ⟨-, -, -, -, -, -, -, q8, -, -⟩ := base_case_b ℓ A S hℓ
  have hval : PadicInt.valuation ((u : ℤ_[ℓ]) - 1) = 1 := by rw [hu, q8 hc, hs]
  obtain ⟨hPhi, hGX⟩ := base_case_a ℤ_[ℓ] A A₀ S B Δ IB hs hΔ hmodπ hcap hreg
  rw [hcard] at hPhi hGX
  rw [← hu] at hGX
  have hGQ := gamma_quotient_case_a ℤ_[ℓ] A₀ B hQL hdiv hjac
  obtain ⟨c, hcc, -, -⟩ := consequence_five_holds ℓ u hℓ2 hval
  obtain ⟨l1, l3⟩ := regulator_quotient_case_a ℓ A A₀ S B Δ IB ι pr D₀ W₀ ρ₀ M₀ D₀' V₀ J₀ hℓ c0
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11⟩ := hP4
  have hQI : B.Q ∈ Ideal.span {(ℓ : A₀), B.X} := by
    have hQ' : B.Q = B.X + (B.p : A₀) := hQL
    rw [hQ', hp]
    exact Ideal.add_mem _ (Ideal.subset_span (by simp)) (Ideal.subset_span (by simp))
  have hφI : ∀ a ∈ Ideal.span {(ℓ : A₀), B.X}, B.φ a ∈ Ideal.span {(ℓ : A₀), B.X} := by
    intro a ha
    have : Ideal.span {(ℓ : A₀), B.X} ≤ (Ideal.span {(ℓ : A₀), B.X}).comap (B.φ : A₀ →+* A₀) := by
      rw [Ideal.span_le]
      rintro x (rfl | rfl)
      · show (B.φ : A₀ →+* A₀) (ℓ : A₀) ∈ Ideal.span {(ℓ : A₀), B.X}
        rw [map_natCast]
        exact Ideal.subset_span (by simp)
      · show B.φ B.X ∈ Ideal.span {(ℓ : A₀), B.X}
        obtain ⟨v, hv⟩ := B.φX
        rw [hv]
        exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))
    exact this ha
  exact ⟨hℓ2, A₀, inferInstance, inferInstance, B, M₀, u, H, jumps, c, D₀', D₁', D₂',
    inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance,
    V₀, V₁, V₂, Sq, δ, cl₁, cl₂, Ideal.span {(ℓ : A₀), B.X}, inferInstance,
    hp, hPhi, hGX, hval, hcc, hδ, hQI, hφI, l1, l3 hnt,
    x_kills_case_a ℓ A A₀ S B Δ IB ι pr D₀ D₁ D₂ W₀ W₁ W₂ E M h M₀ H ρ₁ ρ₂ D₁' D₂' V₁ V₂ Sq.π J₁ J₂ hℓ
      hs hR hD a0 a1 a2 b0 b1 b2 c0 c1 c2 hP6 hM hH hcard hΔ n1 hπ s2 hSπ,
    semilinear_case_a ℓ A₀ R B M₀ D₀' P V₀ δ u c jumps ρ κ L.t L.γR L.locA L.loc L.γl L.n L.a hGQ hδ p1 p2
      p3 p4 p5 p6 p7 p8 hcc p9 p10 p11 hj,
    hnat, hc1, hc2, hinj,
    extension_case_a ℓ A A₀ S B Δ IB ι pr D₁ W₁ M₀ D₁' V₁ H₁ cl₁ Hf₁ M h H hℓ hs hR hD a1 b1 c1 hM hH hcard
      hΔ (extension_nonlinear_holds ℓ A A₀ S B Δ IB ι pr D₁ W₁ ρ₁ M₀ D₁' V₁ J₁ H₁ cl₁ Hf₁ M h H hs hR hD a1 b1 c1 hM hH
      hcard hΔ hGQ hcap k1 he1),
    extension_case_a ℓ A A₀ S B Δ IB ι pr D₂ W₂ M₀ D₂' V₂ H₂ cl₂ Hf₂ M h H hℓ hs hR hD a2 b2 c2 hM hH hcard
      hΔ (extension_nonlinear_holds ℓ A A₀ S B Δ IB ι pr D₂ W₂ ρ₂ M₀ D₂' V₂ J₂ H₂ cl₂ Hf₂ M h H hs hR hD a2 b2 c2 hM hH
      hcard hΔ hGQ hcap k2 he2), hrat, he⟩

theorem source_two_cases_holds : SourceTwoCases := by
  intro ℓ _ H₁ H₂ _ _ _ _ Hf₁ Hf₂ g e hS
  rcases hS with hB | hA | ⟨K₁, K₂, i1, i2, i3, i4, Kf₁, Kf₂, h, res₂, cor₁, cor₂, n, E, k1, k2, k3, k4, k5, k6, k7⟩
  · exact Or.inl (srcNB ℓ H₁ H₂ Hf₁ Hf₂ g e hB)
  · exact Or.inr (Or.inl (srcNA ℓ H₁ H₂ Hf₁ Hf₂ g e hA))
  · exact Or.inr (Or.inr ⟨K₁, K₂, i1, i2, i3, i4, Kf₁, Kf₂, h, res₂, cor₁, cor₂, n, E, k1, k2, k3, k4, k5,
      k6.imp (srcNB ℓ K₁ K₂ Kf₁ Kf₂ h E) (srcNA ℓ K₁ K₂ Kf₁ Kf₂ h E), k7⟩)

theorem srcNO2 : StatSrcNO2 := by
  intro ℓ _ O _ _ H₁ H₂ _ _ _ _ _ _ _ _ Hf₁ Hf₂ g e' hS
  obtain ⟨e, he, h⟩ := hS
  exact ⟨e, he, source_two_cases_holds ℓ H₁ H₂ _ _ _ e h⟩

end Formalism.RepresentationBoundsCohomology.SplitClassesAll
