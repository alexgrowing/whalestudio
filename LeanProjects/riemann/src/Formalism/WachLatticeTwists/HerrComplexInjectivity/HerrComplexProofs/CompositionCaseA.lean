import Formalism.WachLatticeTwists.HerrComplexInjectivity.ExtInputNA
import Formalism.WachLatticeTwists.HerrComplexInjectivity.HerrComplexProofs.RegulatorQuotientCaseA

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.JN

open Formalism.CoboundaryTransfers Formalism.RepresentationBoundsCohomology.N1 Formalism.RepresentationBoundsCohomology.N2

theorem extension_case_a : StatExtA := by
  intro ℓ _ A A₀ _ _ _ _ S B Δ _ _ _ IB ι _ pr D _ _ _ _ W M₀ D' _ _ _ _ V Hh _ _ cl Hf M h H hℓ hs hR
    hD hP2 hP5 hL hM hH hcard hΔ hE κ hκ
  obtain ⟨X, Dp, Dt, i1, i2, i3, i4, i5, i6, i7, i8, Wp, Wt, E, ρp, ρt, Jp, Jt, p2p, p2t, p5p, p5t,
    lp, lt, p6, -, -, ⟨d1, d2, d3⟩, hF, hdict⟩ := hE κ hκ
  exact ⟨X, x_kills_case_a ℓ A A₀ S B Δ IB ι pr D Dp Dt W Wp Wt E M h M₀ H ρp ρt X.Dp X.Dt X.Wp X.Wt
    X.S.π Jp Jt hℓ hs hR hD hP2 p2p p2t hP5 p5p p5t hL lp lt p6 hM hH hcard hΔ d1 d2 d3 hF, hdict⟩

theorem composition_case_a : StatCompA := by
  intro ℓ _ hℓ2 A A₀ _ _ _ _ S B Δ _ _ _ IB ι _ pr D₀ D₁ D₂ _ _ _ _ _ _ _ _ _ _ _ _ W₀ W₁ W₂ E M h M₀ H
    ρ₀ ρ₁ ρ₂ D₀' D₁' D₂' _ _ _ _ _ _ _ _ _ _ _ _ V₀ V₁ V₂ Sq J₀ J₁ J₂ u jumps δ R P ρ κ _ _ _ _ _ _ _ L
    H₁ H₂ _ _ _ _ cl₁ cl₂ Hf₁ Hf₂ g _ hℓ hs hc hu hR hD a0 a1 a2 b0 b1 b2 c0 c1 c2 hP6 hM hH hp hcard
    hΔ hmodπ hcap hreg hQL hdiv hjac _ _ _ hΔM hF hδ hnt hP4 hj hnat hc1 hc2 hinj he1 he2 hrat
  obtain ⟨-, -, -, -, -, -, -, q8, -, -⟩ := base_case_b ℓ A S hℓ
  have hval : PadicInt.valuation ((u : ℤ_[ℓ]) - 1) = 1 := by rw [hu, q8 hc, hs]
  obtain ⟨hPhi, hGX⟩ := base_case_a ℤ_[ℓ] A A₀ S B Δ IB hs hΔ hmodπ hcap hreg
  rw [hcard] at hPhi hGX
  rw [← hu] at hGX
  have hGQ := gamma_quotient_case_a ℤ_[ℓ] A₀ B hQL hdiv hjac
  obtain ⟨c, hcc, -, -⟩ := consequence_five_holds ℓ u hℓ2 hval
  obtain ⟨l1, l3⟩ := regulator_quotient_case_a ℓ A A₀ S B Δ IB ι pr D₀ W₀ ρ₀ M₀ D₀' V₀ J₀ hℓ c0
  obtain ⟨d1, d2, d3⟩ := hΔM
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
  exact lift_exists_first_case ℓ hℓ2 A₀ B M₀ u H jumps c hp hPhi hGX hval hcc D₀' D₁' D₂' V₀ V₁ V₂ Sq δ H₁ H₂ cl₁
    cl₂ Hf₁ Hf₂ g (Ideal.span {(ℓ : A₀), B.X}) hδ hQI hφI l1 (l3 hnt)
    (x_kills_case_a ℓ A A₀ S B Δ IB ι pr D₀ D₁ D₂ W₀ W₁ W₂ E M h M₀ H ρ₁ ρ₂ D₁' D₂' V₁ V₂ Sq.π J₁ J₂ hℓ
      hs hR hD a0 a1 a2 b0 b1 b2 c0 c1 c2 hP6 hM hH hcard hΔ d1 d2 d3 hF)
    (semilinear_case_a ℓ A₀ R B M₀ D₀' P V₀ δ u c jumps ρ κ L.t L.γR L.locA L.loc L.γl L.n L.a hGQ hδ p1 p2
      p3 p4 p5 p6 p7 p8 hcc p9 p10 p11 hj)
    hnat hc1 hc2 hinj
    (extension_case_a ℓ A A₀ S B Δ IB ι pr D₁ W₁ M₀ D₁' V₁ H₁ cl₁ Hf₁ M h H hℓ hs hR hD a1 b1 c1 hM hH hcard
      hΔ he1)
    (extension_case_a ℓ A A₀ S B Δ IB ι pr D₂ W₂ M₀ D₂' V₂ H₂ cl₂ Hf₂ M h H hℓ hs hR hD a2 b2 c2 hM hH hcard
      hΔ he2) hrat

end Formalism.RepresentationBoundsCohomology.JN
