import Formalism.WachLatticeTwists.SplitClassesAll.StatSrcNB
import Formalism.WachLatticeTwists.HerrComplexInjectivity.HerrComplexProofs.ShortExactSequenceHolds

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.SplitClassesAll

open Formalism.CoboundaryTransfers Formalism.RepresentationBoundsCohomology.N1 Formalism.RepresentationBoundsCohomology.N2 Formalism.RepresentationBoundsCohomology.JL Formalism.RepresentationBoundsCohomology.JN

theorem srcNB : StatSrcNB := by
  intro ℓ _ H₁ H₂ _ _ _ _ Hf₁ Hf₂ g e hS
  obtain ⟨A, _, _, S, ι, _, pr, D₀, D₁, D₂, _, _, _, _, _, _, _, _, _, _, _, _, W₀, W₁, W₂, E, M, h, M₀, H, u,
    jumps, R, P, ρ, κ, _, _, _, _, _, _, _, L, _, hℓ, hc, hu, hR, hD, a0, a1, a2, b0, b1, b2, c0, c1, c2, hP6,
    hM, hH, hreg, hnt, hP4, hT, hj, hGal, hrat, he⟩ := hS
  obtain ⟨V₀, V₁, V₂, Sq, v0, v1, v2, hi, hp, hX⟩ := short_exact_sequence_holds ℤ_[ℓ] A S ι pr D₀ D₁ D₂ W₀ W₁ W₂ E M h
    M₀ H hR hD a0 a1 a2 b0 b1 b2 c0 c1 c2 hP6 hM hH
  obtain ⟨cl₁, cl₂, hnat, hc1, hc2, hinj, he1, he2⟩ := hGal V₀ V₁ V₂ Sq v0 v1 v2 hi hp
  obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8, q9, q10⟩ := base_case_b ℓ A S hℓ
  obtain ⟨l1, l2, l3⟩ := wach_lattice_holds ℓ A S ι pr D₀ W₀ M₀ V₀ hℓ v0
  have hcomp : IsAdicComplete (mI S) V₀.N := by rw [v0.1]; infer_instance
  exact ⟨A, inferInstance, inferInstance, S.base, M₀, u, S.s, H, jumps, (ι → D₀), (ι → D₁), (ι → D₂),
    inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance,
    V₀, V₁, V₂, Sq, cl₁, cl₂, mI S, hcomp, q1, q2, hu ▸ q3, q4 hR, q5, q6,
    (by rw [hu]; exact q8 hc), q9, q10, l2 hreg, l1 c0, l3 hnt, hX,
    semilinear_case_b ℓ A S ι pr D₀ W₀ M₀ V₀ R P ρ κ L u jumps hR v0 hP4 hT hj, hnat, hc1, hc2, hinj,
    extension_holds ℓ A S ι pr D₁ W₁ M₀ V₁ H₁ cl₁ Hf₁ M h H hR hD v1 a1 b1 c1 hM hH he1,
    extension_holds ℓ A S ι pr D₂ W₂ M₀ V₂ H₂ cl₂ Hf₂ M h H hR hD v2 a2 b2 c2 hM hH he2, hrat, he⟩

end Formalism.RepresentationBoundsCohomology.SplitClassesAll
