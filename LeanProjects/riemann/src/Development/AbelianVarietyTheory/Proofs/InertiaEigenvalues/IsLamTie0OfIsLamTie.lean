import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAuxiliaryHeckeCharacter

noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie

namespace GlobalTheory.LamTieWeak

variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

theorem isThEmpty_of_isThOf {i : X.Tw} {ι : ℂ →+* Kbar X i} {lam : X.abelian₂ i} {I : Type} [Fintype I] {φ : I → D.host.E →+* ℂ}
    {s : ℕ} {κ : I → ℕ} {𝔣 : Ideal (OF D.host.E)} {χ : Formalism.L2.Host.HChar D.host.E}
    (h : IsThOf X i ι lam φ s κ 𝔣 χ) : IsThEmpty X i ι lam φ s κ 𝔣 χ := by
  classical
  obtain ⟨u, hu, hth⟩ := h
  have hQ : BlochKatoReduction.Gen.QOk X i ∅ :=
    ⟨fun _ h => absurd h (Finset.notMem_empty _), Finset.disjoint_empty_left _, fun _ h => absurd h (Finset.notMem_empty _)⟩
  obtain ⟨hfin, π, T, -, hT, hδ⟩ := hth ∅ hQ
  have he : belowSet (∅ : Finset (HeightOneSpectrum (𝓞 D.host.E))) = ∅ := Finset.image_empty _
  have hc : condQ 𝔣 (belowSet (∅ : Finset (HeightOneSpectrum (𝓞 D.host.E)))) = 𝔣 := by
    rw [he]; simp [condQ]
  have := Fintype.ofFinite (PicO (condQ 𝔣 (belowSet (∅ : Finset (HeightOneSpectrum (𝓞 D.host.E))))))
  have t : IsToricSum φ s κ (condQ 𝔣 (belowSet (∅ : Finset (HeightOneSpectrum (𝓞 D.host.E))))) χ (∑ q, T q) :=
    (isToricSum_iff _ _ _ _ _ _).2 ⟨hfin, T, hT, (finsum_eq_sum_of_fintype _).symm⟩
  have key : ∀ z : ℂ, IsToricSum φ s κ (condQ 𝔣 (belowSet (∅ : Finset (HeightOneSpectrum (𝓞 D.host.E))))) χ z →
      IsToricSum φ s κ 𝔣 χ z := by
    rw [hc]; exact fun _ hz => hz
  refine ⟨u, ∑ q, T q, hu, key _ t, ?_⟩
  rw [map_sum, Finset.sum_congr rfl fun δ _ => hδ δ, ← Finset.mul_sum, ← map_sum,
    ← Finset.sum_fiberwise Finset.univ (fun q => π q⁻¹)]
  congr 2
  refine Finset.sum_congr rfl fun δ _ => ?_
  rw [show {q | π q⁻¹ = δ} = ↑(Finset.univ.filter fun q => π q⁻¹ = δ) by ext; simp, finsum_mem_coe_finset]

theorem isLamTie0_of_isLamTie : ∀ (D : D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (Z : LamDat D),
    IsLamTie X Z → IsLamTie0 X Z := by
  intro D N X Z h i hi lam
  obtain ⟨-, ι, -, hι⟩ := h i hi
  obtain ⟨j, a, s, hl, ht⟩ := hι lam
  exact ⟨_, j, a, s, hl.2.1, isThEmpty_of_isThOf ht⟩

end GlobalTheory.LamTieWeak
