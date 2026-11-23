import Formalism.WachLatticeTwists.RealDisplaySplitting.RealDisplayProofs.RealDisplayAllWAOf
import Formalism.WachLatticeTwists.RealDisplaySplitting.RealDisplayProofs.IdempotentRankOneAtPoint

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.SF

open Formalism.NG Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.ringDataObjects

set_option maxHeartbeats 4000000 in
theorem galois_theorem_primitive_data : GaloisTheoremPrimitiveData := by
  intro ℓ _ O _ _ _ _ X _ T d _ _ Ek Ω _ _ _ _ _ r π t ht bl χ₁ ε g₀ hyp L ϖ hϖ
  obtain ⟨eB, e₁, s, hAB, hall⟩ := chain_from_primitive_data O X T d (Ω ≃ₐ[Ek] Ω) r π t ht bl χ₁ ε g₀ hyp L ϖ hϖ
  refine ⟨eB, e₁, s, hAB, ?_⟩
  intro O' _ _ _ _ _ _ e he hspl
  obtain ⟨D, hD, ⟨i1, i2, i3, i4, i5, hT, hFree⟩, hv⟩ := hall O' e he hspl
  obtain ⟨hP, hA, -, -, -⟩ := hyp
  obtain ⟨hI, ⟨m, jj, a, hja, hs⟩, hsep⟩ := hAB
  obtain ⟨b1, b2, b3, b4⟩ := bridge O X T d (Ω ≃ₐ[Ek] Ω) r π eB hI.1 hI.2.2.1 m jj a hja (ϖ ^ L)
  rw [← hs] at b1 b2 b3 b4
  obtain ⟨cP, -, cI, -, -⟩ := stageC O O' e he X T d (Ω ≃ₐ[Ek] Ω) r π t bl χ₁ ε hP hA eB e₁ hI g₀ s b1 b2 b3 b4
    hsep hspl
  obtain ⟨hd1, hd2⟩ := deltaBc O O' e he
  have hT' := hT
  obtain ⟨-, -, -, -, hee, -, -, -, hsurj, -, hcard1, -, -, -, -, -, -, hOne0⟩ := hT'
  obtain ⟨-, -, p3, -⟩ := hOne0
  refine ⟨D, hD, hd2 ℓ, (hd1 X d (Ω ≃ₐ[Ek] Ω) t bl T r π χ₁ ε g₀ eB e₁ s D hD).2,
    surjection_of_rank_one_idempotent O' D.R' _ (D.ρk 0).toRingHom D.e₁ (hsurj 0) hee (idempotent_rank_one_at_point cI hD),
    scalar_action_on_block O' D.R' _ D.E D.δO p3 (blk_scalar D _ (hcard1 _ (by
      intro h
      have := congrArg Fin.val h
      simp at this))), i1, i2, i3, i4, i5, ?_⟩
  intro _ _ _ _ _ _ _ _ _ _ Z
  have hδO := deltaO_eq hD
  have hrr := rr_act hD
  have hba := blk_act cP hD
  exact ⟨realDisplay2_of ℓ O' X D.X' Z D.p d D.R' D.T' Ek Ω D.r D.χ D.E D.e₁ D.δ t ht bl D.ρk D.δO
      (bcChar O' ε) g₀ _ (bcT O' T) D.T' D.q D.b D.π' D.ρπ D.sE D.tE D.rr (bcChar O' χ₁ g₀) hT (hFree Z) rfl hδO
      hrr hba (hv Z).symm,
    realDisplayWA_of ℓ O' X D.X' Z D.p d D.R' D.T' Ek Ω D.r D.χ D.E D.e₁ D.δ t ht bl D.ρk D.δO
      (bcChar O' ε) g₀ _ (bcT O' T) D.T' D.q D.b D.π' D.ρπ D.sE D.tE D.rr (bcChar O' χ₁ g₀) hT (hFree Z) rfl hδO
      hrr hba (hv Z).symm,
    realDisplayAll2_of ℓ O' X D.X' Z D.p d D.R' D.T' Ek Ω D.r D.χ D.E D.e₁ D.δ t ht bl D.ρk D.δO
      (bcChar O' ε) g₀ _ (bcT O' T) D.T' D.q D.b D.π' D.ρπ D.sE D.tE D.rr (bcChar O' χ₁ g₀) hT (hFree Z) rfl hδO
      hrr hba (hv Z).symm,
    realDisplayAllWA_of ℓ O' X D.X' Z D.p d D.R' D.T' Ek Ω D.r D.χ D.E D.e₁ D.δ t ht bl D.ρk D.δO
      (bcChar O' ε) g₀ _ (bcT O' T) D.T' D.q D.b D.π' D.ρπ D.sE D.tE D.rr (bcChar O' χ₁ g₀) hT (hFree Z) rfl hδO
      hrr hba (hv Z).symm⟩

theorem galois_theorem_with_extension : GaloisTheoremWithExtension := by
  intro ℓ _ O _ _ _ _ X _ T d _ _ Ek Ω _ _ _ _ _ r π t ht bl χ₁ ε g₀ hyp L ϖ hϖ
  obtain ⟨eB, e₁, s, hAB, hall⟩ := galois_theorem_primitive_data ℓ O X T d Ek Ω r π t ht bl χ₁ ε g₀ hyp L ϖ hϖ
  refine ⟨eB, e₁, s, hAB, ?_⟩
  obtain ⟨hI, ⟨m, jj, a, hja, hs⟩, hsep⟩ := hAB
  obtain ⟨-, b2, b3, -⟩ := bridge O X T d (Ω ≃ₐ[Ek] Ω) r π eB hI.1 hI.2.2.1 m jj a hja (ϖ ^ L)
  rw [← hs] at b2 b3
  let ι : O →+* FractionRing O := algebraMap O (FractionRing O)
  have hι : Function.Injective ι := IsFractionRing.injective O (FractionRing O)
  have hmon : ∀ x, (blockPoly (eB x) (eB x * r g₀ x * eB x + s x)).Monic := by
    intro x
    have hbb : eB x * eB x = eB x := congrFun hI.2.2.1 x
    have hbs : eB x * s x = s x := congrFun b2 x
    have hsb : s x * eB x = s x := congrFun b3 x
    refine Polynomial.monic_of_injective hι ?_
    rw [blockPoly_map]
    refine (bcSplit (FractionRing O) d _ _ t ?_ ?_ ?_ (hI.2.2.2.2.2.2.1 x)).1
    · rw [← Matrix.map_mul, hbb]
    · rw [← Matrix.map_mul, mul_add, ← mul_assoc, ← mul_assoc, hbb, hbs]
    · rw [← Matrix.map_mul, add_mul, mul_assoc, hbb, hsb]
  obtain ⟨O', i1, i2, i3, i4, i5, i6, e, he, hspl⟩ := splitExt O X
    (fun x => blockPoly (eB x) (eB x * r g₀ x * eB x + s x)) hmon
    (fun x => by rw [blockPoly_map]; exact hsep x)
  exact ⟨O', i1, i2, i3, i4, i5, i6, e, he, hall O' e he hspl⟩

end Formalism.RepresentationBoundsCohomology.SF
