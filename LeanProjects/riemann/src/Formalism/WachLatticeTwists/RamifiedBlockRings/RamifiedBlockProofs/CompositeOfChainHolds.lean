import Formalism.WachLatticeTwists.RamifiedBlockRings.RamifiedBlockProofs.TopLengthBoundViaSplitting
import Formalism.WachLatticeTwists.RamifiedBlockRings.RamifiedBlockProofs.LemmaFiveThreeExtensionOfModule

open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.ringDataObjects

open Formalism.NG Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities Formalism.RepresentationBoundsCohomology.BR

theorem freeImp : FreeImp := by
  intro O _ _ _ X X' T Z p d _ _ R' _ Tc _ _ _ _ G _ r χ E e₁ δ π' t ht bl ρk _ _ _ _ δO h ι _ _ colIdx hinj
    D j e' Kc k0 hoff g₀ n _ _
  exact h ι colIdx hinj D j e' Kc k0 hoff

theorem free_of_bound (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (X X' : Type)
    (T : Subalgebra O (X → O)) (T' : Subalgebra O (X' → O)) (Z : Set X) (p : X' → X) (q : ℕ)
    (b : Fin q → (X' → O)) (d : Type) [Fintype d] [DecidableEq d]
    (R' : Subalgebra O (X' → Matrix d d (FractionRing O))) [IsNoetherian R' R']
    (Tc : Type) [CommRing Tc] [Algebra Tc R'] [∀ x', Module Tc (EvalSp O d R' x')]
    [∀ x', IsScalarTower Tc R' (EvalSp O d R' x')]
    (G : Type) [Group G] (r : G →* R') (χ : G →* Tcˣ) (E e₁ : R') (δ : Tc)
    (π' : X') (ρπ : R' →ₐ[O] Matrix d d O) (t : ℕ) (ht : 1 ≤ t) (bl : d → Fin (t + 1))
    (ρk : ∀ k : Fin (t + 1), R' →ₐ[O] Matrix {a // bl a = k} {a // bl a = k} O)
    [∀ k, SMulCommClass R' O (blockRestrictedRepresentationType bl ρk k)] [∀ k, Module Tc (blockRestrictedRepresentationType bl ρk k)]
    [∀ k, IsScalarTower Tc R' (blockRestrictedRepresentationType bl ρk k)] [∀ k, IsScalarTower O R' (blockRestrictedRepresentationType bl ρk k)]
    (sE : Finset G) (tE : G → Tc) (δO : O)
    (hR : RingTop O X X' T T' p q b d R' Tc G r χ E e₁ δ π' ρπ t ht bl ρk sE tE δO)
    (hB : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (colIdx : ι → ℕ) (D : ℕ → Subgroup G) (j : ℕ → ℕ)
      (Kc : ∀ l, Fin (j (colIdx l)) → G → R') (k0 : ι → G → R'),
      (∀ x', p x' ∉ Z → ∃ φ : ColNNJ r χ E e₁ δ (fun l => D (colIdx l)) (fun l => j (colIdx l)) Kc k0 →ₗ[R']
        EvalSp O d R' x', φ ≠ 0) →
      vcc T Z (p π') ≤ ∑ k : Fin (t + 1), Module.length O
        (ColNNJ r χ E e₁ δ (fun l => D (colIdx l)) (fun l => j (colIdx l)) Kc k0 →ₗ[R'] blockRestrictedRepresentationType bl ρk k)) :
    LocalToDisplayFree O X X' T Z p d R' Tc G r χ E e₁ δ π' t ht bl ρk δO := by
  obtain ⟨ha, hb, hc, hEE, hee, hpts, hρπ, hbl, hsurj, hblk, hcard1, hEsum, hE0, hδ0, hτ0, hne, hC,
    hOne⟩ := hR
  intro ι _ _ colIdx hinj D j e' Kc k0 hoff ℓ cB what₂ qs deg s vhE H0 Sha hk0
    cols eO vδ N h0 L _ _ _ tens v₁ κ HcG Hc F Vo VS Io IS ε T₁ T₂ _ _ _ _ ρ₁ ρ₂ inc π γ lam Cs _ _
    cls pr Fs Im cT I γQ ζ ζO nQ u hIn0 hInC hIn1
  refine top_length_bound_via_splitting O X X' T T' Z p q b ha (fun x _ => hb x) d R' hc Tc G r χ E e₁ δ ι colIdx hinj
    D j e' Kc k0 hEE hee ?_ π' ρπ hρπ t ht bl hbl ρk hsurj hblk ?_ hcard1
    sE tE δO ℓ cB what₂ qs deg s vhE H0 Sha hEsum hk0
    L tens v₁ κ HcG Hc F Vo VS Io IS ε T₁ T₂ ρ₁ ρ₂ inc π γ lam Cs cls pr Fs Im
    cT I γQ ζ ζO nQ u hE0 hδ0 hτ0 hne hIn0 ?_ ?_
  · intro x' hx'
    obtain ⟨δx, h1, h2, h3, h4⟩ := hpts x'
    exact ⟨δx, h1, h2, h3, h4, (hoff x' hx').1, (hoff x' hx').2⟩
  · refine hB ι colIdx D j Kc k0 fun x' hx' => ?_
    obtain ⟨δx, h1, h2, h3, h4⟩ := hpts x'
    exact columnJ R' Tc (FractionRing O) (EvalSp O d R' x') G r χ E e₁ δ ι (fun l => D (colIdx l))
      (fun l => j (colIdx l)) Kc k0 hEE hee δx h1 h2 h3 h4 (hoff x' hx').1 (hoff x' hx').2
  · intro c hc2
    obtain ⟨h1, h2, h3, h4⟩ := hC c hc2
    exact ⟨h1, h2, h3, h4, (hInC c hc2).1, (hInC c hc2).2⟩
  · obtain ⟨h1, h2, h3, h4⟩ := hOne
    exact ⟨h1, h2, h3, h4, hIn1⟩

theorem displayFree (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (X : Type) [Fintype X]
    (T : Subalgebra O (X → O)) (d : Type) [Fintype d] [DecidableEq d] (G : Type) [Group G]
    (r₀ : G →* (X → Matrix d d O)) (π : X) (t : ℕ) (ht : 1 ≤ t) (bl : d → Fin (t + 1)) (χ₁ ε : G →* Oˣ)
    (hP : PrimHyp O T r₀ π bl χ₁ ε)
    (hA : AbsIrr (fun g => ((r₀ g π).toSquareBlock bl 0).map (IsLocalRing.residue O)))
    (eB e₁ : X → Matrix d d O) (hI : IdemHyp O T r₀ π bl eB e₁) (g₀ : G) (s : X → Matrix d d O)
    (hX : DistinctEigenvalueCornerPerturbation O T r₀ π t g₀ eB s) (D : RingData O X d G t bl)
    (hD : RingDef O T r₀ π χ₁ ε g₀ eB e₁ s D) [IsNoetherian D.R' D.R']
    [∀ x', IsScalarTower D.T' D.R' (EvalSp O d D.R' x')] [∀ k, SMulCommClass D.R' O (blockRestrictedRepresentationType bl D.ρk k)]
    [∀ k, IsScalarTower D.T' D.R' (blockRestrictedRepresentationType bl D.ρk k)] [∀ k, IsScalarTower O D.R' (blockRestrictedRepresentationType bl D.ρk k)]
    (hT : D.Top T ht) (Z : Set X) :
    LocalToDisplayFree O X D.X' T Z D.p d D.R' D.T' G D.r D.χ D.E D.e₁ D.δ D.π' t ht bl D.ρk D.δO := by
  have hpπ : D.p D.π' = π := by
    obtain ⟨-, -, -, -, h, -⟩ := hD
    exact h
  refine free_of_bound O X D.X' T D.T' Z D.p D.q D.b d D.R' D.T' G D.r D.χ D.E D.e₁ D.δ D.π' D.ρπ t ht bl
    D.ρk D.sE D.tE D.δO hT fun ι _ _ colIdx Dd j Kc k0 hφ => ?_
  obtain ⟨g, n, hn⟩ := Module.Finite.exists_fin (R := D.R')
    (M := ColNNJ D.r D.χ D.E D.e₁ D.δ (fun l => Dd (colIdx l)) (fun l => j (colIdx l)) Kc k0)
  rw [hpπ]
  exact lemma_five_three_any_residue_field O X d G t ht bl T r₀ π χ₁ ε g₀ eB e₁ s hP hA hI hX D hD Z _ g n hn hφ

theorem composite_of_chain_holds : CompositeOfChain := by
  intro O _ _ _ X _ T d _ _ G _ r₀ π t ht bl χ₁ ε hP hA eB e₁ hI g₀ s hX
  obtain ⟨D, hD, ⟨i1, i2, i3, i4, i5⟩, _, hT⟩ :=
    ring_objects_exist O X T d G r₀ π t ht bl χ₁ ε hP hA eB e₁ hI g₀ s hX
  exact ⟨D, hD, i1, i2, i3, i4, i5, fun Z =>
    displayFree O X T d G r₀ π t ht bl χ₁ ε hP hA eB e₁ hI g₀ s hX D hD hT Z⟩

end Formalism.RepresentationBoundsCohomology.ringDataObjects
