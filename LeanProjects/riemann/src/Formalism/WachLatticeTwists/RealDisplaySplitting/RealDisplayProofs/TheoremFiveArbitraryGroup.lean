import Formalism.WachLatticeTwists.RealDisplaySplitting.SplittingTheoremArbitraryGroup
import Formalism.WachLatticeTwists.RealDisplaySplitting.RealDisplayProofs.SplitF
import Formalism.WachLatticeTwists.RealDisplaySplitting.RealDisplayProofs.IdempotentRankOneAtPoint

open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.SF

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic Formalism.RepresentationBoundsCohomology.JL Formalism.RepresentationBoundsCohomology.JT Formalism.RepresentationBoundsCohomology.JS Formalism.RepresentationBoundsCohomology.SplitClassesAll

set_option maxHeartbeats 4000000 in
theorem absDisplayAll_of (ℓ : ℕ) [Fact ℓ.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra ℤ_[ℓ] O] (X X' : Type)
    (Z : Set X) (p : X' → X)
    (d : Type) [Fintype d] [DecidableEq d] (R' : Subalgebra O (X' → Matrix d d (FractionRing O)))
    [IsNoetherian R' R']
    (Tc : Type) [CommRing Tc] [Algebra Tc R'] [∀ x', Module Tc (EvalSp O d R' x')]
    [∀ x', IsScalarTower Tc R' (EvalSp O d R' x')]
    (G : Type) [Group G] (r : G →* R') (χ : G →* Tcˣ) (E e₁ : R') (δ : Tc)
    (t : ℕ) (ht : 1 ≤ t) (bl : d → Fin (t + 1))
    (ρk : ∀ k : Fin (t + 1), R' →ₐ[O] Matrix {a // bl a = k} {a // bl a = k} O)
    [∀ k, SMulCommClass R' O (blockRestrictedRepresentationType bl ρk k)] [∀ k, Module Tc (blockRestrictedRepresentationType bl ρk k)]
    [∀ k, IsScalarTower Tc R' (blockRestrictedRepresentationType bl ρk k)] [∀ k, IsScalarTower O R' (blockRestrictedRepresentationType bl ρk k)]
    (δO : O) (ε : G →* Oˣ) (gI : G) (lhs : ℕ∞)
    (T : Subalgebra O (X → O)) (T' : Subalgebra O (X' → O)) (q : ℕ) (b : Fin q → (X' → O)) (π' : X')
    (ρπ : R' →ₐ[O] Matrix d d O) (sE : Finset G) (tE : G → Tc) (rr : ℕ → Tc) (u₁ : Oˣ)
    (hR : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingTop O X X' T T' p q b d R' Tc G r χ E e₁ δ π' ρπ t ht bl ρk sE tE δO)
    (hF : Formalism.RepresentationBoundsCohomology.ringDataObjects.LocalToDisplayFree O X X' T Z p d R' Tc G r χ E e₁ δ π' t ht bl ρk δO)
    (hδ : δ = ∏ i ∈ Finset.Ioo 0 t, (rr 0 - rr i))
    (hδO : δO = ∏ i ∈ Finset.Ioo 0 t, ((u₁ : O) - (u₁ : O) * (((ε gI)⁻¹ ^ i : Oˣ) : O)))
    (hrr : ∀ (c : Fin (t + 1)) (i : ℕ), i < t → ∀ m : blockRestrictedRepresentationType bl ρk c,
      rr i • m = ((u₁ : O) * (((ε gI)⁻¹ ^ i : Oˣ) : O)) • m)
    (hl : lhs = vcc T Z (p π')) :
    AbsDisplayAll ℓ O X X' Z p d R' Tc G r χ E e₁ δ t ht bl ρk δO ε gI lhs := by
  obtain ⟨ha, hb, hc, hEE, hee, hpts, hρπ, hbl, hsurj, hblk, hcard1, hEsum, hE0, hδ0, hτ0, hne, hC0,
    hOne0⟩ := hR
  obtain ⟨p1, p2, p3, -⟩ := hOne0
  subst hl
  intro ι _ _ colIdx hinj D j e' what₂ qs deg s vhE H0 Sha uT wT sT mT dT UT cols eO cB vδ N h0 c1
    L _ _ _ _ _ _ tens v₁ κ V _ _ _ _ _ _ iL qV Ff κz HcG Hc F Vo VS Io IS T₁ T₂ _ _ _ _ ρ₁ ρ₂ inc π
    γ lam Cs _ _ cls pr Fs Im I γQ ζ ζO nQ u s₀ y HW HV₂ _ _ _ _ _ _ _ _ qW jT pairW HfW Hf₂
    Pe _ _ _ _ _ _ ince eve heve PE _ _ _ _ _ _ incE evE hevE Hfe₁ HfE₁ HfE₂ uz
    hnu hs1 hs2 hε hse hsE hincE hact huz hu hLe hLE hrat0 hFix hBK hC hOne hrest
  exact realization_all_forms_holds ℓ O X X' T T' Z p q b ha (fun x _ => hb x) d R' hc Tc G r χ E e₁ δ ι colIdx hinj
    D j e' hEE hee π' ρπ hρπ t ht bl hbl ρk hsurj hblk hcard1 sE tE δO what₂ qs deg s vhE H0
    Sha uT wT sT mT dT UT hEsum hF L tens v₁ κ V iL qV Ff κz HcG Hc F Vo VS Io IS ε T₁ T₂ ρ₁ ρ₂ inc π
    γ lam Cs cls pr Fs Im I γQ ζ ζO nQ u rr gI s₀ u₁ y HW HV₂ qW jT pairW HfW Hf₂
    Pe ince eve heve PE incE evE hevE Hfe₁ HfE₁ HfE₂ uz
    hnu hs1 hs2 hε hδ hδO hrr hse hsE hincE hact huz hu hLe hLE
    (fun x' hx' => by
      obtain ⟨δx, q1, q2, q3, q4⟩ := hpts x'
      exact ⟨δx, q1, q2, q3, q4, (hrat0 x' hx').1, (hrat0 x' hx').2⟩)
    hE0 hτ0 hne hFix hBK
    (fun c hc2 => ⟨(hC0 c hc2).1, (hC0 c hc2).2.1, (hC0 c hc2).2.2.2, hC c hc2⟩)
    ⟨p1, p2, p3, hOne⟩ hrest

set_option maxHeartbeats 4000000 in
theorem absDisplaySplit2_of (ℓ : ℕ) [Fact ℓ.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra ℤ_[ℓ] O] (X X' : Type)
    (Z : Set X) (p : X' → X)
    (d : Type) [Fintype d] [DecidableEq d] (R' : Subalgebra O (X' → Matrix d d (FractionRing O)))
    [IsNoetherian R' R']
    (Tc : Type) [CommRing Tc] [Algebra Tc R'] [∀ x', Module Tc (EvalSp O d R' x')]
    [∀ x', IsScalarTower Tc R' (EvalSp O d R' x')]
    (G : Type) [Group G] (r : G →* R') (χ : G →* Tcˣ) (E e₁ : R') (δ : Tc)
    (t : ℕ) (ht : 1 ≤ t) (bl : d → Fin (t + 1))
    (ρk : ∀ k : Fin (t + 1), R' →ₐ[O] Matrix {a // bl a = k} {a // bl a = k} O)
    [∀ k, SMulCommClass R' O (blockRestrictedRepresentationType bl ρk k)] [∀ k, Module Tc (blockRestrictedRepresentationType bl ρk k)]
    [∀ k, IsScalarTower Tc R' (blockRestrictedRepresentationType bl ρk k)] [∀ k, IsScalarTower O R' (blockRestrictedRepresentationType bl ρk k)]
    (δO : O) (ε : G →* Oˣ) (gI : G) (lhs : ℕ∞)
    (T : Subalgebra O (X → O)) (T' : Subalgebra O (X' → O)) (q : ℕ) (b : Fin q → (X' → O)) (π' : X')
    (ρπ : R' →ₐ[O] Matrix d d O) (sE : Finset G) (tE : G → Tc) (rr : ℕ → Tc) (u₁ : Oˣ)
    (hR : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingTop O X X' T T' p q b d R' Tc G r χ E e₁ δ π' ρπ t ht bl ρk sE tE δO)
    (hF : Formalism.RepresentationBoundsCohomology.ringDataObjects.LocalToDisplayFree O X X' T Z p d R' Tc G r χ E e₁ δ π' t ht bl ρk δO)
    (hδ : δ = ∏ i ∈ Finset.Ioo 0 t, (rr 0 - rr i))
    (hδO : δO = ∏ i ∈ Finset.Ioo 0 t, ((u₁ : O) - (u₁ : O) * (((ε gI)⁻¹ ^ i : Oˣ) : O)))
    (hrr : ∀ (c : Fin (t + 1)) (i : ℕ), i < t → ∀ m : blockRestrictedRepresentationType bl ρk c,
      rr i • m = ((u₁ : O) * (((ε gI)⁻¹ ^ i : Oˣ) : O)) • m)
    (hl : lhs = vcc T Z (p π')) :
    AbsDisplaySplit2 ℓ O X X' Z p d R' Tc G r χ E e₁ δ t ht bl ρk δO ε gI lhs := by
  obtain ⟨ha, hb, hc, hEE, hee, hpts, hρπ, hbl, hsurj, hblk, hcard1, hEsum, hE0, hδ0, hτ0, hne, hC0,
    hOne0⟩ := hR
  obtain ⟨p1, p2, p3, -⟩ := hOne0
  subst hl
  intro ι _ _ colIdx hinj D j e' what₂ qs deg s vhE H0 Sha uT wT sT mT dT UT cols eO cB vδ N h0 c1
    L _ _ _ _ _ _ tens v₁ κ V _ _ _ _ _ _ iL qV Ff κz HcG Hc F Vo VS Io IS T₁ T₂ _ _ _ _ ρ₁ ρ₂ inc π
    γ lam Cs _ _ _ _ cls pr Fs Im I γQ ζ ζO nQ u s₀ y HW HV₂ _ _ _ _ _ _ _ _ qW jT pairW HfW Hf₂
    Pe _ _ _ _ _ _ ince eve heve PE _ _ _ _ _ _ incE evE hevE Hfe₁ HfE₁ HfE₂ uz
    hnu hs1 hs2 hε hse hsE hincE hact huz hu hLe hLE hrat0 hFix hBK hC hOne hrest
    conj nlam m cloudC lowsC cloudR lowsR h0C h0R V₂ _ _ _ _ ρV ρA iV qA Zc clsV H₁ _ _ _ _ Hf₁ gR
    τH DatH bH wH mH hrows hseq hcls hclsV hliftR hH0 hJC hJR
  exact split_all_second_form ℓ O X X' T T' Z p q b ha (fun x _ => hb x) d R' hc Tc G r χ E e₁ δ ι colIdx hinj
    D j e' hEE hee π' ρπ hρπ t ht bl hbl ρk hsurj hblk hcard1 sE tE δO what₂ qs deg s vhE H0
    Sha uT wT sT mT dT UT hEsum hF L tens v₁ κ V iL qV Ff κz HcG Hc F Vo VS Io IS ε T₁ T₂ ρ₁ ρ₂ inc π
    γ lam Cs cls pr Fs Im I γQ ζ ζO nQ u rr gI s₀ u₁ y HW HV₂ qW jT pairW HfW Hf₂
    Pe ince eve heve PE incE evE hevE Hfe₁ HfE₁ HfE₂ uz
    hnu hs1 hs2 hε hδ hδO hrr hse hsE hincE hact huz hu hLe hLE
    (fun x' hx' => by
      obtain ⟨δx, q1, q2, q3, q4⟩ := hpts x'
      exact ⟨δx, q1, q2, q3, q4, (hrat0 x' hx').1, (hrat0 x' hx').2⟩)
    hE0 hτ0 hne hFix hBK
    (fun c hc2 => ⟨(hC0 c hc2).1, (hC0 c hc2).2.1, (hC0 c hc2).2.2.2, hC c hc2⟩)
    ⟨p1, p2, p3, hOne⟩ hrest
    conj nlam m cloudC lowsC cloudR lowsR h0C h0R V₂ ρV ρA iV qA Zc clsV H₁ Hf₁ gR
    τH DatH bH wH mH hrows hseq hcls hclsV hliftR hH0 hJC hJR

open Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities Formalism.RepresentationBoundsCohomology.ringDataObjects in
set_option maxHeartbeats 4000000 in
theorem theorem_five_arbitrary_group : SplittingTheoremArbitraryGroup := by
  intro ℓ _ O _ _ _ _ X _ T d _ _ G _ r π t ht bl χ₁ ε g₀ hyp L ϖ hϖ
  obtain ⟨eB, e₁, s, hAB, hall⟩ := chain_from_primitive_data O X T d G r π t ht bl χ₁ ε g₀ hyp L ϖ hϖ
  refine ⟨eB, e₁, s, hAB, ?_⟩
  intro O' _ _ _ _ _ _ e he hspl
  obtain ⟨D, hD, ⟨i1, i2, i3, i4, i5, hT, hFree⟩, hv⟩ := hall O' e he hspl
  obtain ⟨hd1, hd2⟩ := deltaBc O O' e he
  refine ⟨D, hD, hd2 ℓ, (hd1 X d G t bl T r π χ₁ ε g₀ eB e₁ s D hD).2, i1, i2, i3, i4, i5, ?_⟩
  intro _ Z
  have hδO := deltaO_eq hD
  have hrr := rr_act hD
  exact ⟨absDisplayAll_of ℓ O' X D.X' Z D.p d D.R' D.T' G D.r D.χ D.E D.e₁ D.δ t ht bl D.ρk D.δO
      (bcChar O' ε) g₀ _ (bcT O' T) D.T' D.q D.b D.π' D.ρπ D.sE D.tE D.rr (bcChar O' χ₁ g₀) hT (hFree Z) rfl hδO
      hrr (hv Z).symm,
    absDisplaySplit2_of ℓ O' X D.X' Z D.p d D.R' D.T' G D.r D.χ D.E D.e₁ D.δ t ht bl D.ρk D.δO
      (bcChar O' ε) g₀ _ (bcT O' T) D.T' D.q D.b D.π' D.ρπ D.sE D.tE D.rr (bcChar O' χ₁ g₀) hT (hFree Z) rfl hδO
      hrr (hv Z).symm⟩

end Formalism.RepresentationBoundsCohomology.SF
