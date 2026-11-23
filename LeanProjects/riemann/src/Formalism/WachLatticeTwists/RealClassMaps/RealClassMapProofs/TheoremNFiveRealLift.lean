import Formalism.WachLatticeTwists.RealClassMaps.RealClassMapLift
import Formalism.WachLatticeTwists.RealClassMaps.RealClassMapProofs.TheoremNFiveRealSecond
import Formalism.WachLatticeTwists.SplitClassesAll.SplitClassesProofs.SourceCaseBSpecialHolds
import Formalism.WachLatticeTwists.SplitClassesAll.SplitClassesProofs.WFromFirstPredicates

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.FIN

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic Formalism.RepresentationBoundsCohomology.JL Formalism.RepresentationBoundsCohomology.JT Formalism.RepresentationBoundsCohomology.JS Formalism.RepresentationBoundsCohomology.SplitClassesAll Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology Formalism.RepresentationBoundsCohomology.T2
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC
open ReciprocityTheory.ChartRestriction.T2 (PadicCoeff FracTop IsFGTop cupFG IsCycOn)

theorem row_tb_of_w {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {A T' G : Type} [Ring A] [Algebra O A] [CommRing T'] [Algebra T' A] [Group G]
    (ℓ : ℕ) [Fact ℓ.Prime] (M : Type) [AddCommGroup M] [Module A M] [Module O M]
    [SMulCommClass A O M] (r : G →* A) (χ : G →* T'ˣ) (E : A) (Dw : Subgroup G)
    (F : Submodule O (H1z (resRep (uRep O (M := M) r χ) Dw)))
    (u w : ℤ_[ℓ]ˣ) (s m e d : ℕ) (U : Finset ℤ) (h : RowTBW ℓ M r χ E Dw F u w s m e d U) :
    RowTB ℓ M r χ E Dw F u w s m e d U := by
  intro ψ hψ z hz
  obtain ⟨B, hB⟩ := h ψ hψ z hz
  exact ⟨B, tbWIn ℓ B.D u w s m e d U hB⟩

set_option maxHeartbeats 8000000 in
theorem theorem_n_five_real_lift : RealClassMapLift := by
  intro ℓ _ O _ _ _ _ _ _ _ _ _ X X' T T' Z p q b h1 h2 d _ _ R' _ _ _ _ _ hdet Tc _ _ _ _ Ek Ω _ _ _ _ _
    r χ E e₁ δ ι _ _ colIdx hinj
    Aw pl Av j e' hE2 he1 π' ρπ hρπ t ht bl hbl ρk hsurj hblk _ _ _ _ hcard1 sE tE δO what₂ qs s H0
    Sha uT wT sT mT dT UT hEsum cols eO cB vδ N h0 c1
    L _ _ _ _ _ _ tens v₁ κ V _ _ _ _ _ _ iL qV Ff κz F Vo VS Io IS ε T₁ T₂ _ _ _ _ _ _ _ ρ₁ ρ₂ inc π
    γ lam VT VT' _ _ _ _ _ _ _ _ _ _ _ _ _ _ Dat uD huD vD hpD heD _ _ _ _ Fs Hf₁ I γQ ζ ζO nQ u rr gI s₀ u₁ y
    _ _ _ _ HfW Hf₂ gR Im
    Pe _ _ _ _ _ _ ince eve heve PE _ _ _ _ _ _ incE evE hevE Hfe₁ HfE₁ HfE₂ uz
    hinjO hO hFr hA hcyc hinc hur hAv hreal hs1 hs2 hε hδ hδO hrr hse hsE hincE hact huz hu hLe hLE hrat0 hb1 hb3 hb4
    hFix hRows hC hOne hrest
    conj nlam m cloudC lowsC cloudR lowsR h0C h0R V₂ _ _ _ _ ρV ρA iV qA wD
    τH DatH bH wH mH hrows hseq hwD hliftR hH0 hJC hJR
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8⟩ := hOne
  exact theorem_n_five_real_second ℓ O X X' T T' Z p q b h1 h2 d R' hdet Tc Ek Ω r χ E e₁ δ ι colIdx hinj Aw pl Av j e' hE2 he1
    π' ρπ hρπ t ht bl hbl ρk hsurj hblk hcard1 sE tE δO what₂ qs s H0 Sha uT wT sT mT dT UT hEsum
    L tens v₁ κ V iL qV Ff κz F Vo VS Io IS ε T₁ T₂ ρ₁ ρ₂ inc π
    γ lam VT VT' Dat uD huD vD hpD heD Fs Hf₁ I γQ ζ ζO nQ u rr gI s₀ u₁ y HfW Hf₂
    Pe ince eve heve PE incE evE hevE Hfe₁ HfE₁ HfE₂ uz
    hinjO hO hFr hA hcyc hinc hur hAv hreal hs1 hs2 hε hδ hδO hrr hse hsE hincE hact huz hu
    (fun l => srcNO2 ℓ O _ _ _ _ _ _ (hLe l)) (fun l => srcNO2 ℓ O _ _ _ _ _ _ (hLE l)) hrat0 hb1 hb3 hb4
    hFix hRows
    (fun c hc => ⟨(hC c hc).1, (hC c hc).2.1, (hC c hc).2.2.1, (hC c hc).2.2.2.1,
      fun w hw => ⟨((hC c hc).2.2.2.2.1 w hw).1, ((hC c hc).2.2.2.2.1 w hw).2.1,
        row_tb_of_w ℓ _ r χ E _ _ _ _ _ _ _ _ _ ((hC c hc).2.2.2.2.1 w hw).2.2⟩, (hC c hc).2.2.2.2.2⟩)
    ⟨o1, o2, o3, o4, o5, o6, fun w hw => ⟨(o7 w hw).1, row_tb_of_w ℓ _ r χ E _ _ _ _ _ _ _ _ _ (o7 w hw).2⟩, o8⟩
    hrest conj nlam m cloudC lowsC cloudR lowsR h0C h0R V₂ ρV ρA iV qA wD
    τH DatH bH wH mH hrows hseq hwD (fun w hw => srcNO2 ℓ O _ _ _ _ _ _ (hliftR w hw))
    (fun w hw => ⟨(hH0 w hw).1, h0WJ ℓ _ _ _ _ (hH0 w hw).2⟩) hJC hJR

end Formalism.RepresentationBoundsCohomology.FIN
