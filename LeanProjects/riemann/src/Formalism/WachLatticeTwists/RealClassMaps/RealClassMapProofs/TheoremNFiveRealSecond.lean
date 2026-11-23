import Formalism.WachLatticeTwists.RealClassMaps.RealClassMapSecondPlace
import Formalism.WachLatticeTwists.RealClassMaps.RealClassMapProofs.TheoremNFiveReal
import Formalism.WachLatticeTwists.RealClassMaps.RealClassMapProofs.InRowRealOf

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.FIN

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic Formalism.RepresentationBoundsCohomology.JL Formalism.RepresentationBoundsCohomology.JT Formalism.RepresentationBoundsCohomology.JS Formalism.RepresentationBoundsCohomology.SplitClassesAll Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology Formalism.RepresentationBoundsCohomology.T2
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC
open ReciprocityTheory.ChartRestriction.T2 (PadicCoeff FracTop IsFGTop cupFG IsCycOn)

set_option maxHeartbeats 8000000 in
theorem theorem_n_five_real_second : RealClassMapSecondPlace := by
  intro ℓ _ O _ _ _ _ _ _ _ _ _ X X' T T' Z p q b h1 h2 d _ _ R' _ _ _ _ _ hdet Tc _ _ _ _ Ek Ω _ _ _ _ _
    r χ E e₁ δ ι _ _ colIdx hinj
    Aw pl Av j e' hE2 he1 π' ρπ hρπ t ht bl hbl ρk hsurj hblk _ _ _ _ hcard1 sE tE δO what₂ qs s H0
    Sha uT wT sT mT dT UT hEsum cols eO cB vδ N h0 c1
    L _ _ _ _ _ _ tens v₁ κ V _ _ _ _ _ _ iL qV Ff κz F Vo VS Io IS ε T₁ T₂ _ _ _ _ _ _ _ ρ₁ ρ₂ inc π
    γ lam VT VT' _ _ _ _ _ _ _ _ _ _ _ _ _ _ Dat uD huD vD hπD heD _ _ _ _ Fs Hf₁ I γQ ζ ζO nQ u rr gI s₀ u₁ y
    _ _ _ _ HfW Hf₂ gR Im
    Pe _ _ _ _ _ _ ince eve heve PE _ _ _ _ _ _ incE evE hevE Hfe₁ HfE₁ HfE₂ uz
    hinjO hO hFr hA hcyc hinc hur hAv hreal hs1 hs2 hε hδ hδO hrr hse hsE hincE hact huz hu hLe hLE hrat0 hb1 hb3 hb4
    hFix hRows hC hOne hrest
    conj nlam m cloudC lowsC cloudR lowsR h0C h0R V₂ _ _ _ _ ρV ρA iV qA wD
    τH DatH bH wH mH hrows hseq hwD hliftR hH0 hJC hJR
  have hrow : ∀ w ∈ cols, conj w ∈ what₂ := fun w hw => hrows ▸ Finset.mem_image_of_mem conj hw
  obtain ⟨f1, f2, f3, f4, f6, f7, f8, f9, f11⟩ := hFix
  have hres : ∀ (c : Fin (t + 1)) (w : ℕ), lcH1 (uRep O (M := blockRestrictedRepresentationType bl ρk c) r χ) ≤
      (lcH1 (resRep (uRep O (M := blockRestrictedRepresentationType bl ρk c) r χ) (decs Ek Aw w))).comap
        (resH1 (uRep O (M := blockRestrictedRepresentationType bl ρk c) r χ) (decs Ek Aw w)) :=
    fun c w => resLC O _ _ (uRep O (M := blockRestrictedRepresentationType bl ρk c) r χ) (decs Ek Aw w)
  have hFix' : InRhoFixReal (blockRestrictedRepresentationType bl ρk 0) r χ E e₁ colIdx (decs Ek Aw) j what₂ s tens v₁ κ iL qV Ff κz
      (lcH1 (uRep O (M := blockRestrictedRepresentationType bl ρk 0) r χ)) (F 0) Io ε ρ₁ ρ₂ inc π γ lam Dat uD huD vD Fs Im := by
    refine ⟨f1, f2, f3, f4, fun w hw => ?_, f6, f7, f8, f9, fun w hw => ?_, f11⟩
    · rw [kRowRange O (VT w) (VT' w) _ (Dat w) _ _ (uD w) (huD w) (hRows w hw).2.2.2.1.openT]
      exact hres 0 w
    · exact inRowReal_of ℓ r χ E (decs Ek Aw w) ρ₁ inc π (Dat w) (vD w) (hπD w) (heD w) (Fs w) (Hf₁ w) hO hA hinc
        (hur.comp continuous_subtype_val) (hRows w hw).2.2.2.2.2.2.2.2.2
  have hRows' : ∀ w ∈ what₂, (Aw w).valuation (ℓ : Ω) < 1 ∧ IsPlaceOver (Aw w) (pl w) ∧
      (∀ g : decs Ek Aw w, (Dat w).ε g = ε g) ∧ RealLat (Dat w) ∧
      (∀ (g : decs Ek Aw w) t, vD w (ρ₂ g t) = (Dat w).ρTl' g (vD w t)) ∧
      (∀ t m, γ t m = pairKO (Dat w).bT (Dat w).T (uD w m) (vD w t)) ∧
      (∀ a, a ∈ HfW w ↔ ∀ b ∈ Hf₂ w, cupFG (Dat w) a b = 0) ∧
      F 0 w = (((HfW w).restrictScalars O).map (Dat w).q).map (kRow (Dat w) _ (uD w) (huD w)) ∧
      Fs w = ((Hf₂ w).restrictScalars O).comap (Dat w).j' := by
    intro w hw
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, -⟩ := hRows w hw
    exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩
  refine theorem_n_five_real ℓ O X X' T T' Z p q b h1 h2 d R' hdet Tc Ek Ω r χ E e₁ δ ι colIdx hinj Aw pl Av j e' hE2 he1
    π' ρπ hρπ t ht bl hbl ρk hsurj hblk hcard1 sE tE δO what₂ qs s H0 Sha uT wT sT mT dT UT hEsum
    L tens v₁ κ V iL qV Ff κz (fun c => lcH1 (uRep O (M := blockRestrictedRepresentationType bl ρk c) r χ)) F Vo VS Io IS ε T₁ T₂ ρ₁ ρ₂ inc π
    γ lam VT VT' Dat uD huD vD Fs Im I γQ ζ ζO nQ u rr gI s₀ u₁ y HfW Hf₂
    Pe ince eve heve PE incE evE hevE Hfe₁ HfE₁ HfE₂ uz
    hinjO hO hFr hA hcyc hAv hreal hs1 hs2 hε hδ hδO hrr hse hsE hincE hact huz hu hLe hLE hrat0 hb1 hb3 hb4
    hFix' hRows' ?_ ?_ hrest
    conj nlam m cloudC lowsC cloudR lowsR h0C h0R V₂ ρV ρA iV qA (fun w => zcRow (Dat w) (vD w))
    (fun w => clsRowV (Dat w) (wD w)) (fun w => H1 (resRep ρ₁ (decs Ek Aw w))) Hf₁ gR
    τH DatH bH wH mH hrows hseq ?_ ?_ (fun w hw => ⟨rfl, hliftR w hw⟩) hH0 hJC hJR
  · intro c hc
    obtain ⟨g1, g2, g3, g4, g5, ⟨i1, i3, i4⟩, i5⟩ := hC c hc
    exact ⟨g1, g2, g3, g4, g5, i1, fun w _ => hres c w, i3, i4, i5⟩
  · obtain ⟨o1, o2, o3, o4, o5, o6, o7, ⟨i1, i3, i4⟩, o10⟩ := hOne
    refine ⟨o1, o2, o3, o4, o5, o6, o7, ⟨i1, fun w _ => hres c1 w, i3, i4⟩, ?_, o10⟩
    rintro _ ⟨c, hc, rfl⟩
    exact ⟨c, rfl, hc⟩
  · intro w hw
    exact classMapReal O (VT (conj w)) (VT' (conj w)) _ (Dat (conj w)) T₂ (resRep ρ₂ (decs Ek Aw (conj w)))
      (vD (conj w)) (hRows' _ (hrow w hw)).2.2.2.2.1 (Fs (conj w))
  · intro w hw a ha
    exact clsVReal O (VT (conj w)) (VT' (conj w)) _ (Dat (conj w)) T₂ V₂ (resRep ρV (decs Ek Aw (conj w))) iV
      (vD (conj w)) (wD (conj w)) (hwD w hw).1 (hwD w hw).2 a ha

end Formalism.RepresentationBoundsCohomology.FIN
