import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TraitOrdOfTraitOrdPt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDvrExtensionEtaleStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DvrLiftEtaleStalkStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BoundaryEtaleStalkUnifStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BoundaryEtaleStalkFormsStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Cartier

namespace GlobalTheory.TorRef

theorem exists_lift_formAt_chart : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} (Z : GMod Xo c) (Cn : ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] (m : ℕ), (Fin m → LinearMap.BilinForm ℤ X) → Prop), HasCones Cn Z → ∀ {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (ξ : Sp R ⟶ Z.X) (t : SAB H (Sp R)) (_ : SABMap t Z.t ξ) (P : PELUnif (maximalIdeal R) t), IsCN R → IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom → ((residue R).comp (Scheme.stalkClosedPointTo ξ).hom).FormallyUnramified → P.TorsionIso → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ ϖ : W, Irreducible ϖ → ∀ (χ : Sp W ⟶ Z.X) (tW : SAB H (Sp W)) (_ : SABMap tW Z.t χ) (PW : PELUnif (maximalIdeal W) tW), Set.range (jK W ≫ χ) ⊆ Set.range Z.j → ∀ be ∈ levelForms H 1 PW.D.toPre.X, IsMonomial PW.D.toPre ![ϖ] ![be] → ∀ hs : χ (closedPoint W) ⤳ ξ (closedPoint R), (χ (closedPoint W) = ξ (closedPoint R) ∨ ringKrullDim (Z.X.presheaf.stalk (χ (closedPoint W))) ≤ 1) → 0 < ringKrullDim (Z.X.presheaf.stalk (χ (closedPoint W))) → ∃ (W' : Type) (_ : CommRing W') (_ : IsDomain W') (_ : IsLocalRing W') (ι : W →+* W') (g : R →+* W') (e : P.D.toPre.X →ₗ[𝓞 E] PW.D.toPre.X), CDvr W' ∧ Irreducible (ι ϖ) ∧ Function.Surjective e ∧ (∀ a, g ((Scheme.stalkClosedPointTo ξ).hom a) = ι ((Scheme.stalkClosedPointTo χ).hom ((Z.X.presheaf.stalkSpecializes hs).hom a))) ∧ FormAt P.D.toPre g (ι ϖ) (be.compl₁₂ e.toAddMonoidHom.toIntLinearMap e.toAddMonoidHom.toIntLinearMap) := by
  intro E _ _ _ H D l Xo c Z Cn hC R _ _ _ ξ t mξ P hCN hEt hFU hTI W _ _ _ hW ϖ hϖ χ tW mW PW hχ be hbe hmon hs hd h0
  by_cases hq : χ (closedPoint W) = ξ (closedPoint R)
  · have key : ∀ (y : Z.X) (hy : y ⤳ ξ (closedPoint R)), y = ξ (closedPoint R) →
        IsLocalHom (Z.X.presheaf.stalkSpecializes hy).hom := by
      intro y hy hyx
      subst hyx
      rw [TopCat.Presheaf.stalkSpecializes_refl]
      exact isLocalHom_of_isIso _
    haveI := key _ hs hq
    obtain ⟨W', _, _, _, ι, g, hW', hι, hc⟩ := GlobalTheory.T.exists_dvr_extension_etale (Scheme.stalkClosedPointTo ξ).hom
      ((Scheme.stalkClosedPointTo χ).hom.comp (Z.X.presheaf.stalkSpecializes hs).hom) hCN hEt hFU hW inferInstance
    have hcomm : ∀ a, g ((Scheme.stalkClosedPointTo ξ).hom a) =
        ι ((Scheme.stalkClosedPointTo χ).hom ((Z.X.presheaf.stalkSpecializes hs).hom a)) := fun a => RingHom.congr_fun hc a
    obtain ⟨e, he, hf⟩ := GlobalTheory.T.boundary_etale_stalk_unif Z ξ t mξ P hCN hEt hFU hTI W hW ϖ hϖ χ tW mW PW hχ be hbe hmon hs hq W' ι g hW' (hι ϖ hϖ) hcomm
    exact ⟨W', inferInstance, inferInstance, inferInstance, ι, g, e, hW', hι ϖ hϖ, he, hcomm, hf⟩
  · have h1 : ringKrullDim (Z.X.presheaf.stalk (χ (closedPoint W))) = 1 := by
      rcases hd with hd | hd
      · exact absurd hd hq
      · refine le_antisymm hd ?_
        generalize ringKrullDim (Z.X.presheaf.stalk (χ (closedPoint W))) = d at h0 hd ⊢
        induction d using WithBot.recBotCoe with
        | bot => exact absurd h0 (by simp)
        | coe n =>
          induction n using ENat.recTopCoe with
          | top => simp
          | coe n =>
            have : (0 : ℕ) < n := by exact_mod_cast h0
            exact_mod_cast this
    obtain ⟨W', _, _, _, ι, g, hW', hιϖ, hcomm⟩ := GlobalTheory.T.dvr_lift_etale_stalk Z ξ hCN hEt hFU W hW ϖ hϖ χ hχ hs hq h1
    obtain ⟨e, he, hf⟩ := GlobalTheory.T.boundary_etale_stalk_forms Z ξ t mξ P hCN hEt hFU hTI W hW ϖ hϖ χ tW mW PW hχ be hbe hmon hs hq h1 W' ι g hW' hιϖ hcomm
    exact ⟨W', inferInstance, inferInstance, inferInstance, ι, g, e, hW', hιϖ, he, hcomm, hf⟩

end GlobalTheory.TorRef
