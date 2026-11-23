import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameCarriedAlong
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecCarriedOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleFrameOfSectionUnitsOnClosedFibre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFlatLocalBaseChangeOfProperProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisActsTransitivelyFibresFlatBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameCoefficientsDescendFiniteFreeAffineOpenStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameCoefficientUnitGermsFiniteFreeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CarriedSectionOfFrameCarriedAlongLiftsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

set_option maxHeartbeats 1000000 in

theorem FrameCarried.descend_finiteEtale : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hB : Base R) (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R') (hF : FinExt ρ) (hG : IsGal ρ) (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'] (hS' : IsSemiAbelian G') (U' : Unif (maximalIdeal R') D' A' G') (a : GalAct ρ hD U') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left) (hS : IsSemiAbelian G) (hβ : IsGrpPullback G' G (spMap ρ) β) (hact : ∀ σ, a.act σ ≫ β = β) (R₁ : Type) [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁] (ρ₁ : R →+* R₁), FinExt ρ₁ → ρ₁.Etale → ∀ (V₀ : G.left.Opens) (y : G.left), y ∈ V₀ → ∀ τ : ∀ k : U'.LG.L.ι, Γ(pullback (G'.hom ≫ spMap ρ) (spMap ρ₁), (pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) ⁻¹ᵁ (β ⁻¹ᵁ V₀) ⊓ (pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) ⁻¹ᵁ U'.LG.L.U k)ˣ, FrameAlong U'.LG.L (pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) ((pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) ⁻¹ᵁ (β ⁻¹ᵁ V₀)) τ → (∀ (σ : Gal ρ) (h : IsPullDeg (Gal.hom σ) D'.toPre D'.toPre) (bc : G' ≅ (Over.pullback (specOf (Gal.hom σ))).obj G'), bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ)) = a.act σ → ∀ hP : IsPullUnif (Gal.hom σ) h bc U' U', PullOver hD h → ∀ f' : (pullback (G'.hom ≫ spMap ρ) (spMap ρ₁) : Scheme.{0}) ⟶ pullback (G'.hom ≫ spMap ρ) (spMap ρ₁), f' ≫ (pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) = (pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) ≫ a.act σ → f' ≫ (pullback.snd (G'.hom ≫ spMap ρ) (spMap ρ₁)) = (pullback.snd (G'.hom ≫ spMap ρ) (spMap ρ₁)) → FrameCarriedAlong U'.LG.L (pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) ((pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) ⁻¹ᵁ (β ⁻¹ᵁ V₀)) τ _ (Classical.choose hP.lg) f') → ∃ V : G.left.Opens, y ∈ V ∧ ∃ T : ∀ k : U'.LG.L.ι, Γ(G'.left, β ⁻¹ᵁ V ⊓ U'.LG.L.U k)ˣ, IsFrameOver U'.LG.L (β ⁻¹ᵁ V) T ∧ ∀ (σ : Gal ρ) (h : IsPullDeg (Gal.hom σ) D'.toPre D'.toPre) (bc : G' ≅ (Over.pullback (specOf (Gal.hom σ))).obj G'), bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ)) = a.act σ → ∀ hP : IsPullUnif (Gal.hom σ) h bc U' U', PullOver hD h → FrameCarried U'.LG.L (β ⁻¹ᵁ V) T _ (Classical.choose hP.lg) := by
  intro R _ _ _ hB R' _ _ _ ρ hF hG D D' hD A' G' _ _ hS' U' a G _ _ β hS hβ hact R₁ _ _ _ ρ₁ hF₁ hE₁ V₀ y hy τ hτ hτc
  have hL : U'.LG.L.IsLB := U'.LG.isLB
  haveI : IsNoetherianRing R := hB.1.1
  have hfl : ρ₁.Flat := (RingHom.Etale.iff_flat_and_formallyUnramified.1 hE₁).1
  obtain ⟨-, -, -, hqs, -, -, -, d, b, hb⟩ := GlobalTheory.finiteFlat_proper_baseChange_facts R R₁ ρ₁ hF₁.2.1 hF₁.2.2 hfl
    G'.left G'.left (pullback (G'.hom ≫ spMap ρ) (spMap ρ₁)) (pullback (G'.hom ≫ spMap ρ) (spMap ρ₁)) (𝟙 _) (𝟙 _)
    (G'.hom ≫ spMap ρ) (pullback.snd _ _) (pullback.fst _ _) (pullback.fst _ _) (IsPullback.of_hasPullback _ _)
    (IsPullback.id_vert _) inferInstance
  have hβf : IsFinite β :=
    MorphismProperty.of_isPullback (P := @IsFinite) hβ.1.flip ((IsFinite.SpecMap_iff _).2 hF.2.2)
  have hβc : IsClosedMap β.base := β.isClosedMap
  have hGfl : Flat G.hom := by haveI := hS.smooth; infer_instance
  obtain ⟨V₁, hV₁a, hyV₁, hV₁⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp G.left.isBasis_affineOpens) hy
  have hOa : IsAffineOpen (β ⁻¹ᵁ V₁) := IsAffineOpen.preimage hV₁a β
  have hOW : β ⁻¹ᵁ V₁ ≤ β ⁻¹ᵁ V₀ := fun x hx => hV₁ hx
  obtain ⟨s, hs, hdec⟩ := GlobalTheory.T.frame_coefficients_descend_finiteFree_affineOpen R R₁ ρ₁ d b hb G'.left (G'.hom ≫ spMap ρ) U'.LG.L hL (β ⁻¹ᵁ V₀) (β ⁻¹ᵁ V₁) hOW hOa τ hτ
  have hcar : ∀ (σ : Gal ρ) (h : IsPullDeg (Gal.hom σ) D'.toPre D'.toPre)
      (bc : G' ≅ (Over.pullback (specOf (Gal.hom σ))).obj G'),
      bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ)) = a.act σ → ∀ hP : IsPullUnif (Gal.hom σ) h bc U' U',
      PullOver hD h → ∀ l, SecCarriedOver U'.LG.L (β ⁻¹ᵁ V₁) (s l) _ (Classical.choose hP.lg) := by
    intro σ h bc hbc hP hPO
    refine GlobalTheory.T.carried_section_of_frame_carried_along_lifts R R₁ ρ₁ d b hb G'.left (G'.hom ≫ spMap ρ) U'.LG.L (β ⁻¹ᵁ V₀) (β ⁻¹ᵁ V₁) hOW τ s hdec _
      (Classical.choose hP.lg) ?_ ?_
    · rw [hbc, ← hβ.1.w, ← Category.assoc, hact]
    · intro f' h1 h2
      exact hτc σ h bc hbc hP hPO f' (h1.trans (by rw [hbc])) h2
  have hd : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h0 | h0
    · subst h0
      obtain ⟨c, hc, -⟩ := hb 1
      simp at hc
    · exact h0
  have key : ∃ l, ∀ (z : G'.left) (k : U'.LG.L.ι), β z = y → z ∈ U'.LG.L.U k →
      IsUnit (gs (𝟙 G'.left) z (β ⁻¹ᵁ V₁ ⊓ U'.LG.L.U k) (s l k)) := by
    by_cases hne : ∃ z₀, β z₀ = y
    · obtain ⟨z₀, hz₀⟩ := hne
      obtain ⟨z', hz'⟩ := hqs z₀
      have hz'O : (pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) z' ∈ β ⁻¹ᵁ V₁ := by
        show β ((pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)).base z') ∈ V₁
        rw [hz', hz₀]; exact hyV₁
      obtain ⟨l, hl⟩ := GlobalTheory.T.exists_frameCoefficient_unitGerms_finiteFree R R₁ ρ₁ d b G'.left (G'.hom ≫ spMap ρ) U'.LG.L hL (β ⁻¹ᵁ V₀) (β ⁻¹ᵁ V₁) hOW τ s hs
        hdec z' hz'O
      have hl' : ∀ k, z₀ ∈ U'.LG.L.U k → IsUnit (gs (𝟙 G'.left) z₀ (β ⁻¹ᵁ V₁ ⊓ U'.LG.L.U k) (s l k)) := by
        intro k hk
        have := hl k (by show (pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)).base z' ∈ _; rw [hz']; exact hk)
        revert this
        show IsUnit (gs (𝟙 G'.left) ((pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)).base z') _ _) → _
        rw [hz']; exact id
      refine ⟨l, fun z k hz hk => ?_⟩
      obtain ⟨σ, hσ⟩ := GlobalTheory.T.galois_acts_transitively_fibres_flat_baseChange R R' ρ hF.2.2 hG G.left G'.left G.hom G'.hom β hGfl hβ.1 a.act
        (fun σ => (a.cart σ).1.w) hact z₀ z (hz₀.trans hz.symm)
      obtain ⟨h, bc, hbc, hP, hPO⟩ := a.unif σ
      obtain ⟨k₀, hk₀⟩ := exists_chart hL z₀
      have hz₀O : z₀ ∈ β ⁻¹ᵁ V₁ := show β z₀ ∈ V₁ from hz₀ ▸ hyV₁
      have hφ : (bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ))) z₀ = z := by rw [hbc]; exact hσ
      subst hφ
      have hzO : (bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ))) z₀ ∈ β ⁻¹ᵁ V₁ :=
        show β _ ∈ V₁ from hz ▸ hyV₁
      have e := hcar σ h bc hbc hP hPO l z₀ k k₀ hz₀O hzO hk₀ hk
      have hu : IsUnit (gs (bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ))) z₀ _ (s l k)) := by
        rw [e]; exact (Units.isUnit _).mul (hl' k₀ hk₀)
      rw [gs_eq_map_gs (bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ))) z₀ (β ⁻¹ᵁ V₁ ⊓ U'.LG.L.U k) ⟨hzO, hk⟩] at hu
      exact (isUnit_map_iff _ _).1 hu
    · push_neg at hne
      exact ⟨⟨0, hd⟩, fun z k hz _ => absurd hz (hne z)⟩
  obtain ⟨l, hl⟩ := key
  obtain ⟨V, hyV, -, T, hT, hTc⟩ :=
    GlobalTheory.Mum.exists_frame_of_isUnit_on_fibre G'.left G.left β hβc U'.LG.L hL V₁ (s l) (hs l) y hyV₁ hl
  exact ⟨V, hyV, T, hT, fun σ h bc hbc hP hPO => hTc _ _ (hcar σ h bc hbc hP hPO l)⟩

end GlobalTheory.Mum
