import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsUniquePartner
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SecCmp
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniformisationCompleteLocalNormalDomain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGen
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniqueExpansionSectionAdmissibleBase
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EgaHolds
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpandsAtSecIsMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleSectionBaseMulCancelFlatDomainStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionExpansionScaleBaseElementStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GermDvdOfSectionExpansionDvdClosedFibreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleSectionDvdEverywhereSmoothConnectedFibStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseMulSectionOfGermDvdFlatDomainStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.SecDiv

theorem resTop_map {Y : Scheme.{0}} {V W : Y.Opens} (h : W ≤ V) (c : Γ(Y, ⊤)) :
    (Y.presheaf.map (homOfLE h).op).hom (ReciprocityTheory.ChartRestriction.G.Out.resTop V c) = ReciprocityTheory.ChartRestriction.G.Out.resTop W c := by
  unfold ReciprocityTheory.ChartRestriction.G.Out.resTop
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem exists_secIsMul {R : Type} [CommRing R] {Y : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of R)) {L : LB Y}
    (a : R) (τ : LB.Sec L) : ∃ σ : LB.Sec L, ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul p a σ τ := by
  unfold ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul
  refine ⟨⟨fun j => ReciprocityTheory.ChartRestriction.G.Out.resTop (L.U j) (scal p a) * τ.f j, fun i j => ?_⟩, fun j => rfl⟩
  simp only [map_mul, resTop_map]
  rw [τ.2 i j]
  ring

theorem exists_expT_of_dvd : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : GlobalTheory.UU.PreU (maximalIdeal R) D A G) (σ : U.SecGT (𝟙_ _) 1) (f g : ∀ α, GlobalTheory.UU.SecBT D (𝟙_ _) 1 α) (q : R), q ≠ 0 → U.ExpT (𝟙_ _) 1 σ f → (∀ α, ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul (𝟙_ _ ⊗ D.P.A).hom q (f α) (g α)) → ∃ τ : U.SecGT (𝟙_ _) 1, U.ExpT (𝟙_ _) 1 τ g := by
  intro R _ _ _ hB D A G _ _ U σ f g q hq hσ hfg
  have hB' : AdmBase R (maximalIdeal R) ∧ CharZero R := hB
  have h1 : IsNoetherianRing R ∧ IsDomain R ∧ IsIntegrallyClosed R ∧ IsAdicComplete (maximalIdeal R) R := hB'.1
  obtain ⟨hN, -, hIC, hC⟩ := h1
  haveI := hN
  haveI := hIC
  have hs := U.semi
  haveI := hs.smooth
  haveI := hs.geomConnected
  haveI : IsIso (λ_ G).hom.left := inferInstanceAs (IsIso ((Over.forget _).mapIso (λ_ G)).hom)
  have hSm : Smooth (𝟙_ (Over (Sp R)) ⊗ G).hom := by
    rw [← Over.w (λ_ G).hom]
    infer_instance
  have hGC : GeometricallyConnected (𝟙_ (Over (Sp R)) ⊗ G).hom := by
    have hsq : IsPullback (λ_ G).hom.left (𝟙_ (Over (Sp R)) ⊗ G).hom G.hom (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨by rw [Over.w, Category.comp_id]⟩
    exact MorphismProperty.of_isPullback (P := @GeometricallyConnected) hsq inferInstance
  have he : (η[G].left ≫ (λ_ G).inv.left) ≫ (𝟙_ (Over (Sp R)) ⊗ G).hom = 𝟙 _ := by
    simp only [Category.assoc, Over.w]
    rfl
  have hLB : (LB.LinComb U.P.L.L (K := Fin 1) (fun _ : Fin 1 => (snd (𝟙_ (Over (Sp R))) G).left)
      (fun _ => ((1 : ℕ) : ℤ))).IsLB := by
    first
    | exact ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB _ U.P.L.isLB _ _
    | exact ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB _ _ _
  have hloc := GlobalTheory.T.germ_dvd_of_sectionExpansion_dvd_closedFibre R hB D A G U σ f g q hσ hfg
  have hall := GlobalTheory.T.lineBundle_section_dvd_everywhere_smooth_connected_fibres R _ (𝟙_ (Over (Sp R)) ⊗ G).hom hSm hGC _ he _ hLB σ q hq hloc
  have hflat : Flat (𝟙_ (Over (Sp R)) ⊗ G).hom := inferInstance
  obtain ⟨τ, hτ⟩ := GlobalTheory.T.exists_baseMul_section_of_germ_dvd_flat_domain R _ (𝟙_ (Over (Sp R)) ⊗ G).hom hflat _ σ q hq hall
  have hEga : GlobalTheory.LN.AlgSt ∧ GlobalTheory.LN.MorAlgSt ∧ GlobalTheory.LN.SecAlgSt ∧ GlobalTheory.LN.PicardZeroDegenerationCondition := GlobalTheory.LN.ega_holds
  obtain ⟨h, hh⟩ := GlobalTheory.CompleteBaseExpansion.exists_expT hEga.2.2.1 hC U 1 τ
  choose f' hf' using fun α => exists_secIsMul (𝟙_ (Over (Sp R)) ⊗ D.P.A).hom q (h α)
  have hσf' : U.ExpT (𝟙_ _) 1 σ f' := GlobalTheory.T.sectionExpansion_scale_base_element R (maximalIdeal R) D A G U 1 q σ τ f' h hτ hf' hh
  have hjac : maximalIdeal R ≤ Ideal.jacobson ⊥ := (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge
  have hff' : f' = f := GlobalTheory.CompleteBaseExpansion.expT_unique hjac U 1 σ f' f hσf' hσ
  have hflatD : Flat (𝟙_ (Over (Sp R)) ⊗ D.P.A).hom := by
    haveI : IsIso (λ_ D.P.A).hom.left := inferInstanceAs (IsIso ((Over.forget _).mapIso (λ_ D.P.A)).hom)
    haveI : Smooth D.P.A.hom := D.P.isAb.smooth
    rw [← Over.w (λ_ D.P.A).hom]
    infer_instance
  have hhg : h = g := by
    funext α
    have hfa := hf' α
    rw [hff'] at hfa
    exact GlobalTheory.T.lineBundleSection_baseMul_cancel_flat_domain R _ _ hflatD _ q hq (f α) (h α) (g α) hfa (hfg α)
  refine ⟨τ, ?_⟩
  rw [← hhg]
  exact hh

end GlobalTheory.SecDiv
