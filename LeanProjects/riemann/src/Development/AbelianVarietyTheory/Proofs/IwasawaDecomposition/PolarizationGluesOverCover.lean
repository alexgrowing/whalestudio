import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsChartOf
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GlueSchemesOverOpensAlongCocycle
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSemiAbelianTripleGlueCommonGenericPart
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SemiAbelianHomExtendsUniquelyOverDvr
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabDescentOfFieldExtension
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAbelianTripleGlueTwoOpenImmersions
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationBaseChangeModels
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AmpleOfLocalAffineCover
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlueEffectiveCartier
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsModelDominatingModelsOnOpenCover
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeAndRelDimOfOpenCover
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsAffineOpenGUInf

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.TorRef GlobalTheory.FlagMod GlobalTheory.Reg GlobalTheory.PolFin
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv mkT tanM_ext tv_mem)
open MonoidalCategory CartesianMonoidalCategory MonObj Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GlueProj

theorem range_spMap_away {O R : Type} [CommRing O] [CommRing R] (a : O) (b : O →+* R)
    (h : @IsLocalization.Away O _ a R _ b.toAlgebra) : Set.range (spMap b) = {x : Sp O | a ∉ x.asIdeal} := by
  letI := b.toAlgebra
  exact PrimeSpectrum.localization_away_comap_range R a

theorem openImm_range : ∀ {O : Type} [CommRing O] {R : Type} [CommRing R] (a : O) (b : O →+* R) {A X : Scheme.{0}}
    (F : A ⟶ Sp O) (s : X ⟶ Sp R) (ψ : X ⟶ A), @IsLocalization.Away O _ a R _ b.toAlgebra →
    IsPullback ψ s F (spMap b) → IsOpenImmersion ψ ∧ Set.range ψ = F ⁻¹' {x : Sp O | a ∉ x.asIdeal} := by
  intro O _ R _ a b A X F s ψ h hp
  have hb := ModelJoin.isOpenImmersion_away a b h
  refine ⟨MorphismProperty.of_isPullback (P := @IsOpenImmersion) hp.flip hb, ?_⟩
  rw [← range_spMap_away a b h, ← Scheme.Pullback.range_fst, ← hp.isoPullback_hom_fst, Scheme.Hom.comp_base,
    TopCat.coe_comp, Set.range_comp, (hp.isoPullback.hom.surjective).range_eq, Set.image_univ]

theorem isProper_of_cover : ∀ {O : Type} [CommRing O] {I : Type} {R : I → Type} [∀ i, CommRing (R i)] (a : I → O)
    (b : ∀ i, O →+* R i) {A : Scheme.{0}} (F : A ⟶ Sp O) {X : I → Scheme.{0}} (s : ∀ i, X i ⟶ Sp (R i))
    (ψ : ∀ i, X i ⟶ A), (∀ i, @IsLocalization.Away O _ (a i) (R i) _ (b i).toAlgebra) → Ideal.span (Set.range a) = ⊤ →
    (∀ i, IsPullback (ψ i) (s i) F (spMap (b i))) → (∀ i, IsProper (s i)) → IsProper F := by
  intro O _ I R _ a b A F X s ψ h hspan hp hs
  haveI := fun i => ModelJoin.isOpenImmersion_away (a i) (b i) (h i)
  let U : I → (Sp O).Opens := fun i => (spMap (b i)).opensRange
  have hU : iSup U = ⊤ := by
    refine top_le_iff.mp fun x _ => TopologicalSpace.Opens.mem_iSup.mpr ?_
    have : ∃ i, a i ∉ x.asIdeal := by
      by_contra hc
      push_neg at hc
      refine x.isPrime.ne_top (top_le_iff.mp ?_)
      rw [← hspan, Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      exact hc i
    obtain ⟨i, hi⟩ := this
    refine ⟨i, ?_⟩
    show x ∈ Set.range (spMap (b i))
    rw [range_spMap_away (a i) (b i) (h i)]
    exact hi
  have hq : ∀ i, IsPullback (ψ i) (s i ≫ (spMap (b i)).isoOpensRange.hom) F (U i).ι := fun i => by
    refine IsPullback.of_iso (hp i) (Iso.refl _) (Iso.refl _) (spMap (b i)).isoOpensRange (Iso.refl _) ?_ ?_ ?_ ?_
    all_goals simp [U]
  exact CoverGlue.of_isPullback_cover @IsProper hU hq fun i => inferInstance

end GlobalTheory.GlueProj

namespace GlobalTheory.GlueProj

open GlobalTheory.GlueLie GlobalTheory.ShFam GlobalTheory.LocM

theorem cls_polShape {X : Scheme.{0}} {L B : LB X} (m : ℕ) (hL : L.IsLB) (hB : B.IsLB)
    (h : (CechPic.tens (lbPow (CechPic.dual L) m) (CechPic.dual B)).IsLB) :
    CechPic.cls _ h = m • -CechPic.cls L hL + -CechPic.cls B hB := by
  rw [CechPic.cls_tens (isLB_lbPow (CechPic.isLB_dual hL) m) (CechPic.isLB_dual hB),
    CechPic.cls_lbPow (CechPic.isLB_dual hL), CechPic.cls_dual hL, CechPic.cls_dual hB]

theorem isProjOver_of_glue : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l}
    {c : Coeff l} {I : Type} [Finite I] {R : I → Type} [∀ i, CommRing (R i)] {a : I → 𝓞 c.F} {b : ∀ i, 𝓞 c.F →+* R i}
    {ω : ∀ i, R i →+* c.F} (C : ∀ i, Model Xo c (ω i)) (BD : ∀ i, EffCartierData (C i).X) (φ : InvFun (𝓞 E)) (m : ℕ)
    (A : Scheme.{0}) (F : A ⟶ Sp (𝓞 c.F)) (t : SAB H A) (ψ : ∀ i, (C i).X ⟶ A) (B : I → I → Scheme.{0})
    (p : ∀ i k, B i k ⟶ (C i).X) (q : ∀ i k, B i k ⟶ (C k).X), IsCover (algebraMap (𝓞 c.F) c.F) R a b ω →
    (∀ i, IsPullback (ψ i) (C i).s F (spMap (b i))) → (∀ i k, IsPullback (p i k) (q i k) (ψ i) (ψ k)) →
    (∀ i, Nonempty (SABMap (C i).t t (ψ i))) → (∀ i, IsPol φ m (C i) (BD i)) →
    (∀ i k, (BD i).idealSheaf.comap (p i k) = (BD k).idealSheaf.comap (q i k)) → IsProjOver F := by
  intro E _ _ _ H D l Xo c I _ R _ a b ω C BD φ m A F t ψ B p q hC hψ hpq hμ hP hBD
  obtain ⟨-, hloc, hspan⟩ := hC
  have hoi := fun i => openImm_range (a i) (b i) F (C i).s (ψ i) (hloc i).2.2 (hψ i)
  haveI : ∀ i, IsOpenImmersion (ψ i) := fun i => (hoi i).1
  have hprop : ∀ i, IsProper (C i).s := fun i => GlobalTheory.ThetaDescent.isProper_of_isProjOver (C i).proj
  haveI : IsProper F := isProper_of_cover a b F (fun i => (C i).s) ψ (fun i => (hloc i).2.2) hspan hψ hprop
  haveI : A.IsSeparated := ⟨by rw [← terminal.comp_from F]; infer_instance⟩
  have hcov : ∀ x : A, ∃ i, x ∈ Set.range (ψ i) := fun x => by
    have : ∃ i, a i ∉ (F x).asIdeal := by
      by_contra hne
      push_neg at hne
      apply (F x).isPrime.ne_top
      rw [eq_top_iff, ← hspan]
      exact Ideal.span_le.2 (Set.range_subset_iff.2 hne)
    obtain ⟨i, hi⟩ := this
    exact ⟨i, by rw [(hoi i).2]; exact hi⟩
  let sm := fun i => (hμ i).some
  have hLie : ∀ i, (detLie (C i)).IsLB := fun i => isLB_detLie_of_polOf (hP i).2.isLB
  let Λ := gLie C ψ (fun i => (sm i).cart)
  have hΛ : Λ.IsLB := isLB_gLie C ψ _ hLie hcov
  obtain ⟨BD', hBD'⟩ := CartierGlue.exists_glue ψ BD (fun i => inferInstance) hcov (fun i k => by
    have e1 : ((hpq i k).isoPullback.inv ≫ p i k) = pullback.fst (ψ i) (ψ k) := (hpq i k).isoPullback_inv_fst
    have e2 : ((hpq i k).isoPullback.inv ≫ q i k) = pullback.snd (ψ i) (ψ k) := (hpq i k).isoPullback_inv_snd
    rw [← e1, ← e2, Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp, hBD])
  let P := CechPic.tens (lbPow (CechPic.dual Λ) m) (CechPic.dual BD'.lb)
  have hPL : P.IsLB := CechPic.isLB_tens (isLB_lbPow (CechPic.isLB_dual hΛ) m) (CechPic.isLB_dual BD'.isLB_lb)
  have hiso : ∀ i, LBIso (P.pull (ψ i)) (polOf (C i) m (BD i)) := fun i => by
    have hk : BD'.KeepsRegular (ψ i) := BD'.keepsRegular_of_flat (ψ i)
    have e₁ : CechPic.pull (ψ i) (CechPic.cls _ hΛ) = CechPic.cls _ (hLie i) := by
      rw [← CechPic.cls_pull hΛ (ψ i) (pull_isLB hΛ _)]
      exact (CechPic.cls_eq_iff _ _).2 (lbIso_gLie_pull C ψ _ i)
    have e₂ : CechPic.pull (ψ i) (CechPic.cls _ BD'.isLB_lb) = CechPic.cls _ (BD i).isLB_lb := by
      rw [← CechPic.cls_pull BD'.isLB_lb (ψ i) (pull_isLB BD'.isLB_lb _)]
      exact ((CechPic.cls_eq_iff (BD'.pull (ψ i) hk).isLB_lb (pull_isLB BD'.isLB_lb _)).2
        (BD'.lbIso_pull (ψ i) hk)).symm.trans ((CechPic.cls_eq_iff _ _).2
          (EffCartierData.lbIso_of_idealSheaf_eq _ _ ((BD'.idealSheaf_pull (ψ i) hk).trans (hBD' i))))
    refine (CechPic.cls_eq_iff (pull_isLB hPL _) (hP i).2.isLB).1 ?_
    rw [CechPic.cls_pull hPL (ψ i), cls_polShape m hΛ BD'.isLB_lb hPL, map_add, map_nsmul, map_neg, map_neg, e₁, e₂]
    exact (cls_polShape m (hLie i) (BD i).isLB_lb (hP i).2.isLB).symm
  have hamp : IsAmpleLB P := by
    have hX : CompactSpace A := ⟨by simpa using QuasiCompact.isCompact_preimage (f := F) Set.univ isOpen_univ isCompact_univ⟩
    have hXs : QuasiSeparatedSpace A := inferInstance
    exact AmpleOverBase.isAmpleLB_of_basicOpen_cover F ψ a P hX hXs hspan (fun i => inferInstance)
      (fun i => (hoi i).2) (fun i => (hP i).2.of_lbIso (pull_isLB hPL _) (hiso i))
  exact hamp.isProjOver F
end GlobalTheory.GlueProj
