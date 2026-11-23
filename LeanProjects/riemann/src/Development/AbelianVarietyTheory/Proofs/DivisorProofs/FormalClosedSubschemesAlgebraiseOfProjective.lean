import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BaseIdealIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.ProjectiveNotIsUnit
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveAlgebraisationFormalCompleteLoca
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsHomOfThickenings
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProjectiveAlgebraisationFormalEmbeddingComStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsReductionClosedSubschemeIffIdealEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompatibleReductionSystemGivesThickeningTowerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedImmersionOfVeryAmpleSectionsCompatibleStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

theorem GlobalTheory.FormalAlg.alg_of_isProjBy : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R → ∀ (W : Scheme.{0}) (f : W ⟶ Spec (CommRingCat.of R)), IsProjBy f → Alg f I := by
  intro R _ _ I hc W f hP t ht hp
  obtain ⟨q, β, hq, hβ, hpb⟩ := GlobalTheory.T.compatibleReductionSystem_gives_thickening_tower R I W f t ht
  let Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) := fun e => Over.mk (q e)
  let j : ∀ e, (Y e).left ⟶ W := fun e => (t e).subschemeι
  obtain ⟨H, hH, n, s, hs⟩ := hP
  have hL : ∀ e, (H.pull (j e)).IsLB := fun e => LB.isLB_pull hH _
  choose t' ht' using fun e => GlobalTheory.MorAlg.exists_isPull (j e) hH s
  have hv : ∀ e, GlobalTheory.MorAlg.IsPull (β e) (t' (e + 1)) (t' e) := fun e =>
    GlobalTheory.MorAlg.IsPull.cancel hH (hL _) (hL _) (ht' (e + 1)) (by
      have h1 : β e ≫ j (e + 1) = j e := hβ e
      rw [h1]; exact ht' e)
  choose v hv cv using hv
  have hjR : ∀ e, j e ≫ f = (Y e).hom ≫ thick R I e := hq
  have hva : VeryAmpleBy (Y 0).hom (H.pull (j 0)) (t' 0) := by
    obtain ⟨w, hw, c⟩ := ht' 0
    refine GlobalTheory.AbLaw.VeryAmplePull.veryAmpleBy_pull R W f H n s hH hs _ (Ideal.Quotient.mk (I ^ (0 + 1))) _ _ (j 0) (hjR 0) ?_ _ w _ (hL 0) hw c
    have h₃ : IsClosedImmersion (pullback.lift (j 0) (Y 0).hom (hjR 0) ≫ pullback.fst f (thick R I 0)) := by
      rw [pullback.lift_fst]
      exact inferInstanceAs (IsClosedImmersion (t 0).subschemeι)
    exact IsClosedImmersion.of_comp _ (pullback.fst f (thick R I 0))
  obtain ⟨B, H', s', b, w, hH', hs', hb, -, hw, heq⟩ := GlobalTheory.T.exists_projective_algebraisation_formalEmbedding_complete R I hc Y β hpb (fun e => H.pull (j e)) v
    (fun e => ⟨hL e, hv e⟩) n t' cv hva
  obtain ⟨φ, u, hφ, hu, cu⟩ := GlobalTheory.exists_hom_of_veryAmpleBy R W f H n s hH hs B.left B.hom H' s' hH' hs'.1
    fun d F hF h0 => (mem_vanIdeal _ _ _).1 (heq d F hF fun e => (mem_vanIdeal _ _ _).2 fun k => by
      rw [← hjR]
      exact (ht' e).eqn f hH hF h0 k)
  have hbφ : ∀ e, b e ≫ φ = j e := fun e => by
    obtain ⟨w₁, hw₁, c₁⟩ := GlobalTheory.MorAlg.IsPull.comp hH hH' (hL e) ⟨u, hu, cu⟩ ⟨w e, (hw e).1, (hw e).2⟩
    obtain ⟨w₂, hw₂, c₂⟩ := ht' e
    refine GlobalTheory.MapUniq.hom_eq_of_pull_sections R W f H n s hH hs _ _ (t' e) _ _ w₁ w₂ (hL e) ?_ hw₁ hw₂ c₁ c₂
    rw [Category.assoc, hφ, hjR]
    exact (hb e).w
  haveI hci : IsClosedImmersion φ := GlobalTheory.T.isClosedImmersion_of_veryAmpleSections_compatible R W f H n s hH hs B.left B.hom H' s' φ u hH' hs' hφ hu cu
  haveI hBp : IsProper (φ ≫ f) := by
    rw [hφ]; exact GlobalTheory.AbLaw.isProper_of_isProjBy R _ _ ⟨H', hH', n, s', hs'⟩
  refine ⟨φ.ker, ?_, fun e => ?_⟩
  · change IsProper (φ.imageι ≫ f)
    have hg : φ.imageι = inv φ.toImage ≫ φ := (IsIso.eq_inv_comp _).2 φ.toImage_imageι
    rw [hg, Category.assoc]
    infer_instance
  · have key := (GlobalTheory.T.isReduction_closedSubscheme_iff_ideal_eq R (I ^ (e + 1)) W B.left (Y e).left f φ (j e) (q e) hci
      (inferInstanceAs (IsClosedImmersion (t e).subschemeι)) (hq e)).1
      ⟨b e, hbφ e, by rw [hφ]; exact hb e⟩
    rw [key]
    exact Scheme.IdealSheafData.ker_subschemeι (t e)
