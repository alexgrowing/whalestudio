import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PullData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentFactorUniformisedGroupsBaseChange
import Development.AbelianVarietyTheory.Definitions.Divisors.MinSt5OfMinSt4
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusEndOfPadd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinHomIffLinEnd

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum

namespace GlobalTheory.Mum

open GlobalTheory.TorusCoord GlobalTheory.PullLinear in

theorem actsAs_of_isPullUnif : ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (θ : R →+* V) (I : Ideal R) (I' : Ideal V) (D : DegData R I) (D' : DegData V I') (hD : IsPullDeg θ D.toPre D'.toPre) (A : PolAV (Sp (FractionRing R))) (A' : PolAV (Sp (FractionRing V))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (G' : Over (Sp V)) [GrpObj G'] [IsCommMonObj G'] (bc : G' ≅ (Over.pullback (specOf θ)).obj G) (U : Unif I D A G) (U' : Unif I' D' A' G'), IsPullUnif θ hD bc U U' → ∀ (b : D.toPre.P.A ⟶ D.toPre.P.A) (h : D.toPre.X → D.toPre.X) (g : G ⟶ G) (b' : D'.toPre.P.A ⟶ D'.toPre.P.A) (h' : D'.toPre.X → D'.toPre.X) (g' : G' ⟶ G'), IsMonHom b' → ActsAs U.toUnifPre b h g → g' ≫ bc.hom = bc.hom ≫ (Over.pullback (specOf θ)).map g → b' ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf θ)).map b → (∀ y, hD.xe (h' y) = h (hD.xe y)) → ActsAs U'.toUnifPre b' h' g' := by
  intro R R' _ _ _ _ φ I I' D D' hD A A' G _ _ G' _ _ bc U U' hU b k₀ g b' k' g' hb' hlin hG hB hx
  obtain ⟨wL, -, he, -, H⟩ := (isPullUnif_iff_stalks R R' I I' φ D D' hD A A' G G' bc U U').1 hU
  choose h hf hpt _hw using H
  have hact : ∀ (e : ℕ), ((Over.pullback (thick R' I' e)).map g').left ≫ h e =
      h e ≫ ((Over.pullback (thick R I e)).map g).left := by
    intro e
    have hf' : h e ≫ pullback.fst G.hom (thick R I e) = pullback.fst G'.hom (thick R' I' e) ≫
      bc.hom.left ≫ pullback.fst G.hom (specOf φ) := hf e
    have : IsClosedImmersion (thick R I e) :=
      IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    have hmono : Mono (pullback.fst G.hom (thick R I e)) := inferInstance
    rw [← cancel_mono (pullback.fst G.hom (thick R I e)), Category.assoc, Category.assoc, map_left_fst,
      ← Category.assoc (h e), hf', ← Category.assoc, map_left_fst, Category.assoc,
      act_proj _ bc.hom hG, Category.assoc, Category.assoc, Category.assoc]
  have hq : ∀ (e : ℕ), (Over.pullback (thick R' I' e)).map g' ≫ (U'.gt e).q =
      (U'.gt e).q ≫ (Over.pullback (thick R' I' e)).map b' := by
    intro e
    have k : ∀ {S : Type} [CommRing S] [IsDomain S] {J : Ideal S} {E : DegPre S}
        {K : Over (Spec (CommRingCat.of S))} [GrpObj K] [IsCommMonObj K] (c : GtCoord J E e K)
        (u : E.P.A ⟶ E.P.A), (c.q ≫ (Over.pullback (thick S J e)).map u).left ≫
          pullback.fst E.P.A.hom (thick S J e) = c.pG.left ≫ u.left := by
      intro S _ _ J E K _ _ c u
      rw [Over.comp_left, Category.assoc, map_left_fst, PullLinear.pG_left, Category.assoc]
    have k₁ : ((Over.pullback (thick R I e)).map g).left ≫ (U.gt e).pG.left =
        (U.gt e).pG.left ≫ b.left := by
      rw [← k, ← (hlin e).1]
      exact (Category.assoc _ _ _).symm
    have k₂ : (Over.map (thick R' I' e)).map ((Over.pullback (thick R' I' e)).map g') ≫
        (U'.gt e).pG = (U'.gt e).pG ≫ b' := by
      refine ext_of_iso_pullback _ hD.e ?_
      change (((Over.pullback (thick R' I' e)).map g').left ≫ (U'.gt e).pG.left) ≫ _ =
        ((U'.gt e).pG.left ≫ b'.left) ≫ _
      rw [Category.assoc, Category.assoc, act_proj _ hD.e.hom hB, (hpt e).1,
        ← Category.assoc (U'.gt e).pG.left, (hpt e).1, ← Category.assoc, hact, Category.assoc,
        Category.assoc, k₁]
    refine ext_of_pullback _ ?_
    rw [k, Over.comp_left, Category.assoc]
    exact congrArg (·.left) k₂
  refine fun e => ⟨hq e, ?_⟩
  obtain ⟨t, ht, hi⟩ := (hlin e).2
  have hk : ((U'.gt e).i ≫ (Over.pullback (thick R' I' e)).map g') ≫ (U'.gt e).q =
      toUnit _ ≫ η[thickObj R' I' e D'.toPre.P.A] := by
    rw [Category.assoc, hq, ← Category.assoc, (U'.gt e).isKernel.w, Category.assoc,
      IsMonHom.one_hom]
  have hi' := (U'.gt e).isKernel.lift_fst _ _ hk
  generalize (U'.gt e).isKernel.lift _ _ hk = t' at hi'
  refine ⟨t', ?_, hi'.symm⟩
  obtain ⟨s, τ, hτ⟩ := exists_point (U.gt e) (U'.gt e) (hpt e).1 ((hpt e).2 0).1 (𝟙 _)
  have hτ' : ((τ ≫ t) ≫ (U.gt e).i).left = (t' ≫ (U'.gt e).i).left ≫ h e := by
    rw [Category.assoc, ← hi, ← Category.assoc, Over.comp_left, hτ, hi', Category.id_comp,
      Over.comp_left, Category.assoc, Category.assoc, hact]
  intro χ
  refine unit_ext fun z _ => ?_
  have e₁ := char_eq (U.gt e) (U'.gt e) hD.w ((hpt e).2 χ).1 ((hpt e).2 χ).2 t' (τ ≫ t) hτ' z
  have e₂ := char_eq (U.gt e) (U'.gt e) hD.w ((hpt e).2 (k' χ)).1 ((hpt e).2 (k' χ)).2
    (𝟙 _) τ hτ z
  have e₃ := (torusEndOf_iff _ _ t).1 ht _ τ.left z (hD.xe χ)
  rw [hx] at e₂
  refine ((gm_res (𝟙 _) z (V := ⊤) _ trivial _).trans (gm_pull (𝟙 _) t'.left z ⊤ trivial _)).trans ?_
  rw [Category.id_comp]
  exact e₁.symm.trans (e₃.trans e₂)

end GlobalTheory.Mum
