import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FlatQuotientIsoOfSameKernel
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FormallyUnramifiedOfCompOfEtaleOfSurjective

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace AbelianQuotient

variable {S : Scheme.{0}}

lemma exists_desc {X Y Z : Over S} (p : X ⟶ Y) [Flat p.left] [Surjective p.left]
    [QuasiCompact p.left] (f : X ⟶ Z)
    (h : ∀ (W : Over S) (a b : W ⟶ X), a ≫ p = b ≫ p → a ≫ f = b ≫ f) :
    ∃ β : Y ⟶ Z, p ≫ β = f := by
  have hc : ∀ {W : Scheme.{0}} (g g' : W ⟶ X.left), g ≫ p.left = g' ≫ p.left →
      g ≫ f.left = g' ≫ f.left := by
    intro W g g' hg
    have hw : g' ≫ X.hom = g ≫ X.hom := by
      rw [← Over.w p, ← Category.assoc, ← hg, Category.assoc]
    have := h (Over.mk (g ≫ X.hom)) (Over.homMk g rfl) (Over.homMk g' hw)
      (Over.OverMorphism.ext hg)
    exact congrArg CommaMorphism.left this
  have hfac := EffectiveEpi.fac p.left f.left hc
  exact ⟨Over.homMk (EffectiveEpi.desc p.left f.left hc) (by
    rw [← cancel_epi p.left, ← Category.assoc, hfac, Over.w, Over.w]),
    Over.OverMorphism.ext hfac⟩

lemma flat_tensorHom {X Y X' Y' : Over S} (f : X ⟶ Y) (g : X' ⟶ Y')
    [hf : Flat f.left] [hg : Flat g.left] : Flat (f ⊗ₘ g).left := by
  rw [Over.tensorHom_left]
  exact MorphismProperty.pullbackMap (P := @Flat) hf hg (Over.w f).symm (Over.w g).symm

lemma surjective_tensorHom {X Y X' Y' : Over S} (f : X ⟶ Y) (g : X' ⟶ Y')
    [hf : Surjective f.left] [hg : Surjective g.left] : Surjective (f ⊗ₘ g).left := by
  rw [Over.tensorHom_left]
  have : MorphismProperty.IsStableUnderComposition @Surjective.{0} :=
    ⟨fun _ _ _ _ => inferInstance⟩
  exact MorphismProperty.pullbackMap (P := @Surjective) hf hg (Over.w f).symm (Over.w g).symm

lemma quasiCompact_tensorHom {X Y X' Y' : Over S} (f : X ⟶ Y) (g : X' ⟶ Y')
    [hf : QuasiCompact f.left] [hg : QuasiCompact g.left] : QuasiCompact (f ⊗ₘ g).left := by
  rw [Over.tensorHom_left]
  exact MorphismProperty.pullbackMap (P := @QuasiCompact) hf hg (Over.w f).symm (Over.w g).symm

theorem exists_grpObj {A H Q : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj H] (i : H ⟶ A)
    [IsMonHom i] (q : A ⟶ Q) [Flat q.left] [Surjective q.left] [QuasiCompact q.left]
    (hq : IsPullback ((fst H A ≫ i) * snd H A) (snd H A) q q) :
    ∃ _ : GrpObj Q, IsCommMonObj Q ∧ IsMonHom q ∧ IsPullback i (toUnit H) q η[Q] := by
  have rel : ∀ {W : Over S} (a b : W ⟶ A), a ≫ q = b ≫ q ↔ ∃ t : W ⟶ H, a = (t ≫ i) * b := by
    intro W a b
    constructor
    · intro h
      refine ⟨hq.lift a b h ≫ fst H A, ?_⟩
      have h1 := hq.lift_fst a b h
      rw [comp_mul, hq.lift_snd] at h1
      rw [Category.assoc, h1]
    · rintro ⟨t, rfl⟩
      have := lift t b ≫= hq.w
      simpa [comp_mul, ← Category.assoc] using this
  have := flat_tensorHom q q
  have := surjective_tensorHom q q
  have := quasiCompact_tensorHom q q
  have := FlatQuotient.epi_of_flat_surjective q
  have := FlatQuotient.epi_tensorHom q q
  have := FlatQuotient.epi_tensorHom (q ⊗ₘ q) q
  obtain ⟨m, hm⟩ := exists_desc (q ⊗ₘ q) (μ[A] ≫ q) (by
    intro W a b h
    obtain ⟨s, hs⟩ := (rel (a ≫ fst A A) (b ≫ fst A A)).1 (by simpa using h =≫ fst Q Q)
    obtain ⟨t, ht⟩ := (rel (a ≫ snd A A) (b ≫ snd A A)).1 (by simpa using h =≫ snd Q Q)
    rw [← Category.assoc, ← Category.assoc, rel]
    refine ⟨s * t, ?_⟩
    rw [MonObj.mul_eq_mul, comp_mul, comp_mul, hs, ht, mul_comp, _root_.mul_mul_mul_comm])
  obtain ⟨n, hn⟩ := exists_desc q (GrpObj.inv ≫ q) (by
    intro W a b h
    obtain ⟨s, hs⟩ := (rel a b).1 h
    rw [← Category.assoc, ← Category.assoc, rel]
    refine ⟨s⁻¹, ?_⟩
    rw [← Hom.inv_def, ← Hom.inv_def, hs, GrpObj.inv_comp, mul_inv])
  have key : ∀ {W : Over S} (a b : W ⟶ A), lift (a ≫ q) (b ≫ q) ≫ m = (a * b) ≫ q := by
    intro W a b
    rw [← lift_map, Category.assoc, hm, Hom.mul_def, Category.assoc]
  letI : MonObj Q :=
    { one := η[A] ≫ q
      mul := m
      one_mul := by
        rw [← cancel_epi (λ_ Q).inv, ← cancel_epi q]
        have := key (1 : A ⟶ A) (𝟙 A)
        rw [_root_.one_mul] at this
        rw [Iso.inv_hom_id, Category.comp_id]
        refine Eq.trans ?_ (this.trans (Category.id_comp _))
        rw [← Category.assoc, ← Category.assoc]
        congr 1
        ext <;> simp [Hom.one_def]
      mul_one := by
        rw [← cancel_epi (ρ_ Q).inv, ← cancel_epi q]
        have := key (𝟙 A) (1 : A ⟶ A)
        rw [_root_.mul_one] at this
        rw [Iso.inv_hom_id, Category.comp_id]
        refine Eq.trans ?_ (this.trans (Category.id_comp _))
        rw [← Category.assoc, ← Category.assoc]
        congr 1
        ext <;> simp [Hom.one_def]
      mul_assoc := by
        rw [← cancel_epi ((q ⊗ₘ q) ⊗ₘ q)]
        have h1 : ((q ⊗ₘ q) ⊗ₘ q) ≫ m ▷ Q = (μ[A] ▷ A) ≫ (q ⊗ₘ q) := by
          rw [← tensorHom_id, ← tensorHom_id, tensorHom_comp_tensorHom, tensorHom_comp_tensorHom,
            hm, Category.comp_id, Category.id_comp]
        have h2 : ((q ⊗ₘ q) ⊗ₘ q) ≫ (α_ Q Q Q).hom ≫ Q ◁ m =
            (α_ A A A).hom ≫ (A ◁ μ[A]) ≫ (q ⊗ₘ q) := by
          rw [associator_naturality_assoc]
          congr 1
          ext <;> simp [hm]
        rw [reassoc_of% h1, reassoc_of% h2, hm, MonObj.mul_assoc_assoc] }
  have hhom : IsMonHom q := ⟨rfl, hm.symm⟩
  letI : GrpObj Q :=
    { inv := n
      left_inv := by
        rw [← cancel_epi q, comp_lift_assoc, hn, Category.comp_id]
        have := key GrpObj.inv (𝟙 A)
        rw [Category.id_comp] at this
        refine this.trans ?_
        rw [Hom.mul_def, GrpObj.left_inv, comp_toUnit_assoc, Category.assoc]
        rfl
      right_inv := by
        rw [← cancel_epi q, comp_lift_assoc, hn, Category.comp_id]
        have := key (𝟙 A) GrpObj.inv
        rw [Category.id_comp] at this
        refine this.trans ?_
        rw [Hom.mul_def, GrpObj.right_inv, comp_toUnit_assoc, Category.assoc]
        rfl }
  refine ⟨inferInstance, ⟨?_⟩, hhom, ?_⟩
  · rw [← cancel_epi (q ⊗ₘ q), BraidedCategory.braiding_naturality_assoc, ← IsMonHom.mul_hom,
      IsCommMonObj.mul_comm_assoc]
  · have hk : IsPullback (lift (𝟙 H) (toUnit H ≫ η[A])) (toUnit H) (snd H A) η[A] := by
      refine ⟨⟨by simp⟩, ⟨PullbackCone.IsLimit.mk _ (fun s => s.fst ≫ fst H A) ?_ ?_ ?_⟩⟩
      · intro s
        ext
        · simp
        · simp [s.condition, toUnit_unique (toUnit _) s.snd]
      · intro s
        exact toUnit_unique _ _
      · intro s l h1 _
        simp [← h1]
    have := hk.flip.paste_vert hq.flip
    have e : lift (𝟙 H) (toUnit H ≫ η[A]) ≫ ((fst H A ≫ i) * snd H A) = i := by
      simp [comp_mul, ← Hom.one_def]
    rw [e] at this
    exact this.flip

lemma isReduced_of_flat_of_surjective {X Y : Scheme.{0}} (p : X ⟶ Y) [Flat p] [Surjective p]
    [IsReduced X] : IsReduced Y := by
  have (y : Y) : _root_.IsReduced (Y.presheaf.stalk y) := by
    obtain ⟨x, rfl⟩ := p.surjective y
    exact isReduced_of_injective (p.stalkMap x).hom
      (faithfullyFlat_stalkMap_of_flat p x).injective
  exact isReduced_of_isReduced_stalk Y

lemma geometricallyReduced_of_comp {X Y Z : Scheme.{0}} (p : X ⟶ Y) (f : Y ⟶ Z) [Flat p]
    [Surjective p] [h : GeometricallyReduced (p ≫ f)] : GeometricallyReduced f := by
  refine ⟨fun K _ y W a b hW => ?_⟩
  have : IsReduced (pullback p a) :=
    h.geometrically_isReduced y _ _ ((IsPullback.of_hasPullback p a).paste_vert hW)
  exact isReduced_of_flat_of_surjective (pullback.snd p a)

lemma geometricallyConnected_of_comp {X Y Z : Scheme.{0}} (p : X ⟶ Y) (f : Y ⟶ Z)
    [Surjective p] [h : GeometricallyConnected (p ≫ f)] : GeometricallyConnected f := by
  refine ⟨fun K _ y W a b hW => ?_⟩
  have : ConnectedSpace ↥(pullback p a) :=
    h.geometrically_connectedSpace y _ _ ((IsPullback.of_hasPullback p a).paste_vert hW)
  exact (pullback.snd p a).surjective.connectedSpace (pullback.snd p a).continuous

lemma smooth_of_grpObj_of_flat (Q : Over S) [GrpObj Q] [Flat Q.hom]
    [LocallyOfFinitePresentation Q.hom] [GeometricallyReduced Q.hom] : Smooth Q.hom := by
  refine Smooth.of_smooth_fiberToSpecResidueField _ fun y => ?_
  letI : GrpObj (Over.mk Q.hom) := inferInstanceAs (GrpObj Q)
  letI : GrpObj (Over.mk (pullback.snd Q.hom (S.fromSpecResidueField y))) :=
    Over.grpObjMkPullbackSnd
  exact smooth_of_grpObj (K := S.residueField y) (pullback.snd Q.hom (S.fromSpecResidueField y))

end AbelianQuotient

open AbelianQuotient in

theorem quotient_isAbelianScheme_of_quotientScheme :
    (∀ (X S : Scheme.{0}) (f : X ⟶ S), Smooth f → GeometricallyConnected f →
      GeometricallyIntegral f) →
    (∀ (R : Type) [CommRing R] [IsNoetherianRing R] (P : PolAV (Spec (CommRingCat.of R)))
      (H : Over (Spec (CommRingCat.of R))) [GrpObj H] (i : H ⟶ P.A), IsMonHom i → Mono i →
      IsFinite H.hom → Flat H.hom →
      ∃ (Q : Over (Spec (CommRingCat.of R))) (q : P.A ⟶ Q), IsFinite q.left ∧ Flat q.left ∧
        Surjective q.left ∧ IsSeparated Q.hom ∧ LocallyOfFiniteType Q.hom ∧
        IsPullback ((fst H P.A ≫ i) * snd H P.A) (snd H P.A) q q) →
    QuotientSt := by
  intro hint hquot R _ _ P H _ i hi hmono hfin hflat
  obtain ⟨Q, q, h1, h2, h3, h4, h5, hq⟩ := hquot R P H i hi hmono hfin hflat
  have := P.isAb.comm
  obtain ⟨inst, hcomm, hhom, hker⟩ := exists_grpObj i q hq
  refine ⟨Q, inst, ?_, q, hhom, h1, h2, h3, hker⟩
  have hw : q.left ≫ Q.hom = P.A.hom := Over.w q
  have := P.isAb.smooth
  have := P.isAb.proper
  have := P.isAb.geomConnected
  have := hint _ _ P.A.hom P.isAb.smooth P.isAb.geomConnected
  have : Flat (q.left ≫ Q.hom) := by rw [hw]; infer_instance
  have : UniversallyClosed (q.left ≫ Q.hom) := by rw [hw]; infer_instance
  have : GeometricallyReduced (q.left ≫ Q.hom) := by rw [hw]; infer_instance
  have : GeometricallyConnected (q.left ≫ Q.hom) := by rw [hw]; infer_instance
  have := flat_of_comp_of_flat_of_surjective q.left Q.hom
  have := UniversallyClosed.of_comp_surjective q.left Q.hom
  have := geometricallyReduced_of_comp q.left Q.hom
  have : LocallyOfFinitePresentation Q.hom := inferInstance
  exact ⟨hcomm, smooth_of_grpObj_of_flat Q, ⟨⟩, geometricallyConnected_of_comp q.left Q.hom⟩

end GlobalTheory
