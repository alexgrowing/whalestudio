import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.IsSquareDeterminantComparison
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IndepOnEmpty
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

noncomputable section
namespace GlobalTheory.RelBasis

variable {X Y T Y' T' : Scheme.{0}} {L : LB X} {t : ℤ} {N : ℕ}

theorem affine_gs_appLE {Z : Scheme.{0}} (q : Y ⟶ X) (U : X.Opens) (W : Y.Opens) (e : W ≤ q ⁻¹ᵁ U) (r : Z ⟶ Y) (z : Z)
    (hz : r z ∈ W) (f : Γ(X, U)) : gs r z W ((q.appLE U W e).hom f) = gs (r ≫ q) z U f :=
  (gs_res r z e hz _).trans (gs_pull r q z U (e hz) f)

theorem affine_comb (b : Fin N → LB.Sec (pw L t)) (p₁ : Y ⟶ T) (p₂ : Y ⟶ X) (W : T.Opens)
    (j : Y' ⟶ Y) (p₁' : Y' ⟶ T') (g : T' ⟶ T) (w : j ≫ p₁ = p₁' ≫ g) (e : ⊤ ≤ g ⁻¹ᵁ W)
    (c : Fin N → Γ(T, W)) (z : Y') (i : L.ι) (h₂ : p₂ (j z) ∈ L.U i) :
    comb b p₁' (j ≫ p₂) ⊤ (fun k => (g.appLE W ⊤ e).hom (c k)) z i =
      (j.stalkMap z).hom (comb b p₁ p₂ W c (j z) i) := by
  have h₁ : p₁ (j z) ∈ W := by
    have : (j ≫ p₁) z ∈ W := by rw [w]; exact e (show p₁' z ∈ (⊤ : T'.Opens) from trivial)
    exact this
  rw [← comb_comp b j p₁ p₂ W c z i h₁ h₂, comb, comb]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [affine_gs_appLE g W ⊤ e p₁' z trivial, w]

theorem affine_transfer (b : Fin N → LB.Sec (pw L t)) (p₁ : Y ⟶ T) (p₂ : Y ⟶ X) (W : T.Opens)
    (j : Y' ⟶ Y) (p₁' : Y' ⟶ T') (g : T' ⟶ T) [IsOpenImmersion g] (sq : IsPullback j p₁' p₁ g)
    (hr : Set.range g = W) (e : ⊤ ≤ g ⁻¹ᵁ W) (hb : Function.Bijective (g.appLE W ⊤ e).hom)
    (h₁ : IndepOn b p₁' (j ≫ p₂) ⊤) (h₂ : SpanOn b p₁' (j ≫ p₂) ⊤) :
    IndepOn b p₁ p₂ W ∧ SpanOn b p₁ p₂ W := by
  have hj : IsOpenImmersion j := MorphismProperty.of_isPullback (P := @IsOpenImmersion) sq.flip inferInstance
  have hW : ∀ z : Y', p₁ (j z) ∈ W := fun z => by
    have : (j ≫ p₁) z ∈ W := by rw [sq.w]; exact e (show p₁' z ∈ (⊤ : T'.Opens) from trivial)
    exact this
  refine ⟨fun c hc => ?_, fun σ hσ => ?_⟩
  · have := h₁ (fun k => (g.appLE W ⊤ e).hom (c k)) (fun z i _ hz => by
      rw [affine_comb b p₁ p₂ W j p₁' g sq.w e c z i hz, hc (j z) i (hW z) hz, map_zero])
    funext k
    apply hb.1
    rw [Pi.zero_apply, map_zero]
    exact congrFun this k
  · have le : ∀ i, p₁' ⁻¹ᵁ ⊤ ⊓ (j ≫ p₂) ⁻¹ᵁ L.U i ≤ j ⁻¹ᵁ (p₁ ⁻¹ᵁ W ⊓ p₂ ⁻¹ᵁ L.U i) :=
      fun i z hz => ⟨hW z, hz.2⟩
    have key : ∀ (z : Y') (i : L.ι), p₂ (j z) ∈ L.U i →
        gs (𝟙 Y') z _ ((j.appLE _ _ (le i)).hom (σ i)) = (j.stalkMap z).hom (gs (𝟙 Y) (j z) _ (σ i)) := by
      intro z i hz
      rw [affine_gs_appLE j _ _ (le i) (𝟙 Y') z ⟨trivial, hz⟩, Category.id_comp,
        ← gs_comp j (𝟙 Y) z (p₁ ⁻¹ᵁ W ⊓ p₂ ⁻¹ᵁ L.U i) ⟨hW z, hz⟩, Category.comp_id]
    obtain ⟨c', hc'⟩ := h₂ (fun i => (j.appLE _ _ (le i)).hom (σ i)) (fun z i i' _ hi hi' => by
      rw [key z i hi, key z i' hi', hσ (j z) i i' (hW z) hi hi', map_mul]
      congr 1
      have : gm (j ≫ p₂) z (L.U i ⊓ L.U i') (L.g i i') =
          Units.map (j.stalkMap z).hom.toMonoidHom (gm p₂ (j z) (L.U i ⊓ L.U i') (L.g i i')) := by
        apply Units.ext
        rw [← gs_unit (j ≫ p₂) z (L.U i ⊓ L.U i') ⟨hi, hi'⟩, gs_comp j p₂ z (L.U i ⊓ L.U i') ⟨hi, hi'⟩,
          gs_unit p₂ (j z) (L.U i ⊓ L.U i') ⟨hi, hi'⟩]
        rfl
      rw [this, ← map_zpow (Units.map (j.stalkMap z).hom.toMonoidHom)]
      rfl)
    choose c hc using fun k => hb.2 (c' k)
    refine ⟨c, fun y i hy hi => ?_⟩
    obtain ⟨s, hs⟩ : p₁ y ∈ Set.range g := by rw [hr]; exact hy
    obtain ⟨z, rfl, -⟩ := Scheme.exists_preimage_of_isPullback sq y s hs.symm
    apply (ConcreteCategory.bijective_of_isIso (j.stalkMap z)).1
    have := hc' z i trivial hi
    rw [key z i hi, ← funext hc, affine_comb b p₁ p₂ W j p₁' g sq.w e c z i hi] at this
    exact this

theorem indepOn_spanOn_of_affine : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (p : X ⟶ Sp R) (L : LB X) (t : ℤ) (N : ℕ) (b : Fin N → LB.Sec (pw L t)), (∀ (R' : Type) [CommRing R'] (f : R →+* R'), ∃ (Y : Scheme.{0}) (p₁ : Y ⟶ Sp R') (p₂ : Y ⟶ X), IsPullback p₂ p₁ p (spMap f) ∧ GlobalTheory.RelBasis.IndepOn b p₁ p₂ ⊤ ∧ GlobalTheory.RelBasis.SpanOn b p₁ p₂ ⊤) → ∀ (T Y : Scheme.{0}) (q : T ⟶ Sp R) (p₁ : Y ⟶ T) (p₂ : Y ⟶ X), IsPullback p₂ p₁ p q → ∀ W : T.Opens, IsAffineOpen W → GlobalTheory.RelBasis.IndepOn b p₁ p₂ W ∧ GlobalTheory.RelBasis.SpanOn b p₁ p₂ W := by
  intro R _ X p L t N b H T Y q p₁ p₂ sq W hW
  obtain ⟨Y', p₁', p₂', sq', h₁, h₂⟩ := H Γ(T, W) (Spec.preimage (hW.fromSpec ≫ q)).hom
  have hf : spMap (Spec.preimage (hW.fromSpec ≫ q)).hom = hW.fromSpec ≫ q := Spec.map_preimage _
  rw [hf] at sq'
  let j : Y' ⟶ Y := sq.lift p₂' (p₁' ≫ hW.fromSpec) (by rw [sq'.w, Category.assoc])
  have e₂ : j ≫ p₂ = p₂' := sq.lift_fst _ _ _
  have e₁ : j ≫ p₁ = p₁' ≫ hW.fromSpec := sq.lift_snd _ _ _
  rw [← e₂] at sq' h₁ h₂
  have sq'' : IsPullback j p₁' p₁ hW.fromSpec := IsPullback.of_right (by simpa using sq') e₁ sq
  have e : ⊤ ≤ hW.fromSpec ⁻¹ᵁ W := hW.fromSpec_preimage_self.ge
  refine affine_transfer b p₁ p₂ W j p₁' hW.fromSpec sq'' hW.range_fromSpec e ?_ h₁ h₂
  have : hW.fromSpec.appLE W ⊤ e = (Scheme.ΓSpecIso Γ(T, W)).inv := by
    rw [Scheme.Hom.appLE, hW.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
    exact (congrArg _ ((congrArg _ (Subsingleton.elim _ _)).trans (CategoryTheory.Functor.map_id _ _))).trans
      (Category.comp_id _)
  rw [this]
  exact ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso Γ(T, W)).inv

end GlobalTheory.RelBasis
