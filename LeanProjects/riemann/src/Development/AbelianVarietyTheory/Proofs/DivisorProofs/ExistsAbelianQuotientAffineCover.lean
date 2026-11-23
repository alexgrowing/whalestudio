import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ChainOfKernelsUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuotientAbelianSchemeFiniteFlatSubgroup
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbQuotientLocal

theorem exists_quotient_of_openImmersion (S : Scheme.{0}) [IsLocallyNoetherian S] (R : CommRingCat.{0})
    (f : Spec R ⟶ S) [IsOpenImmersion f] (A : Over S) [GrpObj A] (H : Over S) [GrpObj H] (i : H ⟶ A)
    (hA : IsAbelianScheme A) (hi : IsMonHom i) (hm : Mono i) (hf : IsFinite H.hom) (hfl : Flat H.hom) :
    ∃ (B : Over (Spec R)) (_ : GrpObj B) (q : (Over.pullback f).obj A ⟶ B),
      IsAbelianScheme B ∧ IsMonHom q ∧ IsFinite q.left ∧ Flat q.left ∧ Surjective q.left ∧
      IsPullback ((fst ((Over.pullback f).obj H) ((Over.pullback f).obj A) ≫
          (Over.pullback f).map i) * snd ((Over.pullback f).obj H) ((Over.pullback f).obj A))
        (snd ((Over.pullback f).obj H) ((Over.pullback f).obj A)) q q := by
  have hN : IsLocallyNoetherian (Spec R) := isLocallyNoetherian_of_isOpenImmersion f
  have : IsNoetherianRing R := (isLocallyNoetherian_Spec (R := R)).1 hN
  have hA' : IsAbelianScheme ((Over.pullback f).obj A) := GlobalTheory.isAbelianScheme_pullback_obj f A hA
  have hi' : IsMonHom ((Over.pullback f).map i) := inferInstance
  have hm' : Mono ((Over.pullback f).map i) := inferInstance
  have hf' : IsFinite ((Over.pullback f).obj H).hom := by
    show IsFinite (pullback.snd H.hom f)
    infer_instance
  have hfl' : Flat ((Over.pullback f).obj H).hom := by
    show Flat (pullback.snd H.hom f)
    infer_instance
  obtain ⟨B, hB, q, -, h1, h2, h3, h4, h5, -, h6⟩ :=
    GlobalTheory.AbQuotientAny.exists_quotient_abelianScheme R ((Over.pullback f).obj A)
      ((Over.pullback f).obj H) ((Over.pullback f).map i) hA' hi' hm' hf' hfl'
  exact ⟨B, hB, q, h1, h2, h3, h4, h5, h6⟩

theorem exists_local_quotient : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A : Over S) [GrpObj A] (H : Over S) [GrpObj H] (i : H ⟶ A),
    IsAbelianScheme A → IsMonHom i → Mono i → IsFinite H.hom → Flat H.hom → ∀ j : S.affineCover.I₀,
    ∃ (B : Over (S.affineCover.X j)) (_ : GrpObj B) (q : (Over.pullback (S.affineCover.f j)).obj A ⟶ B),
      IsAbelianScheme B ∧ IsMonHom q ∧ IsFinite q.left ∧ Flat q.left ∧ Surjective q.left ∧
      IsPullback ((fst ((Over.pullback (S.affineCover.f j)).obj H) ((Over.pullback (S.affineCover.f j)).obj A) ≫
          (Over.pullback (S.affineCover.f j)).map i) *
          snd ((Over.pullback (S.affineCover.f j)).obj H) ((Over.pullback (S.affineCover.f j)).obj A))
        (snd ((Over.pullback (S.affineCover.f j)).obj H) ((Over.pullback (S.affineCover.f j)).obj A)) q q := by
  intro S _ A _ H _ i hA hi hm hf hfl j
  haveI : IsOpenImmersion (S.affineCover.f j) := S.affineCover.map_prop j
  exact @exists_quotient_of_openImmersion S _ _ (S.affineCover.f j) this A _ H _ i hA hi hm hf hfl

end GlobalTheory.AbQuotientLocal
