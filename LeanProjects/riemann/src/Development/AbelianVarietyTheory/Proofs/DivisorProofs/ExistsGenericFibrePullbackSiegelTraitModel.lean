import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotOrdGeOfNotMem
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegPull
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.Poinc.GenFibre

theorem exists_generic_pullback : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (T : Trait F) (W : Type) [CommRing W] [IsDomain W] (f : T.V →+* W) (fK : FractionRing T.V →+* FractionRing W), (∀ a, fK (algebraMap T.V _ a) = algebraMap W _ (f a)) → ∃ κ : ((Over.pullback (jK W)).obj ((Over.pullback (spMap f)).obj T.G)).left ⟶ T.A.A.left, IsGrpPullback ((Over.pullback (jK W)).obj ((Over.pullback (spMap f)).obj T.G)) T.A.A (spMap fK) κ ∧ κ ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK T.V) = pullback.fst ((Over.pullback (spMap f)).obj T.G).hom (jK W) ≫ pullback.fst T.G.hom (spMap f) := by
  intro g n o _ ζ F T W _ _ f fK hfK
  have hsq : spMap fK ≫ jK T.V = jK W ≫ spMap f := by
    have h : fK.comp (algebraMap T.V (FractionRing T.V)) = (algebraMap W (FractionRing W)).comp f := RingHom.ext hfK
    change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, h]
  have gB := ((isGrpPullback_pullback ((Over.pullback (spMap f)).obj T.G) (jK W)).comp
    (isGrpPullback_pullback T.G (spMap f))).congr hsq.symm rfl
  have he := isGrpPullback_pullback T.G (jK T.V)
  set B := (Over.pullback (jK W)).obj ((Over.pullback (spMap f)).obj T.G)
  have w : (pullback.fst ((Over.pullback (spMap f)).obj T.G).hom (jK W) ≫ pullback.fst T.G.hom (spMap f)) ≫ T.G.hom =
      (B.hom ≫ spMap fK) ≫ jK T.V := by
    rw [Category.assoc B.hom]; exact gB.1.w
  obtain ⟨α, h₁, h₂⟩ : ∃ α : B.left ⟶ ((Over.pullback (jK T.V)).obj T.G).left,
      α ≫ pullback.fst T.G.hom (jK T.V) =
        pullback.fst ((Over.pullback (spMap f)).obj T.G).hom (jK W) ≫ pullback.fst T.G.hom (spMap f) ∧
      α ≫ ((Over.pullback (jK T.V)).obj T.G).hom = B.hom ≫ spMap fK :=
    ⟨he.1.lift _ _ w, he.1.lift_fst _ _ _, he.1.lift_snd _ _ _⟩
  have gα := he.cancel (gB.congr rfl h₁.symm) h₂
  haveI := T.U.gen_hom
  refine ⟨α ≫ T.U.gen.hom.left, (gα.comp (isGrpPullback_of_iso T.U.gen)).congr (Category.comp_id _) rfl, ?_⟩
  rw [Category.assoc, ← Category.assoc T.U.gen.hom.left, ← Over.comp_left, Iso.hom_inv_id, Over.id_left, Category.id_comp]
  exact h₁

end GlobalTheory.Poinc.GenFibre
