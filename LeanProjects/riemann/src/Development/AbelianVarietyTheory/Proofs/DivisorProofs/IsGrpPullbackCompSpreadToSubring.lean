import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MorphismsEqSpreadToSubring
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsPullDegEquivApply
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GrpMulSpread

attribute [local instance] Over.cartesianMonoidalCategory

theorem isPullback_pullbackMap {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} {f : S' ⟶ S}
    {F : G'.left ⟶ G.left} (cart : IsPullback F G'.hom G.hom f) :
    IsPullback (pullback.map G'.hom G'.hom G.hom G.hom F F f cart.w.symm cart.w.symm)
      (G' ⊗ G').hom (G ⊗ G).hom f := by
  have p : IsPullback (pullback.snd G.hom G.hom) (pullback.fst G.hom G.hom) G.hom G.hom :=
    (IsPullback.of_hasPullback G.hom G.hom).flip
  have p' : IsPullback (pullback.snd G'.hom G'.hom) (pullback.fst G'.hom G'.hom) G'.hom G'.hom :=
    (IsPullback.of_hasPullback G'.hom G'.hom).flip
  have c₁ : pullback.map G'.hom G'.hom G.hom G.hom F F f cart.w.symm cart.w.symm ≫ pullback.fst G.hom G.hom =
      pullback.fst G'.hom G'.hom ≫ F := pullback.lift_fst _ _ _
  have c₂ : pullback.map G'.hom G'.hom G.hom G.hom F F f cart.w.symm cart.w.symm ≫ pullback.snd G.hom G.hom =
      pullback.snd G'.hom G'.hom ≫ F := pullback.lift_snd _ _ _
  have q : IsPullback (pullback.map G'.hom G'.hom G.hom G.hom F F f cart.w.symm cart.w.symm ≫
      pullback.snd G.hom G.hom) (pullback.fst G'.hom G'.hom) G.hom (F ≫ G.hom) := by
    rw [c₂, cart.w]
    exact p'.paste_horiz cart
  exact (IsPullback.of_right q c₁ p).paste_vert cart

theorem pullbackMap_comp {S₁ S₀ Y : Scheme.{0}} {A₁ : Over S₁} {D : Over S₀} {U : Over Y} {k : S₁ ⟶ S₀}
    {h₀ : S₀ ⟶ Y} {φ : A₁.left ⟶ D.left} {ψ : D.left ⟶ U.left} (hφ : IsPullback φ A₁.hom D.hom k)
    (cart : IsPullback ψ D.hom U.hom h₀) :
    pullback.map A₁.hom A₁.hom D.hom D.hom φ φ k hφ.w.symm hφ.w.symm ≫
        pullback.map D.hom D.hom U.hom U.hom ψ ψ h₀ cart.w.symm cart.w.symm =
      pullback.map A₁.hom A₁.hom U.hom U.hom (φ ≫ ψ) (φ ≫ ψ) (k ≫ h₀)
        (hφ.paste_horiz cart).w.symm (hφ.paste_horiz cart).w.symm := by
  apply pullback.hom_ext <;> simp only [Category.assoc, pullback.map, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc]

theorem isGrpPullback_comp_spread_to_subring :
    ∀ (g n : ℕ) (B : Type) [CommRing B] (ζ : B) (S : Type) [CommRing S] (R₀ : Subring S) (s₀ : Sp R₀ ⟶ Sp B) (d₀ : SiegPre g n ζ s₀) (Y : Scheme.{0}) (sY : Y ⟶ Sp B) (u : SiegPre g n ζ sY) (h₀ : Sp R₀ ⟶ Y) (ψ : d₀.A.left ⟶ u.A.left) (sE : Sp S ⟶ Sp B) (e : SiegPre g n ζ sE) (j : e.A.left ⟶ d₀.A.left), IsPullback ψ d₀.A.hom u.A.hom h₀ → IsGrpPullback e.A d₀.A (spMap R₀.subtype) j → IsGrpPullback e.A u.A (spMap R₀.subtype ≫ h₀) (j ≫ ψ) → ∃ F : Finset S, ∀ (R₁ : Subring S) (hle : R₀ ≤ R₁), (F : Set S) ⊆ R₁ → ∀ (A₁ : Over (Sp R₁)) [GrpObj A₁] (φ₁ : A₁.left ⟶ d₀.A.left), IsGrpPullback A₁ d₀.A (spMap (Subring.inclusion hle)) φ₁ → IsGrpPullback A₁ u.A (spMap (Subring.inclusion hle) ≫ h₀) (φ₁ ≫ ψ) := by
  intro g n B _ ζ S _ R₀ s₀ d₀ Y sY u h₀ ψ sE e j cart hj hjψ
  haveI := d₀.ab.proper
  haveI := u.ab.smooth
  haveI hqc : QuasiCompact (pullback.fst d₀.A.hom d₀.A.hom ≫ d₀.A.hom) := inferInstance
  haveI hlft : LocallyOfFiniteType (pullback.snd u.A.hom h₀) := inferInstance
  set f₀ : pullback d₀.A.hom d₀.A.hom ⟶ Sp R₀ := pullback.fst d₀.A.hom d₀.A.hom ≫ d₀.A.hom with hf₀
  have hμd : (μ[d₀.A]).left ≫ d₀.A.hom = f₀ := Over.w μ[d₀.A]
  have hμu : (μ[u.A]).left ≫ u.A.hom = pullback.fst u.A.hom u.A.hom ≫ u.A.hom := Over.w μ[u.A]
  set mψ := pullback.map d₀.A.hom d₀.A.hom u.A.hom u.A.hom ψ ψ h₀ cart.w.symm cart.w.symm with hmψ
  have w₁ : ((μ[d₀.A]).left ≫ ψ) ≫ u.A.hom = f₀ ≫ h₀ := by
    rw [Category.assoc, cart.w, ← Category.assoc, hμd]
  have w₂ : (mψ ≫ (μ[u.A]).left) ≫ u.A.hom = f₀ ≫ h₀ := by
    rw [Category.assoc, hμu, ← Category.assoc, hmψ, pullback.lift_fst, Category.assoc, cart.w, hf₀,
      Category.assoc]
  let a : pullback d₀.A.hom d₀.A.hom ⟶ pullback u.A.hom h₀ := pullback.lift _ _ w₁
  let b : pullback d₀.A.hom d₀.A.hom ⟶ pullback u.A.hom h₀ := pullback.lift _ _ w₂
  have key : ∀ {S₁ : Scheme.{0}} {A₁ : Over S₁} [GrpObj A₁] {k : S₁ ⟶ Sp R₀} {φ : A₁.left ⟶ d₀.A.left}
      (hφ : IsPullback φ A₁.hom d₀.A.hom k),
      pullback.map A₁.hom A₁.hom d₀.A.hom d₀.A.hom φ φ k hφ.w.symm hφ.w.symm ≫ mψ =
        pullback.map A₁.hom A₁.hom u.A.hom u.A.hom (φ ≫ ψ) (φ ≫ ψ) (k ≫ h₀)
          (hφ.paste_horiz cart).w.symm (hφ.paste_horiz cart).w.symm := by
    intro S₁ A₁ _ k φ hφ
    exact pullbackMap_comp hφ cart
  have hab : pullback.map e.A.hom e.A.hom d₀.A.hom d₀.A.hom j j (spMap R₀.subtype) hj.1.w.symm hj.1.w.symm ≫ a =
      pullback.map e.A.hom e.A.hom d₀.A.hom d₀.A.hom j j (spMap R₀.subtype) hj.1.w.symm hj.1.w.symm ≫ b := by
    have m₁ := (GlobalTheory.PullDegCompare.isGrpPullback_iff hj.1).1 hj
    have m₂ := (GlobalTheory.PullDegCompare.isGrpPullback_iff hjψ.1).1 hjψ
    apply pullback.hom_ext
    · simp only [a, b, Category.assoc, pullback.lift_fst]
      rw [← Category.assoc, ← m₁, Category.assoc, m₂]
      exact (congrArg (· ≫ (μ[u.A]).left) (key hj.1).symm).trans (Category.assoc _ _ _)
    · simp only [a, b, Category.assoc, pullback.lift_snd]
  obtain ⟨F, hF⟩ := GlobalTheory.morphisms_eq_spread_to_subring S R₀ (pullback e.A.hom e.A.hom)
    (pullback d₀.A.hom d₀.A.hom) (pullback u.A.hom h₀) (e.A ⊗ e.A).hom f₀ (pullback.snd u.A.hom h₀)
    (pullback.map e.A.hom e.A.hom d₀.A.hom d₀.A.hom j j (spMap R₀.subtype) hj.1.w.symm hj.1.w.symm) a b
    (isPullback_pullbackMap hj.1) (pullback.lift_snd _ _ _) (pullback.lift_snd _ _ _) hab
  refine ⟨F, fun R₁ hle hFs A₁ _ φ₁ hφ ↦ ?_⟩
  have cart₁ := hφ.1.paste_horiz cart
  refine (GlobalTheory.PullDegCompare.isGrpPullback_iff cart₁).2 ?_
  have H := hF R₁ hle hFs (pullback A₁.hom A₁.hom) (A₁ ⊗ A₁).hom
    (pullback.map A₁.hom A₁.hom d₀.A.hom d₀.A.hom φ₁ φ₁ _ hφ.1.w.symm hφ.1.w.symm)
    (isPullback_pullbackMap hφ.1)
  have H' := congrArg (· ≫ pullback.fst u.A.hom h₀) H
  simp only [a, b, Category.assoc, pullback.lift_fst] at H'
  have m := (GlobalTheory.PullDegCompare.isGrpPullback_iff hφ.1).1 hφ
  rw [← Category.assoc, m, Category.assoc, H']
  exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ (μ[u.A]).left) (key hφ.1))

end GlobalTheory.GrpMulSpread
