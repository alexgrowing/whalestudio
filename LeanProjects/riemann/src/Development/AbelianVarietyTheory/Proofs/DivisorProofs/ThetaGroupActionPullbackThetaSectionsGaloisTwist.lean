import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenCastIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.MixCore
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Conj

namespace GlobalTheory.Mum.Conj

variable {R : Type} [CommRing R] [IsDomain R]

theorem twK_comp_eq_id {σ τ : Kb R →ₐ[FractionRing R] Kb R} (h : σ.comp τ = AlgHom.id _ _) :
    twK σ ≫ twK τ = 𝟙 _ := by
  apply Over.OverMorphism.ext
  show spMap σ.toRingHom ≫ spMap τ.toRingHom = 𝟙 _
  rw [spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have e : σ.toRingHom.comp τ.toRingHom = RingHom.id _ := congrArg AlgHom.toRingHom h
  rw [e]
  exact Spec.map_id _

theorem mTw_comp_eq_id (A : PolAV (Sp (FractionRing R))) {σ τ : Kb R →ₐ[FractionRing R] Kb R}
    (h : σ.comp τ = AlgHom.id _ _) : mTw A σ ≫ mTw A τ = 𝟙 _ := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, mTw_fst, ← Category.assoc, mTw_fst, Category.assoc, twK_comp_eq_id h, Category.comp_id,
      Category.id_comp]
  · rw [Category.assoc, mTw_snd, mTw_snd, Category.id_comp]

theorem mTw_translT (A : PolAV (Sp (FractionRing R))) {σ τ : Kb R →ₐ[FractionRing R] Kb R}
    (h : σ.comp τ = AlgHom.id _ _) (x : TFK (R := R) (Kb R) ⟶ A.A) :
    mTw A σ ≫ translT A.A (twK τ ≫ x) = translT A.A x ≫ mTw A σ := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [translT]
    rw [Category.assoc, Category.assoc, lift_fst, mTw_fst, ← Category.assoc, lift_fst]
  · simp only [translT]
    rw [Category.assoc, Category.assoc, lift_snd, mTw_snd, lift_snd]
    simp only [translPt]
    rw [← Category.assoc, comp_lift, ← Category.assoc (mTw A σ), mTw_fst, mTw_snd, Category.assoc,
      ← Category.assoc (twK σ), twK_comp_eq_id h, Category.id_comp]

theorem isActOf_secTw : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) (N : ℕ) (σ τ : Kb R →ₐ[FractionRing R] Kb R), σ.comp τ = AlgHom.id _ _ → ∀ (θ : ThetaGrp A.A A.L (N : ℤ) (TFK (R := R) (Kb R))) (a b : SecK A.L (snd (TFK (R := R) (Kb R)) A.A).left N), IsActOf A.A A.L N (thTw A N τ θ) a b → IsActOf A.A A.L N θ (secTw A N σ a) (secTw A N σ b) := by
  intro R _ _ A N σ τ hστ θ a b H
  refine twist_of_val A.isLB θ.isGen fun z J hJ => ?_
  have e1 : (𝟙 _ ≫ (mTw A σ).left) ≫ (mTw A τ).left = 𝟙 _ := by
    rw [Category.id_comp, ← Over.comp_left, mTw_comp_eq_id A hστ, Over.id_left]
  have e2 : (𝟙 _ ≫ (mTw A σ).left) ≫ (translT A.A (twK τ ≫ θ.pt)).left =
      (𝟙 _ ≫ (translT A.A θ.pt).left) ≫ (mTw A σ).left := by
    simp only [Category.id_comp, ← Over.comp_left, mTw_translT A hστ]
  have hv : val (thTw A N τ θ).φ (𝟙 _ ≫ (mTw A σ).left) z J = val θ.φ (𝟙 _) z J :=
    (val_genCast _ _ _ z J).trans ((val_pull hJ _ _ _).trans (congrArg (fun r => val θ.φ r z J) e1))
  have H' := twist_val H (𝟙 _ ≫ (mTw A σ).left) z hJ
  rw [hv] at H'
  have hb : sval (secTw A N σ b) (𝟙 _) z J = sval b (𝟙 _ ≫ (mTw A σ).left) z J :=
    GlobalTheory.FieldBaseChange.sval_pullOver _ _ b _ hJ
  have ha : sval (secTw A N σ a) (𝟙 _ ≫ (translT A.A θ.pt).left) z J =
      sval a ((𝟙 _ ≫ (translT A.A θ.pt).left) ≫ (mTw A σ).left) z J :=
    GlobalTheory.FieldBaseChange.sval_pullOver _ _ a _ hJ
  refine hb.trans (H'.trans ?_)
  rw [ha]
  exact congrArg (fun r => (val θ.φ (𝟙 _) z J).val * sval a r z J) e2

end GlobalTheory.Mum.Conj
