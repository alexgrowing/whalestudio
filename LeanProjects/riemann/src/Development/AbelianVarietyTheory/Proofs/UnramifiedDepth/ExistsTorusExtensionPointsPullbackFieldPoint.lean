import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CubWeilOfInjective
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CubicalBundlePairingCompatiblePullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj

namespace GlobalTheory.AlphaPair

theorem exists_pullEquiv {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' : Scheme.{0}}
    {f : S' ⟶ S} {t : SAB H S} {t' : SAB H S'} (m : SABMap t' t f) (n : ℕ) {Y : Scheme.{0}} (a : Y ⟶ S')
    (u : Y ⟶ S) (hu : a ≫ f = u) :
    ∃ e : (Over.mk u ⟶ t.G) ≃* (Over.mk a ⟶ t'.G), (∀ x, (e x).left ≫ m.cm.F = x.left) ∧
      ∀ x y, CubWeil t.cub n x y 1 → CubWeil t'.cub n (e x) (e y) 1 := by
  subst hu
  have hw : m.cm.F ≫ t.G.hom = t'.G.hom ≫ f := m.cart.1.w
  have mul : ∀ (T : Over S') (x y : T ⟶ t'.G), Out.toBase hw (x * y) = Out.toBase hw x * Out.toBase hw y :=
    fun T x y => Over.OverMorphism.ext (m.cart.2 T x y (Out.toBase hw x) (Out.toBase hw y) rfl rfl).symm
  let β : (Over.mk a ⟶ t'.G) →* (Over.mk (a ≫ f) ⟶ t.G) := GlobalTheory.UU.toBaseHom mul (Over.mk a)
  have hβ : Function.Bijective β := by
    refine ⟨fun x y e => Over.OverMorphism.ext
      (m.cart.1.hom_ext (congrArg (fun q => q.left) e) (by rw [Over.w, Over.w])), fun x => ?_⟩
    exact ⟨Over.homMk (m.cart.1.lift x.left a (Over.w x)) (m.cart.1.lift_snd _ _ _),
      Over.OverMorphism.ext (m.cart.1.lift_fst _ _ _)⟩
  let e := (MulEquiv.ofBijective β hβ).symm
  have he : ∀ x, β (e x) = x := fun x => (MulEquiv.ofBijective β hβ).apply_symm_apply x
  refine ⟨e, fun x => congrArg (fun q => q.left) (he x), fun x y h => ?_⟩
  obtain ⟨ζ, hζ, -⟩ := GlobalTheory.UU.existsUnique_cubWeil t'.cub (N := n) (x := e x) (y := e y)
    (by rw [← map_pow, h.1, map_one]) (by rw [← map_pow, h.2.1, map_one])
  have h' : CubWeil t.cub n (β (e x)) (β (e y)) ζ :=
    GlobalTheory.UU.cubWeil_of_isPullCubical S S' f t.G t'.G m.cm hw mul _ _ t.cub t'.cub m.lin n _ _ _ ζ hζ
  rw [he, he] at h'
  obtain rfl : ζ = 1 := h'.unique h
  exact hζ

theorem exists_isTorExt_pull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S S' : Scheme.{0}) (f : S' ⟶ S) (t : SAB H S) (t' : SAB H S') (_ : SABMap t' t f) (Ω : Type) [Field Ω] (s : Sp Ω ⟶ S) (s' : Sp Ω ⟶ S'), s' ≫ f = s → ∀ n : ℕ, ∃ (τ : PtHom s s' t.G t'.G) (io : TorHom s t.G PUnit), IsTorExt s s' t.G t'.G PUnit τ io ∧ Transfer n t.cub t'.cub τ := by
  intro E _ _ _ H S S' f t t' m Ω _ s s' hs n
  have key : ∀ (A : Type) [CommRing A] [Algebra Ω A], ∃ e : (overAt s A ⟶ t.G) ≃* (overAt s' A ⟶ t'.G),
      (∀ x, (e x).left ≫ m.cm.F = x.left) ∧ ∀ x y, CubWeil t.cub n x y 1 → CubWeil t'.cub n (e x) (e y) 1 :=
    fun A _ _ => exists_pullEquiv m n _ _ (by rw [Category.assoc, hs])
  choose e he hc using key
  have nat : ∀ (A A' : Type) [CommRing A] [Algebra Ω A] [CommRing A'] [Algebra Ω A'] (g : A →ₐ[Ω] A')
      (x : overAt s A ⟶ t.G), e A' (homAt s g ≫ x) = homAt s' g ≫ e A x := by
    intro A A' _ _ _ _ g x
    refine Over.OverMorphism.ext (m.cart.1.hom_ext ?_ (by rw [Over.w, Over.w]))
    rw [he, Over.comp_left, Over.comp_left, Category.assoc, he]
    rfl
  refine ⟨fun A _ _ => (e A).toMonoidHom, fun A _ _ => 1, ⟨nat, ?_, ?_, ?_, ?_⟩, fun A _ _ => hc A⟩
  · intro A A' _ _ _ _ g χ
    exact (MonObj.comp_one _).symm
  · intro A _ _ χ χ' _
    exact MonoidHom.ext fun x => by rw [Subsingleton.elim x 1, map_one, map_one]
  · intro A _ _ x
    exact (e A).map_eq_one_iff.trans ⟨fun h => ⟨1, h.symm⟩, fun ⟨_, h⟩ => h.symm⟩
  · intro A _ _ π _ y hy
    refine ⟨(e A).symm y, (e Ω).map_eq_one_iff.1 ?_, (e A).apply_symm_apply y⟩
    rw [nat, (e A).apply_symm_apply, hy]

end GlobalTheory.AlphaPair
