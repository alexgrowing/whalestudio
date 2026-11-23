import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PhiAt
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TanEigInt

theorem isEigV_of_tanPull_mem : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} (T : CDVR) (io : c.F →+* T.Fr), letI := io.toAlgebra; ∀ (x : Sp T.V ⟶ Y.X) (x' : Sp T.Fr ⟶ Y.X) (e : spMap (algebraMap T.V T.Fr) ≫ x = x'), Function.Injective (GlobalTheory.FlagMod.tanPull (G := Y.t.G) (algebraMap T.V T.Fr) e) → ∀ (G : SAB H (Sp T.V)) (ψ : SABMap G Y.t x) (τ : E →+* ℂ) (w : epsOver T.V T.V ⟶ G.G) (v : ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM x Y.t.G), (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv v).left = w.left ≫ ψ.φ → GlobalTheory.FlagMod.tanPull (algebraMap T.V T.Fr) e v ∈ GlobalTheory.FlagMod.eigLie c x' τ → IsEigV c io G τ w := by
  intro E _ _ _ H Dw l Xo c O _ β Y T io x x' e hinj G ψ τ w v hv hmem a z hz
  have h1 : ReciprocityTheory.ChartRestriction.G.PullbackSections.actR Y.t.act a v = z • v := by
    apply hinj
    rw [GlobalTheory.FlagMod.tanPull_actR, map_smulₛₗ, hmem a, hz]
    rfl
  have h2 : (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv v).left ≫ (Y.t.act.act a).left =
      spMap (epsMul z) ≫ (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv v).left :=
    congrArg (fun u => (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv u).left) h1
  have hc : (epsMul z).comp ((algebraMap T.V (DualNumber T.V)).comp (algebraMap T.V T.V)) =
      (algebraMap T.V (DualNumber T.V)).comp (algebraMap T.V T.V) :=
    RingHom.ext fun r => by ext <;> simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]
  apply ψ.cart.1.hom_ext
  · rw [Over.comp_left, Category.assoc, ψ.act a, ← Category.assoc, ← hv, h2, hv, Category.assoc]
  · rw [Over.comp_left, Category.assoc, Over.w, Over.w, Category.assoc, Over.w]
    show spMap _ = spMap (epsMul z) ≫ spMap _
    rw [spMap_comp', hc]

end GlobalTheory.TanEigInt
