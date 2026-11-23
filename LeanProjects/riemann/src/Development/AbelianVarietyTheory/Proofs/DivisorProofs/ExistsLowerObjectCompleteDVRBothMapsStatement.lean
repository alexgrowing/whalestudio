import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLowerObjectCompleteDVRBothMaps
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lowerObject_completeDVR_both_maps : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : MonoFam Xo c φ R) (Cn : Canon C), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ θ₁ θ₂ : R →+* V, Function.Injective θ₁ → Function.Injective θ₂ → IsLocalHom θ₁ → IsLocalHom θ₂ → ∀ κ₁ κ₂ : Sp (FractionRing V) ⟶ Sp (FractionRing R), κ₁ ≫ jK R = jK V ≫ spMap θ₁ → κ₂ ≫ jK R = jK V ≫ spMap θ₂ → κ₁ ≫ C.y = κ₂ ≫ C.y → ∃ (o' : LowObj Cn.D' c ((θ₁.comp (Cn.ψ.comp MvPolynomial.C)).comp Cn.L.b)) (m₁ : ObjMap o' Cn.L.o (spMap (θ₁.comp (Cn.ψ.comp MvPolynomial.C)))) (m₂ : ObjMap o' Cn.L.o (spMap (θ₂.comp (Cn.ψ.comp MvPolynomial.C)))) (x : Cn.L.D.X → (Sp V ⟶ o'.t.G.left)), (∀ y, x y ≫ m₁.toSABMap.φ ≫ Cn.L.φB = spMap (θ₁.comp (Cn.ψ.comp MvPolynomial.C)) ≫ (Cn.L.D.c y).left) ∧ (∀ y, x y ≫ m₂.toSABMap.φ ≫ Cn.L.φB = spMap (θ₂.comp (Cn.ψ.comp MvPolynomial.C)) ≫ (Cn.L.D.c y).left) ∧ ∀ y, x y ≫ o'.t.G.hom = 𝟙 _ := by
  first | exact @GlobalTheory.UCanon.LowPull.exists_lowObj_cdvr | exact GlobalTheory.UCanon.LowPull.exists_lowObj_cdvr | (intros; apply GlobalTheory.UCanon.LowPull.exists_lowObj_cdvr <;> assumption)
