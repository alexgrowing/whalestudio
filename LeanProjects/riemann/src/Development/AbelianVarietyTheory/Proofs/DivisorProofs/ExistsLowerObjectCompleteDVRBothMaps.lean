import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPeriodGens
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompBEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OnTorusComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalFamilyLatticeIdentificationEqIdStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalFamilyBaseEqOfMatchingPullbacksStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.UCanon.LowPull.exists_lowObj_cdvr : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : MonoFam Xo c φ R) (Cn : Canon C), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ θ₁ θ₂ : R →+* V, Function.Injective θ₁ → Function.Injective θ₂ → IsLocalHom θ₁ → IsLocalHom θ₂ → ∀ κ₁ κ₂ : Sp (FractionRing V) ⟶ Sp (FractionRing R), κ₁ ≫ jK R = jK V ≫ spMap θ₁ → κ₂ ≫ jK R = jK V ≫ spMap θ₂ → κ₁ ≫ C.y = κ₂ ≫ C.y → ∃ (o' : LowObj Cn.D' c ((θ₁.comp (Cn.ψ.comp MvPolynomial.C)).comp Cn.L.b)) (m₁ : ObjMap o' Cn.L.o (spMap (θ₁.comp (Cn.ψ.comp MvPolynomial.C)))) (m₂ : ObjMap o' Cn.L.o (spMap (θ₂.comp (Cn.ψ.comp MvPolynomial.C)))) (x : Cn.L.D.X → (Sp V ⟶ o'.t.G.left)), (∀ y, x y ≫ m₁.toSABMap.φ ≫ Cn.L.φB = spMap (θ₁.comp (Cn.ψ.comp MvPolynomial.C)) ≫ (Cn.L.D.c y).left) ∧ (∀ y, x y ≫ m₂.toSABMap.φ ≫ Cn.L.φB = spMap (θ₂.comp (Cn.ψ.comp MvPolynomial.C)) ≫ (Cn.L.D.c y).left) ∧ ∀ y, x y ≫ o'.t.G.hom = 𝟙 _ := by
  intro E _ _ _ H Dw l Xo c φ hpq hφ hns R _ _ _ hR C Cn V _ _ _ hV θ₁ θ₂ hθ₁ hθ₂ hl₁ hl₂ κ₁ κ₂ hκ₁ hκ₂ hy
  obtain ⟨hdvr, hc, hch⟩ := hV
  haveI := hdvr
  haveI := hch
  have hb : θ₁.comp C.b = θ₂.comp C.b := LowPull.comp_b_eq C.toFam θ₁ θ₂ κ₁ κ₂ hκ₁ hκ₂ hy
  obtain ⟨D₁, D₂, hD₁, hD₂, j₁, j₂, b, φ', he₁, he₂, hM, hlin, hQ, hbl⟩ :=
    GlobalTheory.UInj.pair_match Xo c φ R hR C.toFam V hc θ₁ θ₂ hθ₁ hθ₂ hl₁ hl₂ κ₁ κ₂ hκ₁ hκ₂ hy
  have hlat := GlobalTheory.T.canonicalFamily_latticeIdentification_eq_id Xo c φ hpq hφ hns R hR C Cn V hc θ₁ θ₂ hθ₁ hθ₂ hl₁ hl₂ D₁ D₂ hD₁ hD₂ j₁ j₂ b φ' he₁ he₂ hM
    hlin hQ
  exact LowPull.exists_pull₂ Cn.L V _ _ (GlobalTheory.T.canonicalFamily_base_eq_of_matching_pullbacks Xo c φ R hR C Cn V hc θ₁ θ₂ hθ₁ hθ₂ hl₁ hl₂ D₁ D₂ hD₁ hD₂ j₁ j₂ b φ'
    he₁ he₂ hM hQ hbl hlat hb)
