import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeSpectrumDualNumberEq

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.CompHS GlobalTheory.CxPts GlobalTheory.Vanishing
open GlobalTheory.TangentOrigin GlobalTheory.CechPic GlobalTheory.TopForm GlobalTheory.Adelic

namespace GlobalTheory.CompHS

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y}
  {Z : Comp Xo c}

theorem evalPt_appLE_of_comp {R : Type} [CommRing R] {A B : Scheme.{0}} (v : Sp R ⟶ A) (φ : A ⟶ B) (U : B.Opens)
    (V : A.Opens) (e : V ≤ φ ⁻¹ᵁ U) (f : Γ(B, U)) (hV : ⊤ ≤ v ⁻¹ᵁ V) (hU : ⊤ ≤ (v ≫ φ) ⁻¹ᵁ U) :
    evalPt v V hV (φ.appLE U V e f) = evalPt (v ≫ φ) U hU f := by
  simp only [evalPt, CommRingCat.hom_comp, RingHom.comp_apply]
  rw [← CommRingCat.comp_apply (φ.appLE U V e), Scheme.Hom.appLE_comp_appLE]

theorem canId_val_mul_det (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw)) (ω : CanId M)
    {L : Type} [Field L] [iL : Algebra c.F L] (Q : FrPt Xo c L)
    (v : GlobalTheory.FlagTan.TIx Dw (GlobalTheory.FlagTan.psiSet H) → FrPt Xo c (DualNumber L))
    (hv : GlobalTheory.FlagTan.IsTanFrame (GlobalTheory.FlagTan.psiSet H) Q v) (z : Sp L ⟶ M.X)
    (zv : GlobalTheory.FlagTan.TIx Dw (GlobalTheory.FlagTan.psiSet H) → (Sp (DualNumber L) ⟶ M.X)) (i : M.K.bundle.ι) (k : X.F.J)
    (O : M.X.Opens) (hO : O ≤ M.K.bundle.U i) (g : Fin (GlobalTheory.FlagTan.dimFlag Dw) → Γ(M.X, O)) (hz : ⊤ ≤ z ⁻¹ᵁ O)
    (hzv : ∀ b, ⊤ ≤ zv b ⁻¹ᵁ O) (hk : ⊤ ≤ (z ≫ toFlag M) ⁻¹ᵁ X.F.U k) (ho : ⊤ ≤ z ⁻¹ᵁ M.off)
    (hi : ⊤ ≤ z ⁻¹ᵁ (LB.div M.K.bundle ((L₀ X Z (GlobalTheory.FlagTan.kap Dw)).pull M.σ)).U (i, flagIdx M _ k))
    (hQ : X.F.ChartFr k (z ≫ toFlag M) hk Q) (hl : ∀ b, zv b ≫ toFlag M = X.ptY (v b)) :
    H0.val (B := LB.div M.K.bundle ((L₀ X Z (GlobalTheory.FlagTan.kap Dw)).pull M.σ)) z (i, flagIdx M _ k) ho hi ω.ω *
        (Matrix.of fun a b => (evalPt (zv (tanOrd Dw b)) O (hzv _) (g a)).snd).det =
      evalPt z O hz (M.K.jacobian i hO g) := by
  have hb := (GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c L).1 Q
  have a := ω.isKS L Q Q 1 v z zv i k O hO g hz hzv hk ho hi hQ hb hv hl
  simpa only [Pi.one_apply, one_zpow, Finset.prod_const_one, Units.val_one, one_mul] using a

end GlobalTheory.CompHS
