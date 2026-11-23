import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyCuspFrame

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompHS

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CechPic GlobalTheory.TangentOrigin GlobalTheory.Vanishing
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag psiSet TIx IsTanFrame)
open GlobalTheory.AllWt (exOf)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : FlagCover Y} {Z : Comp Xo c}
  (M : Modif (str₀ X Z) (U₀ X Z) (dimFlag Dw))

abbrev ksOpen (i : M.K.bundle.ι) (k : X.F.J) : M.X.Opens :=
  M.off ⊓ (LB.div M.K.bundle ((L₀ X Z (FlagTan.kap Dw)).pull M.σ)).U (i, flagIdx M _ k)

def KSRel (i : M.K.bundle.ι) (k : X.F.J) {K : Type} [Field K] (z : Sp K ⟶ M.X) (x : K) : Prop :=
  ∀ [Algebra c.F K] (P Q : FrPt Xo c K) (t : Ix Dw → Kˣ) (v : TIx Dw (psiSet H) → FrPt Xo c (DualNumber K))
    (zv : TIx Dw (psiSet H) → (Sp (DualNumber K) ⟶ M.X)) (O : M.X.Opens) (hO : O ≤ M.K.bundle.U i)
    (g : Fin (dimFlag Dw) → Γ(M.X, O)) (hz : ⊤ ≤ z ⁻¹ᵁ O) (hzv : ∀ b, ⊤ ≤ zv b ⁻¹ᵁ O)
    (hk : ⊤ ≤ (z ≫ toFlag M) ⁻¹ᵁ X.F.U k),
    X.F.ChartFr k (z ≫ toFlag M) hk Q → FrBor t Q P → IsTanFrame (psiSet H) P v →
    (∀ b, zv b ≫ toFlag M = X.ptY (v b)) →
    x * (Matrix.of fun a b =>  (evalPt (zv (tanOrd Dw b)) O (hzv _) (g a)).snd).det =
      (∏ ix, t ix ^ exOf Dw (FlagTan.kap Dw) 0 ix).val * evalPt z O hz (M.K.jacobian i hO g)

theorem isKS_iff_ksRel (ω : H0 M.str (LB.div M.K.bundle ((L₀ X Z (FlagTan.kap Dw)).pull M.σ)) M.off) :
    IsKS M ω ↔ ∀ (K : Type) [Field K] (z : Sp K ⟶ M.X) (i : M.K.bundle.ι) (k : X.F.J) (ho : ⊤ ≤ z ⁻¹ᵁ M.off)
      (hi : ⊤ ≤ z ⁻¹ᵁ (LB.div M.K.bundle ((L₀ X Z (FlagTan.kap Dw)).pull M.σ)).U (i, flagIdx M _ k)),
      KSRel M i k z (H0.val (B := LB.div M.K.bundle ((L₀ X Z (FlagTan.kap Dw)).pull M.σ)) z (i, flagIdx M _ k) ho hi ω) :=
  ⟨fun h K _ z i k ho hi _ P Q t v zv O hO g hz hzv hk hQ ht hv hl =>
      h K P Q t v z zv i k O hO g hz hzv hk ho hi hQ ht hv hl,
    fun h K _ _ P Q t v z zv i k O hO g hz hzv hk ho hi hQ ht hv hl =>
      h K z i k ho hi P Q t v zv O hO g hz hzv hk hQ ht hv hl⟩

end GlobalTheory.CompHS
