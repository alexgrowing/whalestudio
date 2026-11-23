import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.DataAtPointN3

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.FormalGroupLawsExistenceTori

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.DIV.Cons (SCF intO)
open scoped TensorProduct

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

section Point

variable {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {p : ℕ} {C : SCF p} {P : PointsOfFlagModel.PtC Y C}

def rho (A : DatAt Y P) : ℕ := Module.finrank (𝓞 E) A.Ylat

def IsoForms (A A' : DatAt Y P) : Prop :=
  ∃ e : A.Ylat ≃ₗ[𝓞 E] A'.Ylat, ∀ a b, A'.beta (e a) (e b) = A.beta a b

structure FormLaws (A : DatAt Y P) : Prop where

  add : ∀ a a' b : A.Ylat, A.beta (a + a') b = A.beta a b + A.beta a' b

  balanced : ∀ (x : 𝓞 E) (a b : A.Ylat), A.beta (x • a) b = A.beta a (H.bar x • b)

  pos : ∀ a : A.Ylat, a ≠ 0 → 0 < A.beta a a

  posReal : ∀ (n : ℕ) (t : Fin n → ℝ) (a : Fin n → A.Ylat),
    (∑ i, t i ⊗ₜ[ℤ] a i : ℝ ⊗[ℤ] A.Ylat) ≠ 0 → 0 < ∑ i, ∑ j, t i * t j * A.beta (a i) (a j)

structure RankLaws (A : DatAt Y P) : Prop where

  proj : Module.Projective (𝓞 E) A.Ylat

  rankZ : Module.finrank ℤ A.Ylat = 2 * Module.finrank ℚ (maximalRealSubfield E) * rho A

  le_p : rho A ≤ Dw.p

  le_q : rho A ≤ Dw.q

structure PointLaws (Y : Model Xo c β) (P : PointsOfFlagModel.PtC Y C) : Prop where

  ex : Nonempty (DatAt Y P)

  uniq : ∀ A A' : DatAt Y P, IsoForms A A'

  form : ∀ A : DatAt Y P, FormLaws A

  rank : ∀ A : DatAt Y P, RankLaws A

def qPsi (A : DatAt Y P) (a : A.Ylat) : ℝ :=
  vPsiAt A.U.D.toPre ((intO ↥C.S).subtype.comp A.f) p a

def HalfNormLaw (A : DatAt Y P) : Prop :=
  ∀ a : A.Ylat, qPsi A a = A.beta a (H.w0 • a) ∧ qPsi A a = A.beta a (H.bar H.w0 • a) ∧
    2 * qPsi A a = A.beta a a

end Point

def Laws {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β) (p : ℕ) : Prop :=
  ∀ (C : SCF p) (P : PointsOfFlagModel.PtC Y C), PointLaws Y P

def TowerLaws {p : ℕ} (T : PointsOfFlagModel.Tower p Xo c) : Prop :=
  (∀ v, Laws (T.Y v) p) ∧ ∀ n w, Laws (T.YN n w) p

def Claim : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (p : ℕ), p.Prime →
    ∀ (v : PointsOfFlagModel.abelian₂ p c) (O : Type) [CommRing O] (β : O →+* c.F), PointsOfFlagModel.BaseAt v.1 β →
    ∀ Y : Model Xo c β, Y.SplitFibres → Y.N3 →
      Laws Y p ∧ ∀ (C : SCF p) (P : PointsOfFlagModel.PtC Y C) (A : DatAt Y P), HalfNormLaw A

end GlobalTheory.IndefiniteRowSideFullHecke.FormalGroupLawsExistenceTori
