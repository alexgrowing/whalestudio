import Formalism.LocalToGlobal.ProjectiveLattices.BetaAddRight

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
open Formalism.MainNotions.DIV.Cons (SCF intO)

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

structure LatB (E : Type) [Field E] [NumberField E] where
  Y : Type
  [add : AddCommGroup Y]
  [free : Module.Free ℤ Y]
  [fin : Module.Finite ℤ Y]
  [md : Module (𝓞 E) Y]
  beta : Y → Y → ℝ

attribute [instance] LatB.add LatB.free LatB.fin LatB.md

section
variable {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O]
  {β : O →+* c.F} {Y : Model Xo c β} {p : ℕ} {C : SCF p} {P : PointsOfFlagModel.PtC Y C}

def DatAt.toLatB (A : DatAt Y P) : LatB E := ⟨A.Ylat, A.beta⟩

end

open PointsOfFlagModel

variable {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {p : ℕ}

def N3Tower (T : Tower p Xo c) : Prop := (∀ v, N3AtPoints (T.Y v) p) ∧ ∀ n w, N3AtPoints (T.YN n w) p

def UniqTow (T : Tower p Xo c) : Prop := (∀ v, UniqBeta (T.Y v) p) ∧ ∀ n w, UniqBeta (T.YN n w) p

def AddTow (T : Tower p Xo c) : Prop := (∀ v, BetaAdd (T.Y v) p) ∧ ∀ n w, BetaAdd (T.YN n w) p

def BalTow (T : Tower p Xo c) (cj : E → E) : Prop := (∀ v, BetaBal (T.Y v) p cj) ∧ ∀ n w, BetaBal (T.YN n w) p cj

def PosDefTow (T : Tower p Xo c) : Prop := (∀ v, BetaPosDef (T.Y v) p) ∧ ∀ n w, BetaPosDef (T.YN n w) p

def RankTow (T : Tower p Xo c) (r j : ℕ) : Prop := (∀ v, YlRank (T.Y v) p r j) ∧ ∀ n w, YlRank (T.YN n w) p r j

variable {T : Tower p Xo c}

def lattice₂ (hN : N3Tower T) : ∀ {Z : MdlC}, Pt T Z → LatB E
  | .xm, y => (Classical.choice (hN.1 y.1 y.2.1 y.2.2)).toLatB
  | .yy, y => (Classical.choice (hN.1 y.1 y.2.1 y.2.2.1)).toLatB
  | .xn n, y => (Classical.choice (hN.2 n y.1 y.2.1 y.2.2)).toLatB

abbrev YlatP (hN : N3Tower T) {Z : MdlC} (y : Pt T Z) : Type := (lattice₂ hN y).Y

theorem latticeAt_cases (hN : N3Tower T) (Q : LatB E → Prop)
    (hb : ∀ v (C : SCF p) (P : PtC (T.Y v) C) (A : DatAt (T.Y v) P), Q A.toLatB)
    (hd : ∀ n w (C : SCF p) (P : PtC (T.YN n w) C) (A : DatAt (T.YN n w) P), Q A.toLatB) :
    ∀ {Z : MdlC} (y : Pt T Z), Q (lattice₂ hN y)
  | .xm, y => hb y.1 y.2.1 y.2.2 _
  | .yy, y => hb y.1 y.2.1 y.2.2.1 _
  | .xn n, y => hd n y.1 y.2.1 y.2.2 _

theorem latticeAt_form_add_left (hN : N3Tower T) (hA : AddTow T) {Z : MdlC} (y : Pt T Z) (a a' b : YlatP hN y) :
    (lattice₂ hN y).beta (a + a') b = (lattice₂ hN y).beta a b + (lattice₂ hN y).beta a' b :=
  latticeAt_cases hN (fun L => ∀ a a' b : L.Y, L.beta (a + a') b = L.beta a b + L.beta a' b)
    (fun v C P A => hA.1 v C P A) (fun n w C P A => hA.2 n w C P A) y a a' b

theorem latticeAt_form_symm (hN : N3Tower T) {Z : MdlC} (y : Pt T Z) (a b : YlatP hN y) :
    (lattice₂ hN y).beta a b = (lattice₂ hN y).beta b a :=
  latticeAt_cases hN (fun L => ∀ a b : L.Y, L.beta a b = L.beta b a)
    (fun _ _ _ A a b => betaAt_symm _ _ _ a b) (fun _ _ _ _ A a b => betaAt_symm _ _ _ a b) y a b

theorem latticeAt_form_add_right (hN : N3Tower T) (hA : AddTow T) {Z : MdlC} (y : Pt T Z) (a b b' : YlatP hN y) :
    (lattice₂ hN y).beta a (b + b') = (lattice₂ hN y).beta a b + (lattice₂ hN y).beta a b' := by
  rw [latticeAt_form_symm, latticeAt_form_add_left hN hA, latticeAt_form_symm hN y b a, latticeAt_form_symm hN y b' a]

def beP (hN : N3Tower T) (hA : AddTow T) {Z : MdlC} (y : Pt T Z) : YlatP hN y →ₗ[ℤ] YlatP hN y →ₗ[ℤ] ℝ :=
  (AddMonoidHom.mk' (fun a => (AddMonoidHom.mk' (fun b => (lattice₂ hN y).beta a b)
      (fun b b' => latticeAt_form_add_right hN hA y a b b')).toIntLinearMap)
    (fun a a' => by
      ext b
      simp [latticeAt_form_add_left hN hA y a a' b])).toIntLinearMap

theorem latticeForm_apply (hN : N3Tower T) (hA : AddTow T) {Z : MdlC} (y : Pt T Z) (a b : YlatP hN y) :
    beP hN hA y a b = (lattice₂ hN y).beta a b := rfl

theorem latticeForm_symm (hN : N3Tower T) (hA : AddTow T) {Z : MdlC} (y : Pt T Z) (a b : YlatP hN y) :
    beP hN hA y a b = beP hN hA y b a :=
  latticeAt_form_symm hN y a b

theorem latticeForm_smul_left_eq_conj_smul_right (hN : N3Tower T) (hA : AddTow T) {cj : E → E} (hB : BalTow T cj) {Z : MdlC} (y : Pt T Z)
    (x x' : 𝓞 E) (hx : (x' : E) = cj (x : E)) (a b : YlatP hN y) :
    beP hN hA y (x • a) b = beP hN hA y a (x' • b) := by
  exact latticeAt_cases hN
    (fun L => ∀ (x x' : 𝓞 E), (x' : E) = cj (x : E) → ∀ a b : L.Y, L.beta (x • a) b = L.beta a (x' • b))
    (fun v C P A => hB.1 v C P A) (fun n w C P A => hB.2 n w C P A) y x x' hx a b

theorem latticeForm_posDef (hN : N3Tower T) (hA : AddTow T) (hP : PosDefTow T) {Z : MdlC} (y : Pt T Z) :
    ∃ (ι : Type) (_ : Fintype ι) (b : Module.Basis ι ℤ (YlatP hN y)),
      ∀ x : ι → ℝ, x ≠ 0 → 0 < ∑ i, ∑ k, x i * x k * beP hN hA y (b i) (b k) := by
  exact latticeAt_cases hN
    (fun L => ∃ (ι : Type) (_ : Fintype ι) (b : Module.Basis ι ℤ L.Y),
      ∀ x : ι → ℝ, x ≠ 0 → 0 < ∑ i, ∑ k, x i * x k * L.beta (b i) (b k))
    (fun v C P A => hP.1 v C P A) (fun n w C P A => hP.2 n w C P A) y

theorem exists_finrank_lattice_eq_mul (hN : N3Tower T) {r j : ℕ} (hR : RankTow T r j) {Z : MdlC} (y : Pt T Z) :
    ∃ ρ : ℕ, Module.finrank ℤ (YlatP hN y) = 2 * (Module.finrank ℚ E / 2) * ρ ∧
      (1 ≤ j → j + 1 ≤ r → ρ ≤ j ∧ ρ + j ≤ r) := by
  exact latticeAt_cases hN
    (fun L => ∃ ρ : ℕ, Module.finrank ℤ L.Y = 2 * (Module.finrank ℚ E / 2) * ρ ∧
      (1 ≤ j → j + 1 ≤ r → ρ ≤ j ∧ ρ + j ≤ r))
    (fun v C P A => hR.1 v C P A) (fun n w C P A => hR.2 n w C P A) y

end Formalism.L2.Pj
