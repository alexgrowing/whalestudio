import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.IsNullVal
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TorusAt

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EtaAn

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree GlobalTheory.EtaForm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}

section Fam

variable {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} (Fu : FamilyUnif Xo σ ty)
  (i : Fin Fu.n) (Pm : (Fu.Di i).La →+ (Fin g → ℂ))

def AHFrame (Hm : Matrix (Fin g) (Fin g) ℂ) (χl : (Fin g → ℂ) → ℂ)
    (fr : Xo.univ.t.PP.L.ι → (Fin g → ℂ) → ℂ) : Prop :=
  Hm.IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧
    (∀ a b, (hermForm Hm (Pm a) (Pm b)).im = (Fu.Di i).EF a b) ∧
    (∀ j, DifferentiableOn ℂ (fr j) {z | ⊤ ≤ (Fu.ex i Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j}) ∧
    (∀ j z, ⊤ ≤ (Fu.ex i Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr j z ≠ 0) ∧
    (∀ j j' z, ⊤ ≤ (Fu.ex i Pm z).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') →
      fr j z = valAt' (Fu.ex i Pm z).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j')
        (Xo.univ.t.PP.L.g j j').val * fr j' z) ∧
    (∀ j, ⊤ ≤ (Fu.ex i Pm 0).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr j 0 = valAt' (Fu.u i Pm) ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j))
        (Xo.univ.t.PP.rig.s (fun _ => j)).val) ∧
    ∀ a j z, ‖χl (Pm a)‖ = 1 ∧ (⊤ ≤ (Fu.ex i Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr j z = χl (Pm a) * Complex.exp (Real.pi * hermForm Hm z (Pm a) +
        Real.pi / 2 * hermForm Hm (Pm a) (Pm a)) * fr j (z + Pm a))

def IsFnOf (fr : Xo.univ.t.PP.L.ι → (Fin g → ℂ) → ℂ) (x : Sp ℂ ⟶ Xo.X) (s : LB.Sec (PPx x))
    (θ : (Fin g → ℂ) → ℂ) : Prop :=
  ∀ j z (pt : Sp ℂ ⟶ Gx x), pt ≫ gxFst x = (Fu.ex i Pm z).left → pt ≫ gxSnd x = 𝟙 (Sp ℂ) →
    ⊤ ≤ (Fu.ex i Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
    valAt' pt ((PPx x).U (fun _ => j)) (s.f (fun _ => j)) = θ z * fr j z

end Fam

def IsTorusOf (D : Datum H) {g : ℕ} (ty : Fin g → (E →+* ℂ)) (Pm : D.La →+ (Fin g → ℂ))
    (Hm : Matrix (Fin g) (Fin g) ℂ) (T : I2.PT E) (ψ : (Fin g → ℂ) ≃ₗ[ℂ] I2.Vsp T.dim) : Prop :=
  T.r = D.p + D.q ∧ (∀ τ, T.dim τ = D.mult τ) ∧ (∀ z w, I2.Hf (ψ z) (ψ w) = hermForm Hm z w) ∧
    (∀ v, v ∈ T.L ↔ ∃ a, ψ (Pm a) = v) ∧
    (∀ (α : 𝓞 E) z, ψ (fun k => ty k (α : E) * z k) = I2.act α (ψ z)) ∧
    ∀ a, T.eps (ψ (Pm a)) = (Int.negOnePow (D.EF a (H.w0 • a)) : ℤˣ)

variable (E) in

def RunOK (r DF q : ℕ) (R0 : ℝ) (m : ℕ) : Prop :=
  ∀ X : I2.PT E, X.r = r → (∃ τ, X.dim τ ≤ m) → ∃ P : I2.Par X DF, P.q = q ∧ P.R0 = R0 ∧ P.m = m

variable (E) in

def p3 (r q m : ℕ) : ℝ :=
  r * ((1 + ((I2.PT.f E * r : ℕ) : ℝ) * Real.log (1 + 6 * Real.sqrt (((I2.PT.f E * r : ℕ) : ℝ) * q))) +
    Real.log (2 * (3 * (I2.dstar (E := E) m : ℝ)) ^ I2.dstar (E := E) m) + I2.dstar (E := E) m)

variable (E) in

def p16 (r q m R N : ℕ) : ℝ :=
  2 * (R : ℝ) ^ 4 * (p3 E r q m + (Real.log N + 2 * I2.PT.f E * (r : ℝ) ^ 2 * Real.log R)) +
    ((R : ℝ) ^ 4 * r * I2.dstar (E := E) m / 2) *
      Real.log (((R : ℝ) ^ 4 * r * I2.dstar (E := E) m / 2) * (4 * I2.RR (E := E) * (I2.dstar (E := E) m : ℝ) ^ 2))

def Spans {k : ℕ} {J : Type} {n : ℕ} (x : J → Fin n → LatMod Dw k) : Prop :=
  ∀ j, Submodule.span (𝓞 E) (Set.range (x j)) = ⊤

end GlobalTheory.EtaAn
