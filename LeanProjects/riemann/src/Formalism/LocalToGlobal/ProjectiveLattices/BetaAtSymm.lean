import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp

noncomputable section

namespace Formalism.L2.Pj

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open AlgebraicGeometry CategoryTheory

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]

def ordPsi (D : DegPre R) (χ : D.X) : ℕ∞ :=
  ⨆ (n : ℕ) (_ : D.PsiIn χ (IsLocalRing.maximalIdeal R ^ n)), (n : ℕ∞)

def betaZ (D : DegPre R) (a b : D.X) : ℤ :=
  ((ordPsi D (a + b)).toNat : ℤ) - ((ordPsi D a).toNat : ℤ) - ((ordPsi D b).toNat : ℤ)

def ordNat (R : Type) [CommRing R] [IsLocalRing R] (n : ℕ) : ℕ∞ :=
  ⨆ (k : ℕ) (_ : (n : R) ∈ IsLocalRing.maximalIdeal R ^ k), (k : ℕ∞)

def betaP (D : DegPre R) (p : ℕ) (a b : D.X) : ℝ :=
  (betaZ D a b : ℝ) / ((ordNat R p).toNat : ℝ)

section At

variable {R : Type} [CommRing R] [IsDomain R]

def PsiCoord (D : DegPre R) (χ : D.X) (r : R) : Prop :=
  ∃ (j : PUnit → D.P.L.ι) (_ : (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ (D.c χ).left ⁻¹ᵁ D.P.L.U (j PUnit.unit))
    (h : jK R ⁻¹ᵁ ⊤ ≤ (LB.LinComb D.P.L (K := PUnit) (fun _ => D.xK χ) (fun _ => -1)).U j),
    ((jK R).app ⊤).hom (DegPre.toOpen (R := R) ⊤ r) = ((TK R).left.presheaf.map (homOfLE h).op).hom ((D.psi χ).s j).val

def vPsiAt (D : DegPre R) {C : Type} [NormedField C] (f : R →+* C) (p : ℕ) (χ : D.X) : ℝ :=
  open Classical in
  if h : ∃ r, PsiCoord D χ r then -Real.logb p ‖f h.choose‖ else 0

def betaAt (D : DegPre R) {C : Type} [NormedField C] (f : R →+* C) (p : ℕ) (a b : D.X) : ℝ :=
  vPsiAt D f p (a + b) - vPsiAt D f p a - vPsiAt D f p b

theorem betaAt_symm (D : DegPre R) {C : Type} [NormedField C] (f : R →+* C) (p : ℕ) (a b : D.X) :
    betaAt D f p a b = betaAt D f p b a := by
  unfold betaAt
  rw [add_comm a b]
  ring

end At

end Formalism.L2.Pj
