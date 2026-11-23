import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegExp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtPtBridgeSt

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

variable {V : Type} [CommRing V] [IsDomain V]

def HasVal (ϖ : V) (c : FractionRing V) (n : ℤ) : Prop :=
  ∃ u : Vˣ, c = algebraMap V (FractionRing V) ϖ ^ n * algebraMap V (FractionRing V) (u : V)

lemma wchart_le_preimage {X Y Z : Scheme.{0}} (L : LB X) {Ix : Type} [Fintype Ix] (f : Z ⟶ Y)
    (φ : Ix → (Y ⟶ X)) (φ' : Ix → (Z ⟶ X)) (hφ : ∀ k, φ' k = f ≫ φ k) (j : Ix → L.ι) :
    LB.wchart L φ' j ≤ f ⁻¹ᵁ LB.wchart L φ j := by
  intro x hx
  have hx' : x ∈ ⋂ k, (φ' k).base ⁻¹' (L.U (j k) : Set X) := hx
  show f.base x ∈ ⋂ k, (φ k).base ⁻¹' (L.U (j k) : Set X)
  simp only [Set.mem_iInter, Set.mem_preimage] at hx' ⊢
  intro k
  have h := hx' k
  rw [hφ k] at h
  simpa using h

def GenHasVal (ϖ : V) {X : Scheme.{0}} (L : LB X) {Ix : Type} [Fintype Ix]
    (φ : Ix → (Spec (CommRingCat.of V) ⟶ X)) (φ' : Ix → (Spec (CommRingCat.of (FractionRing V)) ⟶ X))
    (hφ : ∀ k, φ' k = jK V ≫ φ k) (ε : Ix → ℤ) (t : LB.Gen (LB.LinComb L φ' ε)) (n : ℤ) : Prop :=
  ∃ e : LB.Gen (LB.LinComb L φ ε), e.IsGen ∧ ∃ c : FractionRing V, HasVal ϖ c n ∧
    ∀ j, (t.s j).val = resTop _ (scal (𝟙 (Spec (CommRingCat.of (FractionRing V)))) c) *
      (res (wchart_le_preimage L (jK V) φ φ' hφ j) (pullU (jK V) _ (e.s j))).val

namespace QForm

variable (D : DegPre V)

lemma ptK_eq (χ : D.X) : ptK (D.c χ) = jK V ≫ (D.c χ).left := by
  simp only [ptK, Over.comp_left]
  congr 1

def QVal (ϖ : V) (χ : D.X) (n : ℤ) : Prop :=
  GenHasVal ϖ D.P.L (fun _ : PUnit => (D.c χ).left) (fun _ => ptK (D.c χ)) (fun _ => ptK_eq D χ) (fun _ => -1)
    (D.psi χ) n

def IsQ (ϖ : V) (Q : D.X → ℤ) : Prop := ∀ χ, QVal D ϖ χ (Q χ)

def bOf (Q : D.X → ℤ) (χ χ' : D.X) : ℤ := Q (χ + χ') - Q χ - Q χ'

end QForm

end ReciprocityTheory.ChartRestriction.G.DVR
