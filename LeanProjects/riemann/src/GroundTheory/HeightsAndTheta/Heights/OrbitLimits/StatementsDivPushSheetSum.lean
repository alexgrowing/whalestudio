import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivPushA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.KerEqBotOfCoord
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivPushC
import ReciprocityTheory.AnalyticForms.PotentialTheory.SNCAtlas
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsArith
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M

section DivPt

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)} {e n : ℕ}

def divPt (R : AnLogRes P J e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) (x : R.X) :
    ((k : K) → ι k) → ℂ :=
  (Ψ (segre (R.lift x x)) 0)⁻¹ • segre (R.lift x x)

end DivPt

def DivPushSheetSum.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (n : ℕ)
    (R : AnLogRes P J (n + 1)) (L : Fin n → HermLine ι) (A B : HermLine ι) (s : MRing ι)
    (r : ℕ) (m : Fin r → ℕ) (W : Fin r → Set R.X) (BW : ∀ k, FinHolAtlas n (W k))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)),
    IsArithVar P (n + 2) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A → IsSmoothHerm B →
    B.a = 0 → IsSectionOn P A s →
    IsSNC R.A (potOf R A) (fun x y => eval (R.lift x y) (map (Int.castRingHom ℂ) s)) m W →
    (∀ k, HoloMap (BW k) R.A Subtype.val) →
    (∀ W' ∈ divSupp P s, IsHorizontal W' → IsGoodProj W' Ψ) →
    ∀ᵐ y, ∀ W' ∈ divSupp P s, IsHorizontal W' → ∀ w ∈ fibre W' Ψ y,
      ∑ k, (m k : ℝ) * ∑ᶠ x ∈ {x : W k | projCoord R Ψ (x : R.X) = y ∧ divPt R Ψ (x : R.X) = w},
          Real.log (B.h (R.lift x x)) *
            pushDens (BW k) (fun i => (potOf R (L i)).pullback Subtype.val continuous_subtype_val)
              (projCoord R Ψ ∘ Subtype.val) x =
        (multAt (P ⊔ Ideal.span {s}) W' : ℝ) *
          sheetDensity W' Ψ (pot L) (fun z => Real.log (B.h z)) y w

section Inhabitants

open GroundTheory.Heights₂.Heights.Inter

def trivLine : HermLine (PBlk 2) :=
  HermLine.ofWeight (fun _ => 0) (fun _ _ _ => rfl)

end Inhabitants

end GroundTheory.Heights₂.Heights.Targets
