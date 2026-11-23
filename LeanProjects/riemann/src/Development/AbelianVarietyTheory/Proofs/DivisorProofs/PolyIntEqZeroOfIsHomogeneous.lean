import Mathlib
import ReciprocityTheory.AnalyticForms.PotentialTheory.PotentialContDiffAt
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef

set_option autoImplicit false

noncomputable section

open MvPolynomial ReciprocityTheory.AnForm.M

namespace GlobalTheory.ChernPoly

variable {e : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

def monOf (f : Fin e → ι) : ι →₀ ℕ := ∑ j, Finsupp.single (f j) 1

def polyWt (F : MvPolynomial ι ℝ) (f : Fin e → ι) : ℝ :=
  coeff (monOf f) F * ((monOf f).prod fun _ n => (n.factorial : ℝ)) / e.factorial

theorem polyWt_add (F G : MvPolynomial ι ℝ) (f : Fin e → ι) :
    polyWt (F + G) f = polyWt F f + polyWt G f := by
  simp only [polyWt, coeff_add]; ring

theorem polyWt_smul (c : ℝ) (F : MvPolynomial ι ℝ) (f : Fin e → ι) :
    polyWt (c • F) f = c * polyWt F f := by
  simp only [polyWt, coeff_smul, smul_eq_mul]; ring

variable {X : Type*} [TopologicalSpace X]

def combPot (P : ι → LocPot X) (n : ι → ℤ) : LocPot X :=
  (Finset.univ : Finset ι).toList.foldr (fun i Q => (P i).zsmul (n i) + Q) (LocPot.ofFun fun _ => 0)

def polyInt (A : FinHolAtlas e X) (P : ι → LocPot X) (F : MvPolynomial ι ℝ) (g : X → ℝ) : ℝ :=
  ∑ f : Fin e → ι, polyWt F f * mInt A (P ∘ f) g

theorem polyInt_add (A : FinHolAtlas e X) (P : ι → LocPot X) (F G : MvPolynomial ι ℝ) (g : X → ℝ) :
    polyInt A P (F + G) g = polyInt A P F g + polyInt A P G g := by
  simp only [polyInt, polyWt_add, add_mul, Finset.sum_add_distrib]

theorem polyInt_smul (A : FinHolAtlas e X) (P : ι → LocPot X) (c : ℝ) (F : MvPolynomial ι ℝ)
    (g : X → ℝ) : polyInt A P (c • F) g = c * polyInt A P F g := by
  simp only [polyInt, polyWt_smul, Finset.mul_sum, mul_assoc]

def polyIntL (A : FinHolAtlas e X) (P : ι → LocPot X) (g : X → ℝ) : MvPolynomial ι ℝ →ₗ[ℝ] ℝ where
  toFun F := polyInt A P F g
  map_add' F G := polyInt_add A P F G g
  map_smul' c F := polyInt_smul A P c F g

@[simp] theorem polyIntL_apply (A : FinHolAtlas e X) (P : ι → LocPot X) (g : X → ℝ)
    (F : MvPolynomial ι ℝ) : polyIntL A P g F = polyInt A P F g := rfl

end GlobalTheory.ChernPoly

namespace GlobalTheory.ChernPoly

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {D : ℕ} {ι : Type} [Fintype ι]
  [DecidableEq ι]

open scoped Classical in

def cxPolyInt (R : ∀ σ : k →+* ℂ, AnRead p σ D) (L : ι → HermLB p) (F : MvPolynomial ι ℝ)
    (g : ∀ σ : k →+* ℂ, CxPts p σ → ℝ) : ℝ :=
  ∑ᶠ σ, if h : CompactSpace (CxPts p σ) then
    (haveI := h; polyInt (R σ).finAtlas (fun i => ((L i).φ σ).locPot) F (g σ)) else 0

end GlobalTheory.ChernPoly
