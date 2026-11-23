import Development.AbelianVarietyTheory.Definitions.Divisors.IntegralBound
import Formalism.HarderNarasimhan.StatementPl
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open Matrix

noncomputable section

open scoped MatrixOrder ComplexOrder

namespace GlobalTheory.HermFamFrame

def formRight {K V : Type} [Field K] [AddCommGroup V] [Module K V] (nm : HermFam K V)
    (σ : K →+* ℂ) (x : V) : V →+ ℂ :=
  AddMonoidHom.mk' (nm.form σ x) (nm.add_right σ x)

theorem form_sum_right {K V : Type} [Field K] [AddCommGroup V] [Module K V] (nm : HermFam K V)
    (σ : K →+* ℂ) (x : V) {ι : Type} (s : Finset ι) (a : ι → K) (w : ι → V) :
    nm.form σ x (∑ j ∈ s, a j • w j) = ∑ j ∈ s, σ (a j) * nm.form σ x (w j) := by
  have := map_sum (formRight nm σ x) (fun j => a j • w j) s
  simp only [formRight, AddMonoidHom.mk'_apply] at this
  rw [this]
  exact Finset.sum_congr rfl fun j _ => nm.smul_right σ (a j) x (w j)

theorem form_sum_left {K V : Type} [Field K] [AddCommGroup V] [Module K V] (nm : HermFam K V)
    (σ : K →+* ℂ) (y : V) {ι : Type} (s : Finset ι) (a : ι → K) (w : ι → V) :
    nm.form σ (∑ i ∈ s, a i • w i) y = ∑ i ∈ s, starRingEnd ℂ (σ (a i)) * nm.form σ (w i) y := by
  rw [← nm.conj_symm, form_sum_right, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, nm.conj_symm]

def basisGram {K V : Type} [Field K] [AddCommGroup V] [Module K V] (nm : HermFam K V)
    (σ : K →+* ℂ) {ι : Type} (b : Module.Basis ι K V) : Matrix ι ι ℂ :=
  Matrix.of fun i j => nm.form σ (b i) (b j)

end GlobalTheory.HermFamFrame

end
