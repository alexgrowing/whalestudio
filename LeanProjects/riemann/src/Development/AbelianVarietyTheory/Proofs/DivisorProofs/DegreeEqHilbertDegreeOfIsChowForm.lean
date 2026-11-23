import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JoinCastSucc
import Development.AbelianVarietyTheory.Definitions.Divisors.IrreducibleOfIrreducibleMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChowFormIntExistsAndChowFormExists
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.FramedLatticeZeroCycleHeight

set_option autoImplicit false

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

namespace GlobalTheory.ChowDegree

attribute [local instance] MvPolynomial.gradedAlgebra

theorem degree_eq_hilbertDegree_of_isChowForm : ∀ (F : Type) [Field F] [CharZero F] (D N δ : ℕ) (I : Ideal (MvPolynomial (Fin N) F)) (f : MvPolynomial (Fin (D + 1) × Fin N) F), IsChowForm I D δ f → I.IsPrime → (∀ g ∈ I, ∀ n : ℕ, homogeneousComponent n g ∈ I) → δ = hilbertDegree I := by
  intro F _ _ D N δ I f hf hp hI
  haveI := hp
  exact GlobalTheory.ChowExists.degree_eq_hilbertDegree (GlobalTheory.ChowExists.isHomogeneous_of_component hI)
    hf.isChowFormInt

end GlobalTheory.ChowDegree
