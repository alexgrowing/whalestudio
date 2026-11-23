import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleOfFinrankLeCardAlgHomAlgebraicClosure
import Development.AbelianVarietyTheory.Definitions.Divisors.JoinCastSucc
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.FramedLatticeZeroCycleHeight
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_of_finrank_le_card_algHom : ∀ (E R : Type) [Field E] [CommRing R] [Algebra E R] [Module.Finite E R], Finite (R →ₐ[E] AlgebraicClosure E) ∧ Nat.card (R →ₐ[E] AlgebraicClosure E) ≤ Module.finrank E R ∧ (Module.finrank E R ≤ Nat.card (R →ₐ[E] AlgebraicClosure E) → Algebra.Etale E R) := by
  first | exact @GlobalTheory.etale_of_finrank_le_card_algHom_algebraicClosure | exact GlobalTheory.etale_of_finrank_le_card_algHom_algebraicClosure | (intros; apply GlobalTheory.etale_of_finrank_le_card_algHom_algebraicClosure <;> assumption)
