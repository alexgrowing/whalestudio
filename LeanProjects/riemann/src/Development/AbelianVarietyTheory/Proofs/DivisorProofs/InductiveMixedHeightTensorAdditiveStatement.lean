import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InductiveMixedHeightTensorAdditive
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inductiveMixedHeight_tensor_additive : ArchInteg → ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k), IsAmb q → ∀ e : ℕ, topologicalKrullDim Y = (e + 1 + 1 : ℕ) → ∀ T, IsMix q (e + 1) T → ∀ (M : HermLB q) (r : M.B.ι → Y.functionFieldˣ) (hr : IsRatSec M.B r) (A B : HermLB q) (L : Fin e → HermLB q), recVal (T (e + 1) (Fin.cons (A.tens B) L)) (Fin.cons (A.tens B) L : Fin (e + 1) → HermLB q) M hr = recVal (T (e + 1) (Fin.cons A L)) (Fin.cons A L : Fin (e + 1) → HermLB q) M hr + recVal (T (e + 1) (Fin.cons B L)) (Fin.cons B L : Fin (e + 1) → HermLB q) M hr := by
  first | exact @GlobalTheory.MixHt.recVal_tens_cons | exact GlobalTheory.MixHt.recVal_tens_cons | (intros; apply GlobalTheory.MixHt.recVal_tens_cons <;> assumption)
