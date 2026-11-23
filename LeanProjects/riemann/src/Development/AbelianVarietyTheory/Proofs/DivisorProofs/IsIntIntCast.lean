import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowEqPowOfModEqSim
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudeActionAdelicLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeVectorBundlePullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuedIntCastLeIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeCompletionEqLatticeVectorAddNsmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualLatticeDegreeNeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatHermUnitConstant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEqNsmulOfActs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoprimeNatMulFiniteAdeleAwayPIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoprimeNsmulEndomorphismPreservesCompletioStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorActionFormEqSimilitudeMulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDivisorMulIntegralUnitFiniteAdelesAwayPStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralAdeleUnitCongruenceSequence
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeEndomorphismIntegralApproximation

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HeckeApprox

variable {p : ℕ} [Fact p.Prime]

abbrev fAf (D : Datum p) : LinearMap.BilinForm (AfP p) (AfP p ⊗[ℚ] VQ D) := (D.EF.baseChange ℚ).baseChange (AfP p)

theorem isInt_one : IsIntAf (1 : AfP p) := fun v => by rw [map_one]; exact one_mem _
theorem isInt_mul {a b : AfP p} (ha : IsIntAf a) (hb : IsIntAf b) : IsIntAf (a * b) := fun v => by
  rw [map_mul]; exact mul_mem (ha v) (hb v)
theorem isInt_add {a b : AfP p} (ha : IsIntAf a) (hb : IsIntAf b) : IsIntAf (a + b) := fun v => by
  rw [map_add]; exact add_mem (ha v) (hb v)
theorem isInt_sub {a b : AfP p} (ha : IsIntAf a) (hb : IsIntAf b) : IsIntAf (a - b) := fun v => by
  rw [map_sub]; exact sub_mem (ha v) (hb v)
theorem isInt_intCast (k : ℤ) : IsIntAf (k : AfP p) := fun v => by rw [map_intCast]; exact intCast_mem _ k
theorem isInt_natCast (k : ℕ) : IsIntAf (k : AfP p) := fun v => by rw [map_natCast]; exact natCast_mem _ k

def inAfH (D : Datum p) : D.La →+ AfP p ⊗[ℚ] VQ D := AddMonoidHom.mk' (inAf D) (fun x y => by
  simp only [inAf, TensorProduct.tmul_add])

theorem inAf_sub (D : Datum p) (x y : D.La) : inAf D (x - y) = inAf D x - inAf D y := map_sub (inAfH D) x y
theorem inAf_add (D : Datum p) (x y : D.La) : inAf D (x + y) = inAf D x + inAf D y := map_add (inAfH D) x y
theorem inAf_nsmul (D : Datum p) (n : ℕ) (x : D.La) : inAf D (n • x) = n • inAf D x := map_nsmul (inAfH D) n x
theorem inAf_mem (D : Datum p) (x : D.La) : inAf D x ∈ LaHat D :=
  AddSubgroup.subset_closure ⟨1, x, isInt_one, rfl⟩

theorem form_inAf (D : Datum p) (x y : D.La) : fAf D (inAf D x) (inAf D y) = (D.EF x y : AfP p) := by
  simp [fAf, inAf, LinearMap.BilinForm.baseChange_tmul, Algebra.smul_def]

end GlobalTheory.HeckeApprox
