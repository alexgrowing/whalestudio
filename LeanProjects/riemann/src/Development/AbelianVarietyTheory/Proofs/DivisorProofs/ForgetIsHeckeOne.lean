import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelPosOfCoprime
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLevelForgettingFiniteEtaleSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyOfFinitePresentationOfIsQProjOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtModelForgetFiniteEtale
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowEqPowOfModEqSim
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleRigidLevelRigid
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntDvdOfEqNatMulIntegralAdeleAwayFromPStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLatticeVectorEqNsmulOfAdelicNsmulStatement

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.LKGeo.ForgetHecke

variable {p : ℕ} [Fact p.Prime] {D : Datum p}

theorem lattice_dvd (n : ℕ) (hn : 0 < n) (hp : n.Coprime p) (z : D.La)
    (h : ∃ w ∈ LaHat D, inAf D z = n • w) : ∃ u : D.La, z = n • u :=
  GlobalTheory.T.exists_latticeVector_eq_nsmul_of_adelic_nsmul p D n hn hp (GlobalTheory.T.int_dvd_of_eq_nat_mul_integralAdeleAwayFromP p n hn hp) z h

def inAfHom (D : Datum p) : D.La →+ AfP p ⊗[ℚ] VQ D where
  toFun := inAf D
  map_zero' := by simp [inAf]
  map_add' x y := by simp [inAf, TensorProduct.tmul_add]

theorem acts_one_iff {G : HTGroup p} (L : Link D G) (n : ℕ) (hn : 0 < n) (hp : n.Coprime p) (x y : D.La) :
    (∃ w ∈ LaHat D, ((1 : ℕ) : ℤ) • L.actG 1 (inAf D x) = inAf D y + n • w) ↔ ∃ u : D.La, x - y = n • u := by
  simp only [map_one, Nat.cast_one, one_smul, Module.End.one_apply]
  constructor
  · rintro ⟨w, hw, e⟩
    refine lattice_dvd n hn hp _ ⟨w, hw, ?_⟩
    change inAfHom D (x - y) = _
    rw [map_sub]
    change inAf D x - inAf D y = _
    rw [e]; abel
  · rintro ⟨u, hu⟩
    refine ⟨inAf D u, AddSubgroup.subset_closure ⟨1, u, fun v => ?_, ?_⟩, ?_⟩
    · rw [map_one]; exact (v.1.adicCompletionIntegers ℚ).one_mem
    · rfl
    · have h1 : x = y + n • u := by rw [← hu]; abel
      rw [h1]
      change inAfHom D (y + n • u) = inAfHom D y + n • inAfHom D u
      rw [map_add, map_nsmul]

end GlobalTheory.LKGeo.ForgetHecke

namespace GlobalTheory.LKGeo.ForgetHecke

variable {p : ℕ} [Fact p.Prime] {D : Datum p}

end GlobalTheory.LKGeo.ForgetHecke
