import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.BaseP
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.NilpotentHypotheses.TrNondeg
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.NilpotentHypotheses.AevalProdLinearFactors
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CentralExponentBoundOver

noncomputable section

open Matrix GroundTheory.Automorphic.Whittaker GlobalTheory.SplitWeil

namespace PositivityTheory.RgUd.T.Nil.Asm

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem piZ_lin [CharZero k] {n : ℕ} (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (hZ : CR Z) :
    ∃ L : Matrix (Fin n) (Fin n) k →ₗ[k] Matrix (Fin n) (Fin n) k,
      (∀ x, piZ Z x = L x) ∧ (∀ x, L x ∈ Z) ∧ (∀ x, qZ Z (L x) = qZ Z x) ∧ ∀ c ∈ Z, L c = c :=
  piZ_lin' k Z hZ

theorem bez {M : Type*} [AddCommGroup M] [Module ℂ M] (K : Submodule ℂ M) (R R' : M →ₗ[ℂ] M)
    (hRR : R ∘ₗ R' = LinearMap.id) (hR'R : R' ∘ₗ R = LinearMap.id) (hK : ∀ m ∈ K, R m ∈ K) (c : ℝ) (hc : 1 < c)
    (d : ℕ) (a : List ℝ) (ha : ∀ x ∈ a, 2 * x < d) (ζ : M)
    (h1 : ((a.map fun x => R - ((c ^ x : ℝ) : ℂ) • LinearMap.id).prod : Module.End ℂ M) ζ ∈ K)
    (h2 : ((a.map fun x => ((c ^ (d : ℝ) : ℝ) : ℂ) • R' - ((c ^ x : ℝ) : ℂ) • LinearMap.id).prod : Module.End ℂ M) ζ ∈ K) :
    ζ ∈ K :=
  bez' K R R' hRR hR'R hK c hc d a ha ζ h1 h2

end PositivityTheory.RgUd.T.Nil.Asm
