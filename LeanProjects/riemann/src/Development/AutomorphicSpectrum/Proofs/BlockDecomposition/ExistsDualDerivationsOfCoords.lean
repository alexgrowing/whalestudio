import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SEqOne
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ChainRuleAndJacobianCriterion

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.ConeDerivs

theorem exists_dual_derivations : ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))
    (V : X.Opens) (d : ℕ) (c : Coord q V d), letI := (strV q V).toAlgebra;
    ∃ D : Fin d → Derivation K Γ(X, V) Γ(X, V), ∀ k j, D k (c.t j) = if k = j then 1 else 0 := by
  intro K _ X q V d c
  letI := (strV q V).toAlgebra
  letI : Algebra (MvPolynomial (Fin d) K) Γ(X, V) :=
    (MvPolynomial.eval₂Hom (strV q V) c.t : MvPolynomial (Fin d) K →+* Γ(X, V)).toAlgebra
  haveI : IsScalarTower K (MvPolynomial (Fin d) K) Γ(X, V) :=
    IsScalarTower.of_algebraMap_eq fun r => (MvPolynomial.eval₂Hom_C (strV q V) c.t r).symm
  haveI : Algebra.Etale (MvPolynomial (Fin d) K) Γ(X, V) := c.etale
  obtain ⟨⟨b, hb⟩, -⟩ := GlobalTheory.EtaleCoordJacobian.exists_basis_of_etale K Γ(X, V) (Fin d)
  have hb' : ∀ j, KaehlerDifferential.D K Γ(X, V) (c.t j) = b j := fun j => by
    rw [hb j]
    congr 1
    exact (MvPolynomial.eval₂Hom_X' (strV q V) c.t j).symm
  refine ⟨fun k => KaehlerDifferential.linearMapEquivDerivation K Γ(X, V)
    (b.coord k), fun k j => ?_⟩
  change b.coord k (KaehlerDifferential.D K Γ(X, V) (c.t j)) = _
  rw [hb', Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
  simp only [eq_comm]

end GlobalTheory.CompanionTheory.ConeDerivs
