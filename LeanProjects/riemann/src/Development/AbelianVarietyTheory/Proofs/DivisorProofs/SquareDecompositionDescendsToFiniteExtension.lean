import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareDecompositionDescendsToFinitelyGeneratedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareDecompositionBaseChangeAlgebraMapStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.SqDecFinite

theorem exists_algHom_finite (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω) (hR : R.FG) :
    ∃ (k₁ : Type) (_ : Field k₁) (_ : Algebra k k₁) (_ : FiniteDimensional k k₁), Nonempty (R →ₐ[k] k₁) := by
  have : Algebra.FiniteType k R := (Subalgebra.fg_iff_finiteType _).1 hR
  obtain ⟨m, hm⟩ := Ideal.exists_maximal R
  letI : Field (R ⧸ m) := Ideal.Quotient.field m
  have : Algebra.FiniteType k (R ⧸ m) := Algebra.FiniteType.trans (S := R) inferInstance inferInstance
  have : Module.Finite k (R ⧸ m) := finite_of_finite_type_of_isJacobsonRing k (R ⧸ m)
  exact ⟨R ⧸ m, inferInstance, inferInstance, inferInstance, ⟨Ideal.Quotient.mkₐ k m⟩⟩

theorem main : ∀ (k Ω : Type) [Field k] [Field Ω] (σ : k →+* Ω) (A₀ : Over (Sp k)) [GrpObj A₀], IsAbelianScheme A₀ → ∀ (L M : LB A₀.left), L.IsLB → M.IsLB → SqDec ((Over.pullback (spMap σ)).obj A₀) (L.pull (pullback.fst A₀.hom (spMap σ))) (M.pull (pullback.fst A₀.hom (spMap σ))) → ∃ (k₁ : Type) (_ : Field k₁) (_ : Algebra k k₁) (_ : FiniteDimensional k k₁), SqDec ((Over.pullback (spMap (algebraMap k k₁))).obj A₀) (L.pull (pullback.fst A₀.hom (spMap (algebraMap k k₁)))) (M.pull (pullback.fst A₀.hom (spMap (algebraMap k k₁)))) := by
  intro k Ω _ _ σ A₀ _ hA L M hL hM h
  letI := σ.toAlgebra
  obtain ⟨R, hR, hRd⟩ := GlobalTheory.T.squareDecomposition_descends_to_finitelyGenerated k Ω A₀ hA L M hL hM h
  obtain ⟨k₁, _, _, _, ⟨ρ⟩⟩ := exists_algHom_finite k Ω R hR
  exact ⟨k₁, inferInstance, inferInstance, inferInstance, GlobalTheory.T.squareDecomposition_baseChange_algebraMap k R k₁ ρ A₀ L M hL hM hRd⟩

end GlobalTheory.SqDecFinite
