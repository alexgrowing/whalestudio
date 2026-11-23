import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MinpolyIrreducibleNatDegreeOfRankOne
import GroundTheory.Brauer.DoubleCentralizer
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.CentIrr

noncomputable def rootHom (F C : Type) [Field F] [Ring C] [Algebra F C] (y : C) :
    AdjoinRoot (minpoly F y) →ₐ[F] C :=
  Ideal.Quotient.liftₐ (Ideal.span {minpoly F y}) (Polynomial.aeval y) (fun a ha => by
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp ha
    rw [map_mul, minpoly.aeval, zero_mul])

theorem rootHom_root (F C : Type) [Field F] [Ring C] [Algebra F C] (y : C) :
    rootHom F C y (AdjoinRoot.root (minpoly F y)) = y := by
  exact Polynomial.aeval_X y

theorem commute_iff_mem_adjoin (F C : Type) [Field F] [Ring C] [Algebra F C] [FiniteDimensional F C]
    [Algebra.IsCentral F C] [IsSimpleRing C] (n : ℕ) (hn : 0 < n) (hC : Module.finrank F C = n ^ 2)
    (y : C) (hirr : Irreducible (minpoly F y)) (hdeg : (minpoly F y).natDegree = n) (z : C) :
    Commute z y ↔ z ∈ Algebra.adjoin F ({y} : Set C) := by
  set B := Algebra.adjoin F ({y} : Set C) with hBdef
  have hcommB : ∀ {u v : C}, u ∈ B → v ∈ B → u * v = v * u := by
    intro u v hu hv
    have := Algebra.adjoin_le_centralizer_centralizer F ({y} : Set C) hu
    rw [Subalgebra.mem_centralizer_iff] at this
    apply (this v _).symm
    refine Algebra.adjoin_le ?_ hv
    rw [Set.singleton_subset_iff, SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    rw [hg]
  haveI : Fact (Irreducible (minpoly F y)) := ⟨hirr⟩
  set j : AdjoinRoot (minpoly F y) →ₐ[F] C := rootHom F C y
  have hj : Function.Injective j := j.toRingHom.injective
  have hrange : j.range = B := by
    rw [← Algebra.map_top, ← AdjoinRoot.adjoinRoot_eq_top, AlgHom.map_adjoin, Set.image_singleton]
    rw [rootHom_root]
  have hne : minpoly F y ≠ 0 := hirr.ne_zero
  have hEdim : Module.finrank F (AdjoinRoot (minpoly F y)) = n := by
    rw [(AdjoinRoot.powerBasis hne).finrank, AdjoinRoot.powerBasis_dim, hdeg]
  let eB : AdjoinRoot (minpoly F y) ≃ₐ[F] B := (AlgEquiv.ofInjective j hj).trans (Subalgebra.equivOfEq _ _ hrange)
  haveI : IsSimpleRing B := IsSimpleRing.of_ringEquiv eB.toRingEquiv inferInstance
  have hBdim : Module.finrank F B = n := by rw [← eB.toLinearEquiv.finrank_eq, hEdim]
  set Z := Subalgebra.centralizer F (B : Set C)
  have hBZ : B ≤ Z := by
    intro a ha
    rw [Subalgebra.mem_centralizer_iff]
    intro b hb
    exact hcommB hb ha
  have h1 := GroundTheory.Brauer.finrank_mul_finrank_centralizer (K := F) (A := C) B
  have hdim : Module.finrank F B = Module.finrank F Z := by
    apply Nat.eq_of_mul_eq_mul_left (show 0 < Module.finrank F B by rw [hBdim]; exact hn)
    rw [h1, hC, hBdim, sq]
  have hEq : B = Z := Subalgebra.toSubmodule_injective
    (Submodule.eq_of_le_of_finrank_eq (Subalgebra.toSubmodule.monotone hBZ) hdim)
  constructor
  · intro hz
    have hzZ : z ∈ Z := by
      rw [Subalgebra.mem_centralizer_iff]
      intro b hb
      have := Algebra.adjoin_le_centralizer_centralizer F ({y} : Set C) hb
      rw [Subalgebra.mem_centralizer_iff] at this
      refine (this z ?_).symm
      rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
      intro g hg
      rw [Set.mem_singleton_iff] at hg
      rw [hg]; exact hz.eq.symm
    rw [hEq]; exact hzZ
  · intro hz
    exact (hcommB hz (Algebra.self_mem_adjoin_singleton F y) : _)

theorem centralizer_unit_eq_field : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (y₀ : G.Cˣ),
    Irreducible (minpoly G.F (y₀ : G.C)) → (minpoly G.F (y₀ : G.C)).natDegree = G.n →
    ∃ (E : Type) (_ : Field E) (_ : NumberField E) (_ : Algebra G.F E) (j : E →ₐ[G.F] G.C),
      Function.Injective j ∧ ∀ z : G.C, Commute z (y₀ : G.C) ↔ ∃ e, j e = z := by
  intro p _ G y₀ hirr hdeg
  haveI : Fact (Irreducible (minpoly G.F (y₀ : G.C))) := ⟨hirr⟩
  let j : AdjoinRoot (minpoly G.F (y₀ : G.C)) →ₐ[G.F] G.C := rootHom G.F G.C (y₀ : G.C)
  have hne : minpoly G.F (y₀ : G.C) ≠ 0 := hirr.ne_zero
  haveI : FiniteDimensional G.F (AdjoinRoot (minpoly G.F (y₀ : G.C))) :=
    (AdjoinRoot.powerBasis hne).finite
  haveI : FiniteDimensional ℚ (AdjoinRoot (minpoly G.F (y₀ : G.C))) :=
    Module.Finite.trans G.F _
  haveI : CharZero (AdjoinRoot (minpoly G.F (y₀ : G.C))) :=
    charZero_of_injective_algebraMap (algebraMap G.F _).injective
  haveI : NumberField (AdjoinRoot (minpoly G.F (y₀ : G.C))) := ⟨⟩
  have hrange : j.range = Algebra.adjoin G.F ({(y₀ : G.C)} : Set G.C) := by
    rw [← Algebra.map_top, ← AdjoinRoot.adjoinRoot_eq_top, AlgHom.map_adjoin, Set.image_singleton]
    rw [rootHom_root]
  refine ⟨AdjoinRoot (minpoly G.F (y₀ : G.C)), inferInstance, inferInstance, inferInstance, j,
    j.toRingHom.injective, fun z => ?_⟩
  rw [commute_iff_mem_adjoin G.F G.C G.n G.n_pos G.rankC _ hirr hdeg z, ← hrange]
  rfl

end GlobalTheory.CentIrr

example : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (y₀ : G.Cˣ), Irreducible (minpoly G.F (y₀ : G.C)) → (minpoly G.F (y₀ : G.C)).natDegree = G.n → ∃ (E : Type) (_ : Field E) (_ : NumberField E) (_ : Algebra G.F E) (j : E →ₐ[G.F] G.C), Function.Injective j ∧ ∀ z : G.C, Commute z (y₀ : G.C) ↔ ∃ e, j e = z := GlobalTheory.CentIrr.centralizer_unit_eq_field
