import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FinrankEqZeroIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ArcWitMemRangeJKOfMemRangeJ

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace IsLocalRing
open MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam
open Formalism.MainNotions.DIV.Cons (SCF intO)
open GlobalTheory.LocM GlobalTheory.LocM.Cht
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LocM.Cht

theorem trivOfAbSt : TrivOfAbSt := by
  intro E _ _ _ H Dw l Xo c O _ β Y p C P A _ hab
  have hloc : IsLocalHom A.f := ⟨fun a ha => by
    by_contra h
    exact (mem_maximalIdeal _).1 ((mem_maximalIdeal_ball (A.f a)).2 (A.f_loc a ((mem_maximalIdeal _).2 h))) ha⟩
  have e1 : spMap A.f (closedPoint _) = closedPoint A.R := comap_closedPoint A.f
  have e2 : P.yt (closedPoint ↥(intO ↥C.S)) = A.ι (closedPoint A.R) := by
    have h := congrArg (fun g : Sp ↥(intO ↥C.S) ⟶ Y.X => g (closedPoint ↥(intO ↥C.S))) A.fac
    exact h.symm.trans ((Scheme.Hom.comp_apply _ _ _).trans (congrArg A.ι e1))
  have h₁ : closedPoint A.R ∈ abLocus A.t.G :=
    (abLocus_pullback abLocusOne Y.t.semi A.m.cart.1 _).1 (e2 ▸ hab)
  have hmax : (maximalIdeal A.R ^ (0 + 1)).IsMaximal := by
    rw [zero_add, pow_one]; infer_instance
  have hF : IsField (A.R ⧸ maximalIdeal A.R ^ (0 + 1)) :=
    (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1 hmax
  have hle : maximalIdeal A.R ^ (0 + 1) ≤ (closedPoint A.R).asIdeal := by
    rw [zero_add, pow_one]; exact le_rfl
  obtain ⟨q, hq⟩ : closedPoint A.R ∈ Set.range (PrimeSpectrum.comap
      (Ideal.Quotient.mk (maximalIdeal A.R ^ (0 + 1)))) := by
    rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]
    exact hle
  let g := A.U.U.gt 0
  have m : Mono g.i := ⟨fun a b h => g.isKernel.hom_ext h (toUnit_unique _ _)⟩
  have hq' : thick A.R (maximalIdeal A.R) 0 q ∈ abLocus A.t.G := by
    rw [← hq] at h₁; exact h₁
  exact ArcNotAbelian.subsingleton_of_mem_abLocus A.t.G A.t.semi _ hF _ q hq' A.U.D.toPre.X g.i g.i_hom

end GlobalTheory.LocM.Cht
