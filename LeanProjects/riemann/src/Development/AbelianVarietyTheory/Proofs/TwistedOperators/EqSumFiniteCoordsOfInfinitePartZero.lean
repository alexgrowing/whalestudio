import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DerAlong
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientHeightLowerBoundShortIsotropicVector
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.InfZeroFinSum

open Module

theorem repr_map_id {F A A' E ι : Type*} [Field F] [CommRing A] [Algebra F A] [CommRing A'] [Algebra F A']
    [CommRing E] [Algebra F E] [Fintype ι] [DecidableEq ι] (b : Basis ι F E) (f : A →ₐ[F] A')
    (z : A ⊗[F] E) (k : ι) :
    (Algebra.TensorProduct.basis A' b).repr (Algebra.TensorProduct.map f (AlgHom.id F E) z) k
      = f ((Algebra.TensorProduct.basis A b).repr z k) := by
  have hz : z = ∑ i, (Algebra.TensorProduct.basis A b).repr z i • (Algebra.TensorProduct.basis A b) i :=
    ((Algebra.TensorProduct.basis A b).sum_repr z).symm
  have hm : Algebra.TensorProduct.map f (AlgHom.id F E) z
      = ∑ i, f ((Algebra.TensorProduct.basis A b).repr z i) • (Algebra.TensorProduct.basis A' b) i := by
    conv_lhs => rw [hz]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one,
      Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  rw [hm, (Algebra.TensorProduct.basis A' b).repr_sum_self]

theorem eq_sum_of_fst_zero {F Ai Afn E ι : Type*} [Field F] [CommRing Ai] [Algebra F Ai] [CommRing Afn]
    [Algebra F Afn] [CommRing E] [Algebra F E] [Fintype ι] [DecidableEq ι] (b : Basis ι F E)
    (z : (Ai × Afn) ⊗[F] E)
    (hz : Algebra.TensorProduct.map (AlgHom.fst F Ai Afn) (AlgHom.id F E) z = 0) :
    z = ∑ k, ((0 : Ai), (Algebra.TensorProduct.basis Afn b).repr
      (Algebra.TensorProduct.map (AlgHom.snd F Ai Afn) (AlgHom.id F E) z) k) ⊗ₜ[F] b k := by
  have h1 : ∀ k, ((Algebra.TensorProduct.basis (Ai × Afn) b).repr z k).1 = 0 := by
    intro k
    have := repr_map_id b (AlgHom.fst F Ai Afn) z k
    rw [hz, map_zero] at this
    simpa using this.symm
  conv_lhs => rw [← (Algebra.TensorProduct.basis (Ai × Afn) b).sum_repr z]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [repr_map_id b (AlgHom.snd F Ai Afn) z k]
  have hc : (Algebra.TensorProduct.basis (Ai × Afn) b).repr z k
      = ((0 : Ai), AlgHom.snd F Ai Afn ((Algebra.TensorProduct.basis (Ai × Afn) b).repr z k)) :=
    Prod.ext (h1 k) rfl
  rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  exact congrArg (fun x => x ⊗ₜ[F] b k) hc

end GlobalTheory.InfZeroFinSum

theorem GlobalTheory.InfZeroFinSum.eq_sum_finCoord_of_infPart_eq_zero : ∀ (D : D7) (z : AE D), infPart D z = 0 → z = ∑ k, pairA D.host.F 0 (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finCoord D (GlobalTheory.HolDict.ShortVec.finPr D z) k) ⊗ₜ[D.host.F] Module.finBasis D.host.F D.host.E k := by
  intro D z hz
  exact GlobalTheory.InfZeroFinSum.eq_sum_of_fst_zero (Module.finBasis D.host.F D.host.E) z hz
