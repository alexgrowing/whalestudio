import Mathlib
import Formalism.LocalToGlobal.GlobalTheory.HLatOpsP
import Formalism.HarderNarasimhan.FinalCor
import Formalism.QuotientMetricDivisors.ReductionLemmaZero
import Formalism.QuotientMetricDivisors.FinalW
import Formalism.LocalToGlobal.Divisibility.FramesLemmas
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HermitianSelfDualMaxSlopeStatement
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DivisionValues
open scoped Matrix ComplexOrder

namespace GlobalTheory.SelfDualSlope

open Formalism.L2.GlobalTheoryTheory.HLatOps

theorem muMaxDual_nonpos_of_rat_coord : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (K0 : Subfield K), IsCMSub K0 → ∀ v0 : InfinitePlace K, IsConjAt v0 → ∀ (A : HLat K) (n : ℕ) (H : Matrix (Fin n) (Fin n) K) (e : (Fin n → K) ≃ₗ[K] A.V) (M : Submodule (𝓞 K) (Fin n → K)), A.Good → 0 < A.rank → (∀ i j, H i j ∈ K0) → (∀ (v : InfinitePlace K) (i j : Fin n), Formalism.HermitianLatticesTheory.majAt A.b A.X v (e (Pi.single i 1)) (e (Pi.single j 1)) = v.embedding (H i j)) → A.L = M.map (e.toLinearMap.restrictScalars (𝓞 K)) → Formalism.HermitianLatticesTheory.dual (hform H) M ≤ M → A.muMaxDual ≤ 0 := by
  intro K _ _ _ _ K0 hK0 v0 hv0 A n H e M hG hr hH0 hgram hL hdual
  have hs : IsSesq (fun v (x y : Fin n → K) => Formalism.HermitianLatticesTheory.majAt A.b A.X v (e.toLinearMap x) (e.toLinearMap y)) :=
    isSesq_comp (isSesq_maj A.b A.X) e.toLinearMap
  have hg : ∀ v : InfinitePlace K, gramOf (Pi.basisFun K (Fin n))
      (fun (x y : Fin n → K) => Formalism.HermitianLatticesTheory.majAt A.b A.X v (e.toLinearMap x) (e.toLinearMap y)) =
      H.map v.embedding := by
    intro v
    ext i j
    simp only [gramOf, Matrix.of_apply, Pi.basisFun_apply, Matrix.map_apply]
    exact hgram v i j
  have hpos : ∀ v : InfinitePlace K, (H.map v.embedding).PosDef := by
    intro v
    rw [← hg v]
    exact posAt_comp A.b (Pi.basisFun K (Fin n)) (isSesq_maj A.b A.X) (posAt_maj A.b A.X hG.1)
      e.toLinearMap e.injective v
  have hX := Formalism.L2.DIV.stdFrameRatHerm K K0 n H hH0 hpos
  let B : HLat K := Formalism.L2.DIV.toHLat (Formalism.L2.DIV.stdFrame H) M
  let I : Iso B A :=
    { e := e
      map_L := hL.symm
      norm := by
        intro v x
        rw [normAt_eq_sqrt, normAt_eq_sqrt]
        congr 2
        have h1 := sesq_eq_sum hs (Pi.basisFun K (Fin n)) v x x
        have h2 := sesq_eq_sum (isSesq_maj (Pi.basisFun K (Fin n)) (Formalism.L2.DIV.stdFrame H))
          (Pi.basisFun K (Fin n)) v x x
        rw [gramOf_maj] at h2
        have h3 : ((Formalism.L2.DIV.stdFrame H v)⁻¹).conjTranspose * (Formalism.L2.DIV.stdFrame H v)⁻¹ =
          H.map v.embedding := (Formalism.L2.DIV.frameOfSpec n _ (hpos v)).2
        rw [h3] at h2
        rw [hg v] at h1
        exact h1.trans h2.symm }
  have hB : B.Good := I.symm.good hG
  have hlat : Submodule.IsLattice K M := ⟨hB.2.1, hB.2.2⟩
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · exfalso
      subst h
      have h1 : B.rank = A.rank := I.rank_eq
      have h2 : B.rank ≤ Module.finrank K (Fin 0 → K) :=
        Submodule.finrank_le (R := K) (M := Fin 0 → K) _
      simp at h2
      omega
    · exact h
  have hmain := GlobalTheory.T.hermitian_self_dual_max_slope K K0 hK0 v0 hv0 n H _ hX M hlat hdual hn
  rw [← (iso_inv_dual K B A I hB).2.1]
  exact hmain

end GlobalTheory.SelfDualSlope
